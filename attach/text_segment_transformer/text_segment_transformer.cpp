#include "spdlog/spdlog.h"
#include <algorithm>
#include <cerrno>
#include <cstddef>
#include <cstdio>
#include <cinttypes>
#include <cstdlib>
#include <cstring>
#include <dlfcn.h>
#include <fcntl.h>
#include <fstream>
#include <sys/mman.h>
#include <vector>
#include <cstdint>
#include <unistd.h>
#include <string>
#include <atomic>
#include <cinttypes>
#include "text_segment_transformer.hpp"
#include <frida-gum.h>
/*
Function arguments are passed using the following order:
- RDI
- RSI
- RDX
- RCX
- R8
- R9
- ...stack

- RAX: return value

While syscall args are passed using
- RAX:  syscall_nr
- RDI:  arg1
- RSI:  arg2
- RDX:  arg3
- R10:  arg4
- R8:   arg5
- R9:   arg6

- RAX: return value

*/

extern "C" void syscall_hooker_asm();
extern "C" int64_t call_orig_syscall(int64_t sys_nr, int64_t arg1, int64_t arg2,
				     int64_t arg3, int64_t arg4, int64_t arg5,
				     int64_t arg6);
extern "C" void syscall_addr();
// clone_svc_addr is the svc instruction used for clone/clone3 syscalls.
// It must be excluded from rewriting (like syscall_addr) so clone works.
extern "C" void clone_svc_addr();

static const int NR_syscalls = 512;
static syscall_hooker_func_t call_hook = &call_orig_syscall;

#if defined(__x86_64__)
[[maybe_unused]] void __asm_holder()
{
	__asm__(".globl syscall_hooker_asm\n\t"
		"syscall_hooker_asm:\n\t"
		"pop %rax\n\t" // Restore the saved rax, which is the syscall
			       // number
		"cmp $15, %rax\n\t" // Special handing for rt_sigreturn, they
				    // don't need to be traced
		"je handle_sigreturn\n\t"
		"movq (%rsp), %rcx\n\t"
		"pushq %rbp\n\t"
		"movq %rsp, %rbp\n\t"
		"andq $-16, %rsp \n\t" // 16 byte stack alignment
		"pushq %rax\n\t" // Save syscall args on stack
		"pushq %rdi\n\t"
		"pushq %rsi\n\t"
		"pushq %rdx\n\t"
		"pushq %r10\n\t"
		"pushq %r8\n\t"
		"pushq %r9\n\t"
		// Put syscall args in appreciate argument order
		"movq 48(%rsp), %rdi\n\t" // syscall_nr
		"movq 40(%rsp), %rsi\n\t" // arg1
		"movq 32(%rsp), %rdx\n\t" // arg2
		"movq 24(%rsp), %rcx\n\t" // arg3
		"movq 16(%rsp), %r8\n\t" // arg4
		"movq 8(%rsp), %r9\n\t" // arg5
		"pushq (%rsp)\n\t" // arg6
		"call syscall_hooker_cxx\n\t"
		"leave\n\t"
		"ret\n\t");

	__asm__(".globl call_orig_syscall\n\t"
		"call_orig_syscall:\n\t"
		"movq %rdi, %rax \n\t"
		"movq %rsi, %rdi \n\t"
		"movq %rdx, %rsi \n\t"
		"movq %rcx, %rdx \n\t"
		"movq %r8, %r10 \n\t"
		"movq %r9, %r8 \n\t"
		"movq 8(%rsp),%r9 \n\t"
		"handle_sigreturn:\n\t"
		// "addq $8, %rsp\n\t"
		"syscall_addr:\n\t"
		"syscall\n\t"
		"ret\n\t");
}
#elif defined(__aarch64__)
/*
ARM64 syscall ABI:
- x8: syscall number
- x0-x5: arguments
- x0: return value

ARM64 C calling convention:
- x0-x7: arguments
- x0: return value
- x30 (LR): return address
- x29 (FP): frame pointer

IMPORTANT: When we replace svc #0 with bl <trampoline>, the bl instruction
clobbers x30 (link register). Leaf functions that don't save x30 will break.

Solution: We rewrite TWO instructions: the instruction before svc and the svc
itself. We replace them with:
  stp x29, x30, [sp, #-16]!   ; save frame pointer and link register
  bl <stub>                    ; call per-site stub

Each stub:
  1. Executes the displaced original instruction (SP-adjusted if needed)
  2. Branches to the handler
  3. Handler restores x29/x30 from stack and returns

This catches ANY safe instruction before svc, not just mov x8, #N.
*/

static volatile bool g_syscall_rewriting_complete = false;

// Trampoline page management: multiple pages to cover different address ranges.
// Go binaries load at low addresses (~0x400000) while libc is at high addresses.
// ARM64 bl/b has ±128MB range, so a single trampoline can't reach both.
// Each page is 64KB and contains per-site stubs. If the handler is out of
// direct 'b' range, the page starts with a veneer (indirect long jump).
struct TrampolinePage {
	uint64_t base;          // page base address
	uint32_t *next_stub;    // next free stub slot
	uint64_t end;           // end of page
	uint64_t veneer_addr;   // address of handler veneer (0 if handler in b range)
};
static std::vector<TrampolinePage> g_trampoline_pages;

// Raw mprotect - bypasses libc to avoid recursion since libc's mprotect
// may itself contain a rewritten svc instruction.
static inline long raw_mprotect(void *addr, size_t len, int prot)
{
	register long x0 __asm__("x0") = (long)addr;
	register long x1 __asm__("x1") = (long)len;
	register long x2 __asm__("x2") = (long)prot;
	register long x8 __asm__("x8") = 226;
	__asm__ volatile("svc #0"
			 : "+r"(x0)
			 : "r"(x1), "r"(x2), "r"(x8)
			 : "memory");
	return x0;
}

[[maybe_unused]] void __asm_holder()
{
	// syscall_hooker_asm: Central ARM64 syscall handler
	// Called from per-site stubs via: b syscall_hooker_asm
	//
	// On entry:
	//   x8 = syscall number (set by displaced instruction in stub)
	//   x0-x5 = syscall arguments
	//   Stack: [sp] = saved x29, [sp+8] = saved x30 (from call-site stp)
	//   x30 = return address (instruction after the bl at call site)
	//
	// The handler:
	//   1. Checks for rt_sigreturn (passthrough)
	//   2. Handles clone/clone3 at asm level (returns in both parent & child)
	//   3. Saves all registers that kernel svc #0 would preserve
	//   4. Calls syscall_hooker_cxx(sys_nr, arg1..arg6)
	//   5. Restores all preserved registers
	//   6. Restores original x29/x30 from call-site stack frame
	//   7. Returns via br x16 (NOT ret, since x30 is the original value)
	__asm__(
		".globl syscall_hooker_asm\n\t"
		"syscall_hooker_asm:\n\t"
		"bti c\n\t"
		"cmp x8, #139\n\t" // check for rt_sigreturn
		"b.eq handle_sigreturn\n\t"
		// clone/clone3 return in BOTH parent and child. The child gets
		// a new stack, so our handler can't unwind its frame on it.
		// Handle clone at the asm level, before saving any registers.
		"cmp x8, #220\n\t" // clone
		"b.eq handle_clone\n\t"
		"cmp x8, #435\n\t" // clone3
		"b.eq handle_clone\n\t"
		// Stack on entry (from the two-instruction rewrite):
		//   [sp] = original x29, [sp+8] = original x30
		// x30 = return address (instruction after the bl at call site)
		//
		// We must:
		// 1. Save x30 (return address) - bl syscall_hooker_cxx will clobber it
		// 2. Save caller-saved regs x9-x18 - C call may clobber them
		//    but kernel svc #0 preserves them, so callers expect them intact
		// 3. Save syscall arg registers x0-x8 - C call clobbers x0-x7
		//    but kernel svc #0 preserves x1-x8 (only x0 = return value)
		// 4. Save NZCV condition flags - kernel preserves, C call may clobber
		// 5. Call C handler
		// 6. Restore everything in reverse order
		// 7. Return to saved return address via br (not ret)
		// Save return address (x30 from bl instruction)
		"stp x30, xzr, [sp, #-16]!\n\t"
		// Save caller-saved registers (x9-x18) that kernel svc would preserve
		"stp x9, x10, [sp, #-16]!\n\t"
		"stp x11, x12, [sp, #-16]!\n\t"
		"stp x13, x14, [sp, #-16]!\n\t"
		"stp x15, x16, [sp, #-16]!\n\t"
		"stp x17, x18, [sp, #-16]!\n\t"
		// Save syscall argument registers and syscall number
		"stp x0, x1, [sp, #-16]!\n\t"
		"stp x2, x3, [sp, #-16]!\n\t"
		"stp x4, x5, [sp, #-16]!\n\t"
		"stp x6, x7, [sp, #-16]!\n\t"
		"str x8, [sp, #-16]!\n\t"
		// Set up C function args: syscall_hooker_cxx(sys_nr, a1, a2, a3, a4, a5, a6)
		"mov x6, x5\n\t"
		"mov x5, x4\n\t"
		"mov x4, x3\n\t"
		"mov x3, x2\n\t"
		"mov x2, x1\n\t"
		"mov x1, x0\n\t"
		"mov x0, x8\n\t"
		// Save FPSIMD registers - kernel svc preserves all 128 bits of q0-q31,
		// but our C call may clobber q0-q7, upper bits of q8-q15, and q16-q31.
		// Save all 32 for complete transparency. Cost: 512 bytes stack, ~32 cycles.
		"stp q0, q1, [sp, #-32]!\n\t"
		"stp q2, q3, [sp, #-32]!\n\t"
		"stp q4, q5, [sp, #-32]!\n\t"
		"stp q6, q7, [sp, #-32]!\n\t"
		"stp q8, q9, [sp, #-32]!\n\t"
		"stp q10, q11, [sp, #-32]!\n\t"
		"stp q12, q13, [sp, #-32]!\n\t"
		"stp q14, q15, [sp, #-32]!\n\t"
		"stp q16, q17, [sp, #-32]!\n\t"
		"stp q18, q19, [sp, #-32]!\n\t"
		"stp q20, q21, [sp, #-32]!\n\t"
		"stp q22, q23, [sp, #-32]!\n\t"
		"stp q24, q25, [sp, #-32]!\n\t"
		"stp q26, q27, [sp, #-32]!\n\t"
		"stp q28, q29, [sp, #-32]!\n\t"
		"stp q30, q31, [sp, #-32]!\n\t"
		// Save NZCV condition flags - kernel svc preserves them, C call may clobber
		"mrs x8, nzcv\n\t"
		"str x8, [sp, #-16]!\n\t"
		"bl syscall_hooker_cxx\n\t"
		// x0 = return value from syscall handler
		// Restore NZCV condition flags
		"ldr x8, [sp], #16\n\t"
		"msr nzcv, x8\n\t"
		// Restore FPSIMD registers (reverse order)
		"ldp q30, q31, [sp], #32\n\t"
		"ldp q28, q29, [sp], #32\n\t"
		"ldp q26, q27, [sp], #32\n\t"
		"ldp q24, q25, [sp], #32\n\t"
		"ldp q22, q23, [sp], #32\n\t"
		"ldp q20, q21, [sp], #32\n\t"
		"ldp q18, q19, [sp], #32\n\t"
		"ldp q16, q17, [sp], #32\n\t"
		"ldp q14, q15, [sp], #32\n\t"
		"ldp q12, q13, [sp], #32\n\t"
		"ldp q10, q11, [sp], #32\n\t"
		"ldp q8, q9, [sp], #32\n\t"
		"ldp q6, q7, [sp], #32\n\t"
		"ldp q4, q5, [sp], #32\n\t"
		"ldp q2, q3, [sp], #32\n\t"
		"ldp q0, q1, [sp], #32\n\t"
		// Restore x1-x8 (kernel svc preserves them, so must we).
		// x0 is the return value from C handler; keep it, skip saved x0.
		"ldr x8, [sp], #16\n\t" // restore x8 (syscall number)
		"ldp x6, x7, [sp], #16\n\t" // restore x6, x7
		"ldp x4, x5, [sp], #16\n\t" // restore x4, x5
		"ldp x2, x3, [sp], #16\n\t" // restore x2, x3
		"ldr x1, [sp, #8]\n\t" // restore x1 (skip saved x0 at [sp])
		"add sp, sp, #16\n\t" // pop x0,x1 slot
		// Restore caller-saved registers (x9-x18)
		"ldp x17, x18, [sp], #16\n\t"
		"ldp x15, x16, [sp], #16\n\t"
		"ldp x13, x14, [sp], #16\n\t"
		"ldp x11, x12, [sp], #16\n\t"
		"ldp x9, x10, [sp], #16\n\t"
		// Pop saved return address into x16 (IP0, safe scratch register)
		"ldr x16, [sp], #16\n\t"
		// Restore original x29, x30 from the call-site stp x29, x30, [sp, #-16]!
		"ldp x29, x30, [sp], #16\n\t"
		// Return to the instruction after the bl (NOT ret, which uses x30)
		"br x16\n\t"
		// clone/clone3 handler
		// clone returns in BOTH parent and child. The child has a new stack
		// (set by clone args), so we can't access the parent's saved x29/x30.
		// Handle at asm level before any stack frame setup.
		//
		// On entry:
		//   SP has saved x29/x30 from call-site stp
		//   x30 = return address from bl (instruction after bl)
		//   x0-x5, x8 = syscall args
		"handle_clone:\n\t"
		"mov x16, x30\n\t" // save bl return addr in IP0
		".globl clone_svc_addr\n\t"
		"clone_svc_addr:\n\t"
		"svc #0\n\t" // do the real clone/clone3
		"cbz x0, clone_child\n\t" // child returns 0
		// Parent: restore x29, x30 from call-site stp and return
		"ldp x29, x30, [sp], #16\n\t"
		"br x16\n\t"
		"clone_child:\n\t"
		// Child: has a new stack (can't access parent's saved regs).
		// x29 is still the original value (stp saved but didn't modify regs).
		// Just return to the instruction after bl.
		"br x16\n\t");

	// call_orig_syscall: used by the C handler to perform the actual syscall.
	// The svc instruction here (at syscall_addr) is excluded from rewriting.
	__asm__(
		".globl call_orig_syscall\n\t"
		"call_orig_syscall:\n\t"
		"mov x8, x0\n\t"
		"mov x0, x1\n\t"
		"mov x1, x2\n\t"
		"mov x2, x3\n\t"
		"mov x3, x4\n\t"
		"mov x4, x5\n\t"
		"mov x5, x6\n\t"
		"handle_sigreturn:\n\t"
		".globl syscall_addr\n\t"
		"syscall_addr:\n\t"
		"svc #0\n\t"
		"ret\n\t");
}
#else
#error "Unsupported architecture"
#endif

#if defined(__aarch64__)
// Per-thread reentrancy guard using gettid + global bitmap.
// We CANNOT use __thread / TLS because Go's runtime overwrites TPIDR_EL0
// on threads it creates via clone(CLONE_SETTLS). Accessing C __thread
// variables from those threads would read/write into Go's TLS area,
// corrupting Go runtime state and crashing the process.
//
// Instead, we use gettid (via call_orig_syscall, which uses the excluded
// svc at syscall_addr) to identify threads, and index into a global bitmap.
//
// Uses std::atomic with relaxed ordering for C++ standards compliance.
// On ARM64 this compiles to plain ldrb/strb - same as volatile but correct
// under the C++ memory model for concurrent access.
static std::atomic<uint8_t> g_dispatch_flags[65536]; // indexed by tid & 0xFFFF
#endif

extern "C" int64_t syscall_hooker_cxx(int64_t sys_nr, int64_t arg1,
				      int64_t arg2, int64_t arg3, int64_t arg4,
				      int64_t arg5, int64_t arg6)
{
#if defined(__aarch64__)
	// Per-thread reentrancy guard using gettid + global bitmap.
	// gettid goes through call_orig_syscall which uses the excluded svc
	// address, so it won't recurse back into this handler.
	uint32_t tid = (uint32_t)call_orig_syscall(178 /*__NR_gettid*/, 0, 0,
						   0, 0, 0, 0);
	uint32_t idx = tid & 0xFFFF;
	if (g_dispatch_flags[idx].load(std::memory_order_relaxed)) {
		// Already in the handler on this thread - passthrough to
		// avoid recursion
		return call_orig_syscall(sys_nr, arg1, arg2, arg3, arg4, arg5,
					 arg6);
	}
	g_dispatch_flags[idx].store(1, std::memory_order_relaxed);
	int64_t ret = call_hook(sys_nr, arg1, arg2, arg3, arg4, arg5, arg6);
	g_dispatch_flags[idx].store(0, std::memory_order_relaxed);
	return ret;
#else
	return call_hook(sys_nr, arg1, arg2, arg3, arg4, arg5, arg6);
#endif
}

#if defined(__aarch64__)
// SvcLocation - describes one rewritable svc site
struct SvcLocation {
	uint64_t address;        // address of the svc #0 instruction
	uint64_t prev_address;   // address of the instruction before svc
	uint32_t displaced_insn; // instruction to emit in stub (possibly SP-adjusted)
	int orig_perm;           // original page permissions (to restore after rewrite)
};

static std::vector<SvcLocation> g_svc_locations;

// is_unsafe_to_displace - reject instructions that can't be moved.
// PC-relative instructions would compute wrong addresses in the stub.
// Control-flow instructions would jump to wrong targets.
// Trap instructions would cause issues if displaced.
static bool is_unsafe_to_displace(uint32_t insn)
{
	// ADR: [0 ii 10000 ...] - PC-relative address computation
	if ((insn & 0x1f000000) == 0x10000000)
		return true;
	// ADRP: [1 ii 10000 ...] - PC-relative page address
	if ((insn & 0x9f000000) == 0x90000000)
		return true;
	// LDR literal (all variants): [xx 011 x 00 ...] - PC-relative load
	if ((insn & 0x3b000000) == 0x18000000)
		return true;
	// B: [000101 ...]
	if ((insn & 0xfc000000) == 0x14000000)
		return true;
	// BL: [100101 ...]
	if ((insn & 0xfc000000) == 0x94000000)
		return true;
	// B.cond: [01010100 ... 0 ...]
	if ((insn & 0xff000010) == 0x54000000)
		return true;
	// CBZ/CBNZ: [x 011010 x ...]
	if ((insn & 0x7e000000) == 0x34000000)
		return true;
	// TBZ/TBNZ: [x 011011 x ...]
	if ((insn & 0x7e000000) == 0x36000000)
		return true;
	// RET/BR/BLR: [1101011 00 x 1 11111 0000 x 0 Rn 00000]
	if ((insn & 0xfe1ffc1f) == 0xd61f0000)
		return true;
	// SVC/HVC/SMC: [11010100 000 ...] - trap instructions
	if ((insn & 0xffe00000) == 0xd4000000)
		return true;
	return false;
}

// is_sp_relative_load_store - broad catch-all for SP-based memory ops.
// Checks if an instruction uses SP (x31) as a base register for ANY
// load/store addressing mode. Used as a safety net: any SP-relative
// load/store that we don't explicitly know how to adjust gets rejected.
static bool is_sp_relative_load_store(uint32_t insn)
{
	uint32_t rn = (insn >> 5) & 0x1f;
	if (rn != 31)
		return false; // not SP-based, not our concern

	uint32_t op0 = (insn >> 28) & 0xf; // bits [31:28]
	uint32_t op1 = (insn >> 26) & 0x1; // bit [26] (V flag)
	uint32_t op24 = (insn >> 24) & 0x3; // bits [25:24]
	(void)op0;
	(void)op1;

	// Load/store encoding classes all have bits [27:25] in {101, 110, 111}
	uint32_t bits_27_25 = (insn >> 25) & 0x7;
	if (bits_27_25 == 0x7 || bits_27_25 == 0x6 || bits_27_25 == 0x5) {
		// 111 = LDR/STR unsigned offset, LDUR/STUR, pre/post-index, etc.
		// 110 = LDP/STP, LDNP/STNP (load/store pair)
		// 101 = LDR/STR register offset, atomic ops, etc.
		return true;
	}
	// Load/store exclusive: bits [27:24] = 0010
	if (bits_27_25 == 0x4 && op24 == 0x0) {
		return true;
	}
	return false;
}

// adjust_sp_offset_if_needed - fix SP-relative offsets for displaced insns.
// When the displaced instruction runs in the stub, SP is 16 bytes lower
// than it was at the original location (because of the stp x29, x30, [sp, #-16]!
// that executes before bl <stub>). For unsigned-offset SP-relative loads/stores,
// we add 16 bytes (scaled) to the immediate offset to compensate.
//
// Returns:
//   - Adjusted instruction if SP-relative unsigned offset (safe to adjust)
//   - Original instruction unchanged if not SP-relative
//   - 0 if SP-relative but in a form we can't adjust (rejected for safety)
static uint32_t adjust_sp_offset_if_needed(uint32_t insn)
{
	// Check for unsigned offset load/store: [xx 111 0 01 xx imm12 Rn Rt]
	// This covers LDR, STR, LDRB, STRB, LDRH, STRH, LDRSW, etc.
	bool is_unsigned_offset = (insn & 0x3b200000) == 0x39000000;
	if (is_unsigned_offset) {
		uint32_t rn = (insn >> 5) & 0x1f;
		if (rn != 31)
			return insn; // not SP-relative, safe as-is

		// Determine the scale factor from size and V (SIMD) fields
		uint32_t size = (insn >> 30) & 0x3;
		uint32_t V = (insn >> 26) & 0x1;
		uint32_t scale;
		if (V == 0) {
			scale = size; // 0=1byte, 1=2byte, 2=4byte, 3=8byte
		} else {
			// SIMD/FP - opc field determines size for 128-bit
			uint32_t opc = (insn >> 22) & 0x3;
			if (opc == 0)
				scale = size; // 8/16/32/64-bit SIMD
			else
				scale = 4; // 128-bit (Q register)
		}

		uint32_t imm12 = (insn >> 10) & 0xfff;
		// The offset in bytes is imm12 << scale. We need to add 16 bytes.
		// In the scaled encoding, that means adding 16 >> scale to imm12.
		uint32_t adjustment = 16 >> scale;
		if (imm12 + adjustment > 0xfff)
			return 0; // overflow, reject

		insn = (insn & ~(0xfff << 10)) | ((imm12 + adjustment) << 10);
		return insn;
	}

	// For any OTHER SP-relative load/store form (ldur/stur with signed imm9,
	// ldp/stp with signed imm7, pre/post-index modes, etc.), we don't know
	// how to safely adjust the offset. Reject to avoid silent wrong-offset bugs.
	if (is_sp_relative_load_store(insn))
		return 0;

	// Not a load/store with SP base - safe to displace as-is
	return insn;
}

// collect_svc_in_segment - scan a code segment for rewritable svc sites.
// Uses Capstone to disassemble the segment. For each svc #0 found:
//   1. Skip our own svc instructions (syscall_addr, clone_svc_addr)
//   2. Check if the previous instruction is safe to displace
//   3. Adjust SP offsets if the previous instruction is SP-relative
//   4. Record the site in g_svc_locations
static void collect_svc_in_segment(uint8_t *code, size_t len, int perm)
{
	csh cs_handle;
	if (cs_open(CS_ARCH_ARM64, CS_MODE_ARM, &cs_handle) != CS_ERR_OK)
		return;

	const uint8_t *curr_code = code;
	size_t size = len;
	uint64_t curr_addr = (uint64_t)(uintptr_t)curr_code;
	cs_insn curr_insn;
	memset(&curr_insn, 0, sizeof(curr_insn));

	uint64_t prev_addr = 0;
	uint32_t prev_insn_raw = 0;

	while (curr_addr < (uintptr_t)code + len) {
		if (!cs_disasm_iter(cs_handle, &curr_code, &size, &curr_addr,
				    &curr_insn)) {
			if (size >= 4) {
				prev_addr = curr_addr;
				prev_insn_raw = *(uint32_t *)curr_code;
				curr_code += 4;
				curr_addr += 4;
				size -= 4;
				continue;
			}
			break;
		}
		if (std::string(cs_insn_name(cs_handle, curr_insn.id)) ==
		    "svc") {
			// Skip our own svc instructions - these are the
			// "escape hatches" for performing real syscalls from
			// within the handler
			if (curr_insn.address == (uintptr_t)&syscall_addr ||
			    curr_insn.address == (uintptr_t)&clone_svc_addr) {
				prev_addr = curr_insn.address;
				prev_insn_raw = *(uint32_t *)(uintptr_t)
					curr_insn.address;
				continue;
			}
			// Try to displace the instruction before svc into a stub
			if (prev_addr == curr_insn.address - 4) {
				if (!is_unsafe_to_displace(prev_insn_raw)) {
					uint32_t displaced =
						adjust_sp_offset_if_needed(
							prev_insn_raw);
					if (displaced != 0) {
						g_svc_locations.push_back(
							{ curr_insn.address,
							  prev_addr, displaced,
							  perm });
					}
				}
			}
		}
		prev_addr = curr_insn.address;
		prev_insn_raw = *(uint32_t *)(uintptr_t)curr_insn.address;
	}
	cs_close(&cs_handle);
}

// Multi-trampoline page management:
// ARM64 bl/b instructions have a +/- 128MB range. Go binaries load at low
// addresses (~0x400000) while libc loads at high addresses (e.g., 0xffff...).
// A single trampoline page can't be in range of both.
//
// Solution: allocate trampoline pages on demand, near each address cluster.
// If the central handler (syscall_hooker_asm) is out of 'b' range from a
// trampoline page, the page starts with a "veneer" - a small code sequence
// that loads the handler address into a register and jumps indirectly:
//   bti c; ldr x17, [pc, #8]; br x17; .quad handler_addr

// Check if addr is within signed +/- 128MB bl/b range of target
static bool in_branch_range(uint64_t from, uint64_t to)
{
	int64_t off = ((int64_t)to - (int64_t)from) / 4;
	return off >= -(1 << 25) && off < (1 << 25);
}

// Allocate a new 64KB trampoline page near the given address.
// Tries offsets from -1MB to +/- 64MB to find a free region in bl range.
static TrampolinePage *alloc_trampoline_near(uint64_t addr)
{
	uint64_t handler_addr = (uint64_t)(uintptr_t)syscall_hooker_asm;
	void *tp = MAP_FAILED;
	// Try negative offsets first (lower addresses)
	for (int64_t delta = -0x100000; delta >= -0x4000000;
	     delta -= 0x100000) {
		uint64_t hint = addr + delta;
		if (hint < 0x10000)
			continue;
		tp = mmap((void *)hint, 0x10000,
			  PROT_READ | PROT_WRITE | PROT_EXEC,
			  MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
		if (tp != MAP_FAILED && in_branch_range(addr, (uint64_t)tp))
			break;
		if (tp != MAP_FAILED) {
			munmap(tp, 0x10000);
			tp = MAP_FAILED;
		}
	}
	// Try positive offsets if negative didn't work
	if (tp == MAP_FAILED) {
		for (int64_t delta = 0x100000; delta <= 0x4000000;
		     delta += 0x100000) {
			uint64_t hint = addr + delta;
			tp = mmap((void *)hint, 0x10000,
				  PROT_READ | PROT_WRITE | PROT_EXEC,
				  MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
			if (tp != MAP_FAILED &&
			    in_branch_range(addr, (uint64_t)tp))
				break;
			if (tp != MAP_FAILED) {
				munmap(tp, 0x10000);
				tp = MAP_FAILED;
			}
		}
	}
	if (tp == MAP_FAILED)
		return nullptr;

	TrampolinePage page;
	page.base = (uint64_t)tp;
	page.end = page.base + 0x10000;
	page.next_stub = (uint32_t *)tp;
	page.veneer_addr = 0;

	// If the handler is not in direct 'b' range from this page, create a
	// veneer. The veneer is a small trampoline that loads the full 64-bit
	// handler address and jumps to it indirectly.
	if (!in_branch_range(page.base, handler_addr)) {
		uint32_t *v = page.next_stub;
		v[0] = 0xd503245f; // bti c
		v[1] = 0x58000071; // ldr x17, [pc, #8] (loads from v[4..5])
		v[2] = 0xd61f0220; // br x17
		v[3] = 0; // padding for alignment
		*(uint64_t *)(v + 4) = handler_addr; // 8-byte handler address literal
		__builtin___clear_cache((char *)v, (char *)(v + 6));
		page.veneer_addr = (uint64_t)v;
		page.next_stub = v + 6;
	}

	SPDLOG_INFO("Trampoline page at {:x} (veneer={})", page.base,
		    page.veneer_addr ? "yes" : "no");
	g_trampoline_pages.push_back(page);
	return &g_trampoline_pages.back();
}

// Find a trampoline page that's in bl range of the given svc address and
// has space for another stub. Allocates a new page if none are suitable.
static TrampolinePage *find_trampoline_for(uint64_t svc_addr)
{
	for (auto &tp : g_trampoline_pages) {
		if (in_branch_range(svc_addr, (uint64_t)tp.next_stub) &&
		    (uint64_t)tp.next_stub + 12 <= tp.end) {
			return &tp;
		}
	}
	return alloc_trampoline_near(svc_addr);
}

// rewrite_all_svc_instructions - apply the two-instruction rewrite.
// For each collected svc site, performs:
//   Original:  <prev_insn>     ->  stp x29, x30, [sp, #-16]!
//              svc #0          ->  bl <stub>
//
//   Stub:      bti c
//              <displaced_insn>   (original prev_insn, possibly SP-adjusted)
//              b <handler>        (or b <veneer> if handler out of range)
static void rewrite_all_svc_instructions()
{
	size_t num_svcs = g_svc_locations.size();
	if (num_svcs == 0)
		return;

	SPDLOG_INFO("Rewriting {} svc pairs", (int)num_svcs);

	uint64_t handler_addr = (uint64_t)(uintptr_t)syscall_hooker_asm;
	size_t rewritten = 0;
	for (size_t i = 0; i < num_svcs; i++) {
		uint64_t svc_addr = g_svc_locations[i].address;
		uint64_t mov_addr = g_svc_locations[i].prev_address;
		int perm = g_svc_locations[i].orig_perm;

		// Find a trampoline page in bl range of this svc site
		TrampolinePage *tp = find_trampoline_for(svc_addr);
		if (!tp) {
			SPDLOG_WARN("No trampoline for svc at {:x}, skipping",
				    svc_addr);
			continue;
		}

		// Make code pages writable for patching
		uint64_t page_mov = mov_addr & ~0xFFFULL;
		uint64_t page_svc = svc_addr & ~0xFFFULL;
		raw_mprotect((void *)page_mov, 0x1000,
			     PROT_READ | PROT_WRITE | PROT_EXEC);
		if (page_svc != page_mov) {
			raw_mprotect((void *)page_svc, 0x1000,
				     PROT_READ | PROT_WRITE | PROT_EXEC);
		}

		// Replace the instruction before svc with: stp x29, x30, [sp, #-16]!
		// This saves the frame pointer and link register, and decrements SP by 16.
		*(volatile uint32_t *)mov_addr = 0xa9bf7bfd;
		__asm__ volatile(
			"dc cvau,%0; dsb ish; ic ivau,%0; dsb ish; isb" ::"r"(
				mov_addr)
			: "memory");

		// Create per-site stub in trampoline page:
		//   [0] bti c                     - branch target identification
		//   [1] <displaced instruction>   - the original instruction (SP-adjusted)
		//   [2] b <handler or veneer>     - jump to central handler
		uint32_t *stub_ptr = tp->next_stub;
		uint64_t stub_addr = (uint64_t)stub_ptr;

		// Choose branch target: direct to handler if in range, else via veneer
		uint64_t branch_target = handler_addr;
		if (!in_branch_range((uint64_t)(stub_ptr + 2), handler_addr)) {
			branch_target = tp->veneer_addr;
		}

		stub_ptr[0] = 0xd503245f; // bti c
		stub_ptr[1] = g_svc_locations[i].displaced_insn; // displaced instruction
		int64_t handler_off =
			((int64_t)branch_target - (int64_t)(stub_ptr + 2)) / 4;
		stub_ptr[2] = 0x14000000 | (handler_off & 0x03ffffff); // b <target>

		__builtin___clear_cache((char *)stub_ptr,
					(char *)(stub_ptr + 3));
		tp->next_stub = stub_ptr + 3;

		// Replace svc #0 with: bl <stub>
		int64_t bl_off = ((int64_t)stub_addr - (int64_t)svc_addr) / 4;
		*(volatile uint32_t *)svc_addr =
			0x94000000 | (bl_off & 0x03ffffff);
		__asm__ volatile(
			"dc cvau,%0; dsb ish; ic ivau,%0; dsb ish; isb" ::"r"(
				svc_addr)
			: "memory");

		// Restore original page permissions
		raw_mprotect((void *)page_mov, 0x1000, perm);
		if (page_svc != page_mov) {
			raw_mprotect((void *)page_svc, 0x1000, perm);
		}

		rewritten++;
	}

	// Full instruction/data barrier after all rewrites
	__asm__ volatile("dsb ish; isb" ::: "memory");

	g_syscall_rewriting_complete = true;
	SPDLOG_INFO("Rewrote {} svc instruction pairs", (int)rewritten);
}
#endif

static inline void rewrite_segment(uint8_t *code, size_t len, int perm)
{
	// Set the pages to be writable
	if (int err = mprotect(code, len, PROT_READ | PROT_WRITE | PROT_EXEC);
	    err < 0) {
		SPDLOG_ERROR(
			"Failed to change the protect status of the rewriting page {:x}",
			(uintptr_t)code);
		exit(1);
	}
	csh cs_handle;
	cs_err ret;
#if defined(__x86_64__)
	ret = cs_open(CS_ARCH_X86, CS_MODE_64, &cs_handle);
#elif defined(__aarch64__)
	ret = cs_open(CS_ARCH_ARM64, CS_MODE_ARM, &cs_handle);
#endif
	if (ret != CS_ERR_OK) {
		SPDLOG_ERROR("Failed to open capstone instance: {}, {}",
			      (int)ret, cs_strerror(ret));
		exit(1);
	}
	const uint8_t *curr_code = code;
	size_t size = len;
	uint64_t curr_addr = (uint64_t)(uintptr_t)curr_code;
	cs_insn curr_insn;
	memset(&curr_insn, 0, sizeof(curr_insn));
	while (curr_addr < (uintptr_t)code + len) {
		auto ok = cs_disasm_iter(cs_handle, &curr_code, &size,
					 &curr_addr, &curr_insn);
		if (!ok) {
			break;
		}
		auto insn_name =
			std::string(cs_insn_name(cs_handle, curr_insn.id));
#if defined(__x86_64__)
		if (insn_name == "syscall" || insn_name == "sysenter") {
			if (curr_insn.address != (uintptr_t)&syscall_addr) {
				uint8_t *curr_pos =
					(uint8_t *)(uintptr_t)curr_insn.address;
				SPDLOG_TRACE("Rewrite syscall insn at {}",
					      (void *)curr_pos);
				curr_pos[0] = 0xff;
				curr_pos[1] = 0xd0;
			}
		}
#endif
	}
	cs_close(&cs_handle);
	if (int err = mprotect(code, len, perm); err < 0) {
		SPDLOG_ERROR(
			"Failed to change the protect status of the rewriting page {:x}",
			(uintptr_t)code);
		exit(1);
	}
}

struct MapEntry {
	uint64_t begin, end;
	char w, r, x;
	std::string path;
	int get_perm() const
	{
		int ret = 0;
		if (w == 'w')
			ret |= PROT_WRITE;
		if (r == 'r')
			ret |= PROT_READ;
		if (x == 'x')
			ret |= PROT_EXEC;
		return ret;
	}
	bool should_skip() const
	{
		if (path == "[vdso]" || path == "[vsyscall]" ||
		    path == "[stack]")
			return true;
		if (path.find("ld-linux") != std::string::npos ||
		    path.find("ld-musl") != std::string::npos)
			return true;
		if (path.find("libbpftime-agent-transformer") !=
		    std::string::npos)
			return true;
		if (path.find("libbpftime-agent.so") != std::string::npos)
			return true;
		return false;
	}
};

namespace bpftime
{

syscall_hooker_func_t get_call_hook()
{
	return call_hook;
}
void set_call_hook(syscall_hooker_func_t hook)
{
	call_hook = hook;
}

void setup_syscall_tracer()
{
	// Guard against being called multiple times (can happen when the agent
	// is loaded via dlopen in the same namespace and re-triggers init).
	static bool already_setup = false;
	if (already_setup)
		return;
	already_setup = true;

#if defined(__x86_64__)
	// x86_64: Setup zpoline (NOP sled at page 0)

	if (auto mmap_addr =
		    mmap(0x0, 0x1000, PROT_EXEC | PROT_READ | PROT_WRITE,
			 MAP_PRIVATE | MAP_FIXED | MAP_ANONYMOUS, -1, 0);
	    mmap_addr == MAP_FAILED) {
		SPDLOG_ERROR("Failed to perform mmap: errno={}, message={}",
			      errno, strerror(errno));
		exit(1);
	}
	// Setup jumpings
	for (int i = 0; i < NR_syscalls; i++) {
		// 0x90; nop
		*((char *)(uintptr_t)(i)) = 0x90;
	}
	// Jump to the syscall handler function after the nop-s
	/*
	50
	push %rax;

	48 b8 88 77 66 55 44 33 22 11
	movabs $0x1122334455667788, %rax; // The constant is the address
	of syscall_hooker_asm

	ff e0
	jmp *%rax;

	*/
	std::vector<uint8_t> codes;
	codes.push_back(0x50);
	codes.push_back(0x48);
	codes.push_back(0xb8);
	for (int i = 0; i < 8; i++) {
		codes.push_back(
			(uint8_t)((((uint64_t)(uintptr_t)syscall_hooker_asm) >>
				   (8 * i)) &
				  0xff));
	}
	codes.push_back(0xff);
	codes.push_back(0xe0);
	std::copy(codes.begin(), codes.end(),
		  (uint8_t *)(uintptr_t)(0 + NR_syscalls));
	// Set the page to execute-only. Keep normal behavior of
	// dereferencing null-pointers
	if (int err = mprotect(0, 0x1000, PROT_EXEC); err < 0) {
		SPDLOG_ERROR(
			"Failed to set execute only of 0-started page: {}",
			errno);
		exit(1);
	}

	SPDLOG_INFO("Page zero setted up..");

#elif defined(__aarch64__)
	// ARM64: Trampoline pages are allocated on-demand during rewrite.
	// No upfront allocation needed - find_trampoline_for() handles it.
	g_trampoline_pages.clear();
	SPDLOG_INFO("ARM64 syscall interception initializing");
#endif

	// Scan for /proc/self/maps
	std::vector<MapEntry> entries;
	std::ifstream ifs("/proc/self/maps");
	while (ifs) {
		std::string line;
		std::getline(ifs, line);

		MapEntry curr;
		char *path_buf;
		int cnt = sscanf(line.c_str(),
				 "%" SCNx64 "-%" SCNx64
				 " %c%c%c%*c %*x %*x:%*x %*d %ms",
				 &curr.begin, &curr.end, &curr.r, &curr.w,
				 &curr.x, &path_buf);
		if (cnt < 5)
			continue;
		if (cnt == 6) {
			curr.path = path_buf;
			free(path_buf);
		}

		entries.push_back(curr);
	}

#if defined(__aarch64__)
	// Phase 1: Scan all executable segments for svc instructions.
	// Skip our own code and system segments to avoid self-hooking.
	g_svc_locations.clear();
	for (const auto &m : entries) {
		if (m.x != 'x')
			continue;
		if (m.should_skip())
			continue;
		collect_svc_in_segment((uint8_t *)(uintptr_t)m.begin,
				       m.end - m.begin, m.get_perm());
	}
	SPDLOG_INFO("Found {} rewritable svc sites",
		    (int)g_svc_locations.size());
	// Phase 2: Rewrite all collected sites (allocates trampolines on demand).
	rewrite_all_svc_instructions();
	SPDLOG_INFO("ARM64 syscall interception ready");
#else
	SPDLOG_INFO("Rewriting executable segments..");
	// Hack the executable mappings
	for (const auto &map : entries) {
		if (map.x == 'x') {
			if (map.begin == 0) {
				// Skip pages that we mapped
				continue;
			}
			if (map.should_skip()) {
				continue;
			}
			SPDLOG_DEBUG("Rewriting segment from {:x} to {:x}",
				      map.begin, map.end);
			rewrite_segment((uint8_t *)(uintptr_t)(map.begin),
					map.end - map.begin, map.get_perm());
		}
	}
#endif
}

} // namespace bpftime
