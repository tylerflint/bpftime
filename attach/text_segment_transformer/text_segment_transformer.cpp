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
- x8:  syscall number
- x0-x5: arguments
- x0: return value

ARM64 C calling convention:
- x0-x7: arguments
- x0: return value
- x30 (LR): return address
- x29 (FP): frame pointer

When we replace `svc #0` with `bl <trampoline>`, x30 contains the return address.
*/

// Global trampoline address for ARM64 (set during setup)
static void *g_arm64_trampoline_addr = nullptr;

[[maybe_unused]] void __asm_holder()
{
	// syscall_hooker_asm: Entry point from bl instruction
	// x30 has return address (set by bl instruction)
	// x8 has syscall number, x0-x5 have arguments
	__asm__(
		".globl syscall_hooker_asm\n\t"
		"syscall_hooker_asm:\n\t"
		// Check for rt_sigreturn (syscall 139 on ARM64)
		"cmp x8, #139\n\t"
		"b.eq handle_sigreturn\n\t"

		// Save frame pointer and link register
		"stp x29, x30, [sp, #-16]!\n\t"
		"mov x29, sp\n\t"

		// Save callee-saved registers we'll use
		"stp x19, x20, [sp, #-16]!\n\t"
		"stp x21, x22, [sp, #-16]!\n\t"

		// Save syscall arguments (x0-x5) and syscall number (x8)
		"stp x0, x1, [sp, #-16]!\n\t"
		"stp x2, x3, [sp, #-16]!\n\t"
		"stp x4, x5, [sp, #-16]!\n\t"
		"str x8, [sp, #-16]!\n\t"

		// Convert syscall ABI to C ABI for syscall_hooker_cxx:
		// C ABI: x0=syscall_nr, x1=arg1, x2=arg2, x3=arg3, x4=arg4, x5=arg5, x6=arg6
		// Note: arg6 (original x5) goes to x6
		"mov x6, x5\n\t"  // arg6
		"mov x5, x4\n\t"  // arg5
		"mov x4, x3\n\t"  // arg4
		"mov x3, x2\n\t"  // arg3
		"mov x2, x1\n\t"  // arg2
		"mov x1, x0\n\t"  // arg1
		"mov x0, x8\n\t"  // syscall_nr

		// Call the C++ hook function
		"bl syscall_hooker_cxx\n\t"

		// Result is in x0, restore stack
		"add sp, sp, #16\n\t"       // Skip saved x8
		"add sp, sp, #16\n\t"       // Skip saved x4, x5
		"add sp, sp, #16\n\t"       // Skip saved x2, x3
		"add sp, sp, #16\n\t"       // Skip saved x0, x1

		// Restore callee-saved registers
		"ldp x21, x22, [sp], #16\n\t"
		"ldp x19, x20, [sp], #16\n\t"

		// Restore frame pointer and link register
		"ldp x29, x30, [sp], #16\n\t"

		// Return to caller (x0 has return value)
		"ret\n\t"
	);

	// call_orig_syscall: Execute original syscall
	// C ABI input: x0=syscall_nr, x1=arg1, x2=arg2, x3=arg3, x4=arg4, x5=arg5, x6=arg6
	__asm__(
		".globl call_orig_syscall\n\t"
		"call_orig_syscall:\n\t"
		// Convert C ABI back to syscall ABI
		"mov x8, x0\n\t"   // syscall_nr to x8
		"mov x0, x1\n\t"   // arg1
		"mov x1, x2\n\t"   // arg2
		"mov x2, x3\n\t"   // arg3
		"mov x3, x4\n\t"   // arg4
		"mov x4, x5\n\t"   // arg5
		"mov x5, x6\n\t"   // arg6

		"handle_sigreturn:\n\t"
		".globl syscall_addr\n\t"
		"syscall_addr:\n\t"
		"svc #0\n\t"
		"ret\n\t"
	);
}
#else
#error "Unsupported architecture"
#endif

extern "C" int64_t syscall_hooker_cxx(int64_t sys_nr, int64_t arg1,
				      int64_t arg2, int64_t arg3, int64_t arg4,
				      int64_t arg5, int64_t arg6)
{
	return call_hook(sys_nr, arg1, arg2, arg3, arg4, arg5, arg6);
}

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
#elif defined(__aarch64__)
		if (insn_name == "svc") {
			// Skip our own svc instruction
			if (curr_insn.address == (uintptr_t)&syscall_addr) {
				continue;
			}

			// Calculate relative offset for bl instruction
			// bl has a 26-bit signed immediate (in units of 4 bytes)
			// Range: +/- 128MB (2^25 instructions * 4 bytes)
			int64_t offset = (int64_t)g_arm64_trampoline_addr -
					 (int64_t)curr_insn.address;
			int64_t offset_insns = offset / 4;

			// Check if offset is within bl range (+/- 2^25 instructions)
			if (offset_insns < -(1 << 25) ||
			    offset_insns >= (1 << 25)) {
				SPDLOG_WARN(
					"svc instruction at {:x} is too far from trampoline ({:x}), skipping",
					curr_insn.address,
					(uintptr_t)g_arm64_trampoline_addr);
				continue;
			}

			uint8_t *curr_pos =
				(uint8_t *)(uintptr_t)curr_insn.address;
			SPDLOG_TRACE("Rewrite svc insn at {}",
				      (void *)curr_pos);

			// Encode bl instruction: 0x94000000 | (imm26 & 0x03ffffff)
			uint32_t bl_insn =
				0x94000000 | (offset_insns & 0x03ffffff);

			// Write the bl instruction (little-endian)
			curr_pos[0] = (uint8_t)(bl_insn & 0xff);
			curr_pos[1] = (uint8_t)((bl_insn >> 8) & 0xff);
			curr_pos[2] = (uint8_t)((bl_insn >> 16) & 0xff);
			curr_pos[3] = (uint8_t)((bl_insn >> 24) & 0xff);
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
	// ARM64: Allocate a trampoline page and use direct bl instructions
	// The zpoline technique (NOP sled at address 0) doesn't work on ARM64
	// because instructions are 4 bytes and must be aligned.
	// Instead, we allocate a trampoline page and replace svc #0 with
	// bl <trampoline>.

	// Try to allocate trampoline near 4GB boundary for good reach
	// bl instruction has +/- 128MB range, so placing near middle of
	// address space helps reach more code
	void *hint_addr = (void *)0x100000000ULL; // 4GB
	void *trampoline_page = mmap(
		hint_addr, 0x1000, PROT_READ | PROT_WRITE | PROT_EXEC,
		MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);

	if (trampoline_page == MAP_FAILED) {
		// Try without hint
		trampoline_page =
			mmap(nullptr, 0x1000, PROT_READ | PROT_WRITE | PROT_EXEC,
			     MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
		if (trampoline_page == MAP_FAILED) {
			SPDLOG_ERROR(
				"Failed to allocate ARM64 trampoline page: errno={}, message={}",
				errno, strerror(errno));
			exit(1);
		}
	}

	SPDLOG_INFO("ARM64 trampoline page allocated at {:x}",
		     (uintptr_t)trampoline_page);

	// Build trampoline code:
	// Optional: bti c (for BTI-enabled binaries)
	// Load syscall_hooker_asm address into x16 using MOVZ/MOVK
	// br x16
	uint32_t *trampoline_code = (uint32_t *)trampoline_page;
	uint64_t handler_addr = (uint64_t)(uintptr_t)syscall_hooker_asm;
	int idx = 0;

	// BTI landing pad for indirect branches (bti c)
	// Encoding: 0xd503245f
	trampoline_code[idx++] = 0xd503245f;

	// movz x16, #<bits 0-15>
	// Encoding: 0xd2800010 | (imm16 << 5)
	trampoline_code[idx++] =
		0xd2800010 | ((handler_addr & 0xffff) << 5);

	// movk x16, #<bits 16-31>, lsl #16
	// Encoding: 0xf2a00010 | (imm16 << 5)
	trampoline_code[idx++] =
		0xf2a00010 | (((handler_addr >> 16) & 0xffff) << 5);

	// movk x16, #<bits 32-47>, lsl #32
	// Encoding: 0xf2c00010 | (imm16 << 5)
	trampoline_code[idx++] =
		0xf2c00010 | (((handler_addr >> 32) & 0xffff) << 5);

	// movk x16, #<bits 48-63>, lsl #48
	// Encoding: 0xf2e00010 | (imm16 << 5)
	trampoline_code[idx++] =
		0xf2e00010 | (((handler_addr >> 48) & 0xffff) << 5);

	// br x16
	// Encoding: 0xd61f0200
	trampoline_code[idx++] = 0xd61f0200;

	// Store trampoline address globally
	g_arm64_trampoline_addr = trampoline_page;

	// Clear instruction cache for the trampoline
	__builtin___clear_cache((char *)trampoline_page,
				(char *)trampoline_page + idx * 4);

	// Make trampoline read-execute only
	if (int err = mprotect(trampoline_page, 0x1000, PROT_READ | PROT_EXEC);
	    err < 0) {
		SPDLOG_ERROR(
			"Failed to set ARM64 trampoline page permissions: {}",
			errno);
		exit(1);
	}

	SPDLOG_INFO("ARM64 trampoline set up at {:x}, handler at {:x}",
		     (uintptr_t)trampoline_page, handler_addr);
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
			std::string buf = path_buf;
			free(path_buf);
			if (buf == "[stack]" || buf == "[vsyscall]") {
				continue;
			}
		}

		entries.push_back(curr);
	}
	SPDLOG_INFO("Rewriting executable segments..");
	// Hack the executable mappings
	for (const auto &map : entries) {
		if (map.x == 'x') {
#if defined(__x86_64__)
			if (map.begin == 0) {
				// Skip pages that we mapped
				continue;
			}
#elif defined(__aarch64__)
			// Skip the trampoline page we allocated
			if ((uintptr_t)g_arm64_trampoline_addr >= map.begin &&
			    (uintptr_t)g_arm64_trampoline_addr < map.end) {
				continue;
			}
#endif
			SPDLOG_DEBUG("Rewriting segment from {:x} to {:x}",
				      map.begin, map.end);
			rewrite_segment((uint8_t *)(uintptr_t)(map.begin),
					map.end - map.begin, map.get_perm());
		}
	}
}

} // namespace bpftime
