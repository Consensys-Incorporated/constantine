/* Freestanding declarations only — no libc. Implementations are provided at
 * link time by the compiler runtime (Zig compiler_rt / LLVM builtins). */
#ifndef CTT_STANDALONE_STRING_H
#define CTT_STANDALONE_STRING_H

#include <stddef.h>

void *memcpy(void *restrict dest, const void *restrict src, size_t n);
void *memmove(void *dest, const void *src, size_t n);
void *memset(void *dest, int c, size_t n);
int   memcmp(const void *s1, const void *s2, size_t n);
size_t strlen(const char *s);

/* -ffreestanding implies -fno-builtin, so plain memset/memcpy calls are never
 * inlined or elided. Nim zero-initialises every non-{.noInit.} variable via
 * memset, which then costs an out-of-line call per temporary. The __builtin_
 * forms stay optimisable (dead-store elimination, small constant sizes inlined)
 * and still lower to a call to the same symbols when not elided. */
#define memcpy(d, s, n)  __builtin_memcpy((d), (s), (n))
#define memmove(d, s, n) __builtin_memmove((d), (s), (n))
#define memset(d, c, n)  __builtin_memset((d), (c), (n))
#define memcmp(a, b, n)  __builtin_memcmp((a), (b), (n))

#endif
