# Standalone (single-hart) synchronization barrier for zkVM guest builds.
# With one worker, a barrier initialized for N=1 releases immediately;
# wait() returns true for the only thread. No OS primitive exists.

type SyncBarrier* = object
  count: cint

proc init*(syncBarrier: var SyncBarrier, threadCount: cint) {.inline.} =
  # Single-hart guest: only a 1-party barrier is meaningful. Assert so a
  # misconfigured multi-thread barrier fails loudly instead of silently
  # releasing waiters that never rendezvoused.
  doAssert threadCount == 1, "standalone barrier supports exactly 1 thread, got " & $threadCount
  syncBarrier.count = threadCount

proc wait*(syncBarrier: var SyncBarrier): bool {.inline.} =
  # Single hart is always the last (and only) arrival.
  true

proc delete*(syncBarrier: sink SyncBarrier) {.inline.} =
  discard
