# Standalone (single-hart) synchronization barrier for zkVM guest builds.
# With one worker, a barrier initialized for N=1 releases immediately;
# wait() returns true for the only thread. No OS primitive exists.

type SyncBarrier* = object
  count: cint

proc init*(syncBarrier: var SyncBarrier, threadCount: cint) {.inline.} =
  syncBarrier.count = threadCount

proc wait*(syncBarrier: var SyncBarrier): bool {.inline.} =
  # Single hart is always the last (and only) arrival.
  true

proc delete*(syncBarrier: sink SyncBarrier) {.inline.} =
  discard
