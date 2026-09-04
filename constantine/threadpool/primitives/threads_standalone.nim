# Standalone (bare-metal, single-hart) thread shim for zkVM guest builds.
# No OS threads exist under --os:standalone. With a single hart the
# threadpool is constructed with num_threads == 1 and the spawn loop
# `for i in 1 ..< 1` is empty at runtime, so createThread is never called.
# It exists only to satisfy the type-checker; reaching it is a trap.

type Thread*[T] = object
  ## Placeholder thread handle. Never instantiated in a single-hart guest.

proc createThread*[T](t: var Thread[T], fn: proc(x: T) {.thread.}, arg: T) =
  when defined(standalone):
    # Single-hart guest: spawning a second thread is a programming error.
    while true:
      discard
  else:
    discard

proc joinThread*[T](t: Thread[T]) =
  discard

proc getNumCores*(): cint =
  1
