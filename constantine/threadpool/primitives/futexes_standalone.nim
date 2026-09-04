# Standalone (bare-metal) futex shim for zkVM guest builds.
# Single-threaded under --os:standalone: no OS futex primitive exists.
# wait() spins on the word; with one worker there is never a cross-thread
# waiter, so this reduces to a memory fence.

import std/atomics
export MemoryOrder

type
  Futex* = object
    value: Atomic[uint32]

proc initialize*(futex: var Futex) {.inline.} =
  futex.value.store(0, moRelaxed)

proc teardown*(futex: var Futex) {.inline.} =
  futex.value.store(0, moRelaxed)

proc load*(futex: var Futex, order: MemoryOrder): uint32 {.inline.} =
  futex.value.load(order)

proc store*(futex: var Futex, value: uint32, order: MemoryOrder) {.inline.} =
  futex.value.store(value, order)

proc increment*(futex: var Futex, value: uint32, order: MemoryOrder): uint32 {.inline.} =
  futex.value.fetchAdd(value, order)

proc wait*(futex: var Futex, expected: uint32) {.inline.} =
  while futex.value.load(moAcquire) == expected:
    discard

proc wake*(futex: var Futex) {.inline.} =
  discard

proc wakeAll*(futex: var Futex) {.inline.} =
  discard
