# Standalone (bare-metal) panic hook for zkVM guest builds. Included by
# lib_constantine.nim under --os:standalone. There is no OS to abort() into;
# a panic is a guest bug, so trap in place. The procs are compilerprocs so
# they override the Nim runtime's default panic/rawoutput symbols.
{.push stack_trace: off, profiler: off.}

proc rawoutput(s: string) {.compilerproc.} =
  discard

proc panic(s: string) {.noreturn, compilerproc.} =
  rawoutput(s)
  while true:
    discard

{.pop.}
