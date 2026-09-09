# Standalone panic hook for bare-metal guest builds. A panic traps in place.
# The compilerprocs replace the Nim runtime's default panic/output path.
{.push stack_trace: off, profiler: off.}

proc rawoutput(s: string) {.compilerproc, codegenDecl: "static $# $#$#".} =
  discard

proc panic(s: string) {.noreturn, compilerproc,
    codegenDecl: "static $# $#$#".} =
  rawoutput(s)
  while true:
    discard

{.pop.}
