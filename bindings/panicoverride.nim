{.push stack_trace: off, profiler: off.}

proc rawoutput(s: string) =
  discard

proc panic(s: string) {.noreturn.} =
  rawoutput(s)
  while true:
    discard

{.pop.}
