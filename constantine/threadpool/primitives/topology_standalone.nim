# Standalone topology shim: one core, no OS to query.

proc queryNumPhysicalCoresStandalone*(): cint =
  1

proc queryAvailableThreadsStandalone*(): cint =
  1
