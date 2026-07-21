import constantine/threadpool

# Just check this won't hang
const numThreads = 257
const numTasks = numThreads * 4

proc nothing() =
  discard

proc main() =
  echo "\n=============================================================================================="
  echo "Running 'tests/threadpool/t_257_threads.nim'"
  echo "=============================================================================================="

  let tp = Threadpool.new(numThreads = numThreads)
  for _ in 0 ..< numTasks:
    tp.spawn nothing()
  tp.shutdown()

  echo "ok"

main()
