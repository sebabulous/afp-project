The benchmarks code in Map.hs code is based on https://github.com/haskell-perf/dictionaries/tree/master. The benchmarks of the other dictionary data structures are removed.

To add the benchmarks of the agda implementation the following steps are done:
- A Map.agda file is created where the functions that are needed are defined / imported
- Run in command line: agda --compile Map.agda to create MAlonzo directory 
- Import the files of the MAlonzo directory that are needed into the Map.hs which holds the benchmarks and add to the bgroups
- Command that creates out.csv: cabal run map 
<!-- RESULTS -->

## Insert Integer (Randomized)

|Name|10|50|100|150|200|
|---|---|---|---|---|---|
|Haskell|22.00 μs|0.055 ms|0.112 ms|0.173 ms|0.000 s|
|Data.Map.Lazy.Agda|857.5 μs|47.77 ms|346.5 ms|1117 ms|3.593 s|

