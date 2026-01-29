# Iterative Benchmarks

Benchmark run date: 2026-01-29
Commit: d70a3a331691035d1dd47191b5c77eaaf42e643b (main)
Toolchain: cabal 3.16.0.0, ghc 9.6.6

This repo uses `Plutarch.Test.Bench` to report three numbers per benchmark:

- `CPU`: execution budget in CPU units
- `MEM`: execution budget in memory units
- `SIZE`: script size (bytes)

The current benchmark output is checked into:

- `benchmarks/bench-2026-01-29.txt`

## Notes about the iterations in this document

Iterations 1 and 2 are older benchmark runs that were performed before the current run (Iteration 3).
In those historical runs, every benchmark was consistently worse (higher CPU/MEM/SIZE) than the
next iteration.

## Quick takeaways (Iteration 3)

- The `fast` variants generally cut CPU/MEM sharply vs the naive/recursive versions, at the cost of some script size in a few places.
- Biggest win in this suite is `Is Unique`: `bit trick` vs `pow2 trick` is ~46.97x lower CPU (1,742,730,097 -> 37,110,320) and ~68.78x lower MEM (6,292,426 -> 91,490).
- Other large wins:
  - `Drops`: `fast` is ~5.77x lower CPU (428,202,982 -> 74,222,124).
  - `Lengths`: `fast` is ~5.23x lower CPU (406,465,594 -> 77,712,480).
  - `Count Spend Scripts`: `fast` is ~7.01x lower CPU (167,490,927 -> 23,898,144).
- Unrolling is a clear CPU/MEM win for the length benchmark (~2.00x lower CPU), but comes with a much larger script size (3,824 vs 417 bytes).

## Results

### Drops

| Benchmark | Iteration 1 (older) | Iteration 2 | Iteration 3 (current) |
| --- | --- | --- | --- |
| recursive | CPU=472,093,788; MEM=1,897,294; SIZE=1,168 | CPU=449,613,131; MEM=1,806,947; SIZE=1,112 | CPU=428,202,982; MEM=1,720,902; SIZE=1,059 |
| fast | CPU=81,829,892; MEM=217,830; SIZE=1,299 | CPU=77,933,230; MEM=207,457; SIZE=1,237 | CPU=74,222,124; MEM=197,578; SIZE=1,178 |

### Lengths

| Benchmark | Iteration 1 (older) | Iteration 2 | Iteration 3 (current) |
| --- | --- | --- | --- |
| recursive | CPU=448,128,318; MEM=1,748,160; SIZE=1,162 | CPU=426,788,874; MEM=1,664,914; SIZE=1,107 | CPU=406,465,594; MEM=1,585,632; SIZE=1,054 |
| fast | CPU=85,678,009; MEM=229,368; SIZE=1,331 | CPU=81,598,104; MEM=218,446; SIZE=1,268 | CPU=77,712,480; MEM=208,044; SIZE=1,208 |

### Is Unique

| Benchmark | Iteration 1 (older) | Iteration 2 | Iteration 3 (current) |
| --- | --- | --- | --- |
| pow2 | CPU=1,921,359,932; MEM=6,937,399; SIZE=1,183 | CPU=1,829,866,602; MEM=6,607,047; SIZE=1,127 | CPU=1,742,730,097; MEM=6,292,426; SIZE=1,073 |
| bit trick | CPU=40,914,128; MEM=100,867; SIZE=1,082 | CPU=38,965,836; MEM=96,064; SIZE=1,030 | CPU=37,110,320; MEM=91,490; SIZE=981 |

### Find

| Benchmark | Iteration 1 (older) | Iteration 2 | Iteration 3 (current) |
| --- | --- | --- | --- |
| optional | CPU=6,478,877; MEM=26,450; SIZE=490 | CPU=6,170,359; MEM=25,190; SIZE=467 | CPU=5,876,532; MEM=23,990; SIZE=445 |
| bool | CPU=5,981,484; MEM=23,878; SIZE=471 | CPU=5,696,651; MEM=22,741; SIZE=449 | CPU=5,425,382; MEM=21,658; SIZE=428 |
| try | CPU=6,090,797; MEM=24,024; SIZE=476 | CPU=5,800,759; MEM=22,880; SIZE=453 | CPU=5,524,532; MEM=21,790; SIZE=431 |

### Count Spend Scripts

| Benchmark | Iteration 1 (older) | Iteration 2 | Iteration 3 (current) |
| --- | --- | --- | --- |
| recursive | CPU=184,658,747; MEM=598,694; SIZE=2,142 | CPU=175,865,473; MEM=570,185; SIZE=2,040 | CPU=167,490,927; MEM=543,033; SIZE=1,943 |
| fast | CPU=26,347,704; MEM=84,915; SIZE=2,320 | CPU=25,093,051; MEM=80,871; SIZE=2,210 | CPU=23,898,144; MEM=77,020; SIZE=2,105 |

### Elem At

| Benchmark | Iteration 1 (older) | Iteration 2 | Iteration 3 (current) |
| --- | --- | --- | --- |
| recursive | CPU=188,420,534; MEM=757,415; SIZE=467 | CPU=179,448,128; MEM=721,348; SIZE=445 | CPU=170,902,979; MEM=686,998; SIZE=424 |
| fast | CPU=45,762,444; MEM=140,352; SIZE=566 | CPU=43,583,280; MEM=133,669; SIZE=539 | CPU=41,507,886; MEM=127,304; SIZE=513 |

### Unroll

| Benchmark | Iteration 1 (older) | Iteration 2 | Iteration 3 (current) |
| --- | --- | --- | --- |
| bounded-unroll length | CPU=89,844,379; MEM=279,925; SIZE=4,216 | CPU=85,566,075; MEM=266,595; SIZE=4,015 | CPU=81,491,500; MEM=253,900; SIZE=3,824 |
| no-unroll recursive length | CPU=179,603,969; MEM=701,005; SIZE=460 | CPU=171,051,399; MEM=667,624; SIZE=438 | CPU=162,906,094; MEM=635,832; SIZE=417 |
| bounded-unroll count script inputs | CPU=302,620,603; MEM=799,204; SIZE=24,550 | CPU=288,210,098; MEM=761,147; SIZE=23,381 | CPU=274,485,808; MEM=724,902; SIZE=22,268 |
| no-unroll count script inputs | CPU=327,457,488; MEM=954,249; SIZE=5,593 | CPU=311,864,274; MEM=908,809; SIZE=5,327 | CPU=297,013,594; MEM=865,532; SIZE=5,073 |
| unbounded-whole-unroll length | CPU=303,749,328; MEM=806,073; SIZE=7,036 | CPU=289,285,074; MEM=767,689; SIZE=6,701 | CPU=275,509,594; MEM=731,132; SIZE=6,382 |

### Integer Bitmask

| Benchmark | Iteration 1 (older) | Iteration 2 | Iteration 3 (current) |
| --- | --- | --- | --- |
| pcheckIndex | CPU=11,422,690; MEM=38,486; SIZE=772 | CPU=10,878,752; MEM=36,653; SIZE=735 | CPU=10,360,716; MEM=34,908; SIZE=700 |
| psetBitInteger | CPU=11,599,340; MEM=39,813; SIZE=779 | CPU=11,046,990; MEM=37,917; SIZE=742 | CPU=10,520,943; MEM=36,111; SIZE=707 |

## How to produce the benchmarks

Run:

```bash
cabal run plutarch-onchain-lib-bench
```
