# Strong Memo Final-Active Member-Factor Sweep

Generated: 2026-06-03T21:14:40.2560040+08:00

- Seeds: 20260602,20260603,20260604,20260605,20260606
- Random cases per seed: 10000
- Random depth/input length: 7 / 10
- Rows budget: 1 * rsize(r)
- Pair budget: 1 * rsize(r)^2
- Minimum regex size: 5

| Member factor | Result | Worst member ratio | Failure | Failure label | Report | Run log |
| ---: | --- | ---: | --- | --- | --- | --- |
| 8 | pass | 6.809524 | - | - | factor_8/summary.md | factor_8/run.log |
| 10 | pass | 6.809524 | - | - | factor_10/summary.md | factor_10/run.log |
| 12 | pass | 6.809524 | - | - | factor_12/summary.md | factor_12/run.log |

A pass is smoke evidence only. A fail records a concrete budget counterexample
from the seed log and rules out using that member factor as the current proof target.
