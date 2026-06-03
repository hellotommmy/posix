# Strong Memo Final-Active Member-Factor Sweep

Generated: 2026-06-03T21:05:39.7012805+08:00

- Seeds: 20260602,20260603,20260604
- Random cases per seed: 5000
- Random depth/input length: 6 / 8
- Rows budget: 1 * rsize(r)
- Pair budget: 1 * rsize(r)^2
- Minimum regex size: 5

| Member factor | Result | Worst member ratio | Failure | Failure label | Report | Run log |
| ---: | --- | ---: | --- | --- | --- | --- |
| 4 | fail | 6.500000 | finalActiveMaxRowSize=195 > 120 | random seed=20260602 case=4784 | - | factor_4/run.log |
| 6 | fail | 6.500000 | finalActiveMaxRowSize=195 > 180 | random seed=20260602 case=4784 | - | factor_6/run.log |
| 8 | pass | 6.500000 | - | - | factor_8/summary.md | factor_8/run.log |

A pass is smoke evidence only. A fail records a concrete budget counterexample
from the seed log and rules out using that member factor as the current proof target.
