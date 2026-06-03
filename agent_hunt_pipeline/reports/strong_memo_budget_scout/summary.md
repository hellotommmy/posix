# Strong Memo Budget Scout

Generated: 2026-06-03T19:24:46.1373967+08:00

- Route: strong-memo
- Random cases per seed: 2000
- Random depth/input length: 6 / 8
- Cubic factor: 1 * rsize(r)^3
- Minimum regex size: 5

| Seed | Budget CE? | Worst ratio | Witness | Log |
| ---: | --- | ---: | --- | --- |
| 20260602 | no | 0.112000 | exhaustive case 1080 tree=14 rsize=5 input=bbb regex=NTIMES(STAR(CH(b)),2) | seed_20260602.log |
| 20260603 | no | 0.112000 | exhaustive case 1080 tree=14 rsize=5 input=bbb regex=NTIMES(STAR(CH(b)),2) | seed_20260603.log |

A no entry means the smoke run found no final strong-tree witness
above the configured cubic budget. This is smoke evidence only, not an
Isabelle proof of the cubic theorem.
