# Strong Memo Final-Active Scout

Generated: 2026-06-03T19:43:51.0215056+08:00

- Route: strong-memo
- Random cases per seed: 2000
- Random depth/input length: 6 / 8
- Rows budget: 1 * rsize(r)
- Pair budget: 1 * rsize(r)^2
- Minimum regex size: 5

| Seed | Budget CE? | Worst rows ratio | Rows witness | Worst pair ratio | Pair witness | Log |
| ---: | --- | ---: | --- | ---: | --- | --- |
| 20260602 | no | 0.571429 | random seed=20260602 case=995 rsize=28 input=abbbaab regex=NTIMES(ALT(SEQ(ONE,ALT(SEQ(CH(b),ALT(CH(b),ONE)),ZERO)),NTIMES(STAR(ALT(SEQ(STAR(STAR(CH(b))),CH(a)),STAR(STAR(CH(b))))),3)),3) | 0.040000 | exhaustive case 65596 rsize=5 input= regex=SEQ(ALT(CH(a),CH(a)),ZERO) | seed_20260602.log |
| 20260603 | no | 0.217391 | random seed=20260603 case=460 rsize=23 input=bbbbb regex=STAR(STAR(ALT(NTIMES(ONE,0),NTIMES(ALT(SEQ(ALT(ALT(CH(b),ONE),SEQ(ZERO,CH(b))),ONE),STAR(ALT(CH(b),CH(a)))),3)))) | 0.040000 | exhaustive case 65596 rsize=5 input= regex=SEQ(ALT(CH(a),CH(a)),ZERO) | seed_20260603.log |

A no entry means the smoke run found no final-active witness above
the configured linear rows or quadratic pair-budget. This is smoke
evidence for the strong-memo proof route, not an Isabelle proof.
