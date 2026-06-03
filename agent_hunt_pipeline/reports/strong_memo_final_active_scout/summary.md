# Strong Memo Final-Active Scout

Generated: 2026-06-03T20:30:18.9097183+08:00

- Route: strong-memo
- Random cases per seed: 5000
- Random depth/input length: 6 / 8
- Rows budget: 1 * rsize(r)
- Member-size budget: 8 * rsize(r)
- Pair budget: 1 * rsize(r)^2
- Minimum regex size: 5

| Seed | Budget CE? | Worst rows ratio | Rows witness | Worst member ratio | Member witness | Worst pair ratio | Pair witness | Log |
| ---: | --- | ---: | --- | ---: | --- | ---: | --- | --- |
| 20260602 | no | 0.571429 | random seed=20260602 case=995 rsize=28 input=abbbaab regex=NTIMES(ALT(SEQ(ONE,ALT(SEQ(CH(b),ALT(CH(b),ONE)),ZERO)),NTIMES(STAR(ALT(SEQ(STAR(STAR(CH(b))),CH(a)),STAR(STAR(CH(b))))),3)),3) | 6.500000 | random seed=20260602 case=4784 rsize=30 input=bbbb regex=ALT(SEQ(SEQ(STAR(SEQ(ALT(ONE,SEQ(CH(b),CH(b))),STAR(ALT(CH(b),ONE)))),STAR(STAR(NTIMES(ALT(ALT(CH(b),ZERO),STAR(CH(b))),2)))),STAR(STAR(STAR(CH(a))))),ZERO) | 0.040000 | exhaustive case 65596 rsize=5 input= regex=SEQ(ALT(CH(a),CH(a)),ZERO) | seed_20260602.log |
| 20260603 | no | 0.304348 | random seed=20260603 case=2733 rsize=23 input=baaab regex=STAR(STAR(SEQ(STAR(STAR(STAR(SEQ(CH(a),CH(a))))),NTIMES(ALT(STAR(STAR(SEQ(ONE,CH(b)))),STAR(STAR(ALT(CH(b),CH(a))))),2)))) | 3.173913 | random seed=20260603 case=3224 rsize=23 input=bbba regex=NTIMES(STAR(STAR(ALT(STAR(NTIMES(ALT(SEQ(ZERO,CH(b)),CH(a)),1)),ALT(SEQ(ZERO,ONE),STAR(STAR(ALT(CH(a),CH(b)))))))),2) | 0.040000 | exhaustive case 65596 rsize=5 input= regex=SEQ(ALT(CH(a),CH(a)),ZERO) | seed_20260603.log |
| 20260604 | no | 0.782609 | random seed=20260604 case=4077 rsize=23 input=aaaaa regex=NTIMES(STAR(NTIMES(NTIMES(ALT(SEQ(ALT(SEQ(CH(a),CH(a)),ONE),STAR(STAR(CH(a)))),ONE),3),2)),3) | 4.108108 | random seed=20260604 case=2797 rsize=37 input=baab regex=ALT(SEQ(ALT(SEQ(NTIMES(STAR(STAR(ALT(SEQ(ALT(SEQ(ZERO,ZERO),CH(b)),NTIMES(ONE,0)),SEQ(CH(a),CH(a))))),3),CH(b)),SEQ(NTIMES(STAR(STAR(NTIMES(ZERO,0))),1),CH(a))),STAR(STAR(SEQ(ONE,CH(b))))),CH(b)) | 0.040000 | exhaustive case 65596 rsize=5 input= regex=SEQ(ALT(CH(a),CH(a)),ZERO) | seed_20260604.log |

A no entry means the smoke run found no final-active witness above
the configured linear rows, linear member-size, or quadratic pair-budget. This is smoke
evidence for the strong-memo proof route, not an Isabelle proof.
