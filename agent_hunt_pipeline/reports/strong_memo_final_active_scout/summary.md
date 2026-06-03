# Strong Memo Final-Active Scout

Generated: 2026-06-04T01:25:01.7770183+08:00

- Route: strong-memo
- Random cases per seed: 5000
- Random depth/input length: 6 / 8
- Rows budget: 1 * rsize(r)
- Member-size budget: 0 * rsize(r)
- Member DAG budget: 2 * rsize(r)
- Member shape-DAG budget: 2 * rsize(r)
- Pair budget: 1 * rsize(r)^2
- Minimum regex size: 5

| Seed | Budget CE? | Worst rows ratio | Rows witness | Worst raw member ratio | Raw witness | Worst DAG ratio | DAG witness | Worst shape-DAG ratio | Shape-DAG witness | Worst pair ratio | Pair witness | Log |
| ---: | --- | ---: | --- | ---: | --- | ---: | --- | ---: | --- | ---: | --- | --- |
| 20260602 | no | 0.571429 | random seed=20260602 case=995 rsize=28 input=abbbaab regex=NTIMES(ALT(SEQ(ONE,ALT(SEQ(CH(b),ALT(CH(b),ONE)),ZERO)),NTIMES(STAR(ALT(SEQ(STAR(STAR(CH(b))),CH(a)),STAR(STAR(CH(b))))),3)),3) | 5.633333 | random seed=20260602 case=4784 rsize=30 input=bbbb regex=ALT(SEQ(SEQ(STAR(SEQ(ALT(ONE,SEQ(CH(b),CH(b))),STAR(ALT(CH(b),ONE)))),STAR(STAR(NTIMES(ALT(ALT(CH(b),ZERO),STAR(CH(b))),2)))),STAR(STAR(STAR(CH(a))))),ZERO) | 1.266667 | random seed=20260602 case=4784 rsize=30 input=bbbb regex=ALT(SEQ(SEQ(STAR(SEQ(ALT(ONE,SEQ(CH(b),CH(b))),STAR(ALT(CH(b),ONE)))),STAR(STAR(NTIMES(ALT(ALT(CH(b),ZERO),STAR(CH(b))),2)))),STAR(STAR(STAR(CH(a))))),ZERO) | 1.266667 | random seed=20260602 case=4784 rsize=30 input=bbbb regex=ALT(SEQ(SEQ(STAR(SEQ(ALT(ONE,SEQ(CH(b),CH(b))),STAR(ALT(CH(b),ONE)))),STAR(STAR(NTIMES(ALT(ALT(CH(b),ZERO),STAR(CH(b))),2)))),STAR(STAR(STAR(CH(a))))),ZERO) | 0.040000 | exhaustive case 65596 rsize=5 input= regex=SEQ(ALT(CH(a),CH(a)),ZERO) | seed_20260602.log |
| 20260603 | no | 0.304348 | random seed=20260603 case=2733 rsize=23 input=baaab regex=STAR(STAR(SEQ(STAR(STAR(STAR(SEQ(CH(a),CH(a))))),NTIMES(ALT(STAR(STAR(SEQ(ONE,CH(b)))),STAR(STAR(ALT(CH(b),CH(a))))),2)))) | 2.739130 | Chapter 7 k=5 n=8 rsize=46 input=aaaaaaaa regex=STAR(STAR(ALT(STAR(SEQ(CH(a),ONE)),ALT(STAR(SEQ(CH(a),SEQ(CH(a),ONE))),ALT(STAR(SEQ(CH(a),SEQ(CH(a),SEQ(CH(a),ONE)))),ALT(STAR(SEQ(CH(a),SEQ(CH(a),SEQ(CH(a),SEQ(CH(a),ONE))))),STAR(SEQ(CH(a),SEQ(CH(a),SEQ(CH(a),SEQ(CH(a)... | 1.000000 | known CE full-cert greedy sequence CE input=b rsize=10 input=b regex=SEQ(STAR(ALT(STAR(CH(b)),SEQ(CH(b),CH(a)))),STAR(CH(a))) | 1.000000 | known CE full-cert greedy sequence CE input=b rsize=10 input=b regex=SEQ(STAR(ALT(STAR(CH(b)),SEQ(CH(b),CH(a)))),STAR(CH(a))) | 0.040000 | exhaustive case 65596 rsize=5 input= regex=SEQ(ALT(CH(a),CH(a)),ZERO) | seed_20260603.log |
| 20260604 | no | 0.782609 | random seed=20260604 case=4077 rsize=23 input=aaaaa regex=NTIMES(STAR(NTIMES(NTIMES(ALT(SEQ(ALT(SEQ(CH(a),CH(a)),ONE),STAR(STAR(CH(a)))),ONE),3),2)),3) | 3.718750 | random seed=20260604 case=2678 rsize=32 input=aaabba regex=NTIMES(SEQ(STAR(STAR(ALT(STAR(STAR(ALT(CH(a),CH(b)))),CH(a)))),ALT(CH(b),ALT(STAR(STAR(ALT(SEQ(CH(a),ONE),ONE))),ALT(SEQ(ALT(ZERO,CH(a)),CH(b)),STAR(STAR(ONE)))))),2) | 1.000000 | known CE full-cert greedy sequence CE input=b rsize=10 input=b regex=SEQ(STAR(ALT(STAR(CH(b)),SEQ(CH(b),CH(a)))),STAR(CH(a))) | 1.000000 | known CE full-cert greedy sequence CE input=b rsize=10 input=b regex=SEQ(STAR(ALT(STAR(CH(b)),SEQ(CH(b),CH(a)))),STAR(CH(a))) | 0.040000 | exhaustive case 65596 rsize=5 input= regex=SEQ(ALT(CH(a),CH(a)),ZERO) | seed_20260604.log |

A no entry means the smoke run found no final-active witness above
the configured linear rows, exact-DAG member, shape-DAG member, raw member,
or quadratic pair budget. This is smoke
evidence for the strong-memo proof route, not an Isabelle proof.
