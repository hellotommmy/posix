# Strong Memo Final-Active Scout

Generated: 2026-06-03T21:13:36.6928933+08:00

- Route: strong-memo
- Random cases per seed: 10000
- Random depth/input length: 7 / 10
- Rows budget: 1 * rsize(r)
- Member-size budget: 10 * rsize(r)
- Pair budget: 1 * rsize(r)^2
- Minimum regex size: 5

| Seed | Budget CE? | Worst rows ratio | Rows witness | Worst member ratio | Member witness | Worst pair ratio | Pair witness | Log |
| ---: | --- | ---: | --- | ---: | --- | ---: | --- | --- |
| 20260602 | no | 0.312500 | random seed=20260602 case=5858 rsize=32 input=bbbaaaba regex=NTIMES(STAR(STAR(ALT(SEQ(CH(b),ZERO),ALT(STAR(STAR(ALT(ALT(ZERO,ONE),ALT(CH(a),ZERO)))),STAR(STAR(ALT(SEQ(ALT(CH(a),ZERO),ALT(ONE,CH(a))),ALT(CH(b),ZERO)))))))),2) | 5.880000 | random seed=20260602 case=8521 rsize=25 input=b regex=STAR(STAR(STAR(STAR(STAR(NTIMES(SEQ(SEQ(STAR(CH(b)),CH(b)),ALT(SEQ(ALT(SEQ(CH(b),CH(a)),ONE),STAR(ZERO)),NTIMES(ZERO,2))),1)))))) | 0.040000 | exhaustive case 65596 rsize=5 input= regex=SEQ(ALT(CH(a),CH(a)),ZERO) | seed_20260602.log |
| 20260603 | no | 0.350000 | random seed=20260603 case=4131 rsize=20 input=bbbbbb regex=STAR(NTIMES(STAR(ALT(SEQ(CH(b),CH(b)),SEQ(STAR(STAR(ALT(SEQ(CH(b),CH(a)),CH(b)))),STAR(STAR(CH(b)))))),2)) | 5.153846 | random seed=20260603 case=2190 rsize=26 input=a regex=STAR(STAR(STAR(ALT(SEQ(STAR(STAR(NTIMES(ALT(SEQ(CH(b),ZERO),CH(a)),2))),STAR(STAR(NTIMES(ALT(SEQ(ZERO,CH(b)),CH(a)),2)))),CH(b))))) | 0.040000 | random seed=20260603 case=8868 rsize=5 input= regex=SEQ(ALT(ZERO,ONE),ONE) | seed_20260603.log |
| 20260604 | no | 0.473684 | random seed=20260604 case=1244 rsize=38 input=bbaaa regex=STAR(NTIMES(STAR(STAR(SEQ(ALT(SEQ(STAR(ONE),ALT(SEQ(SEQ(ZERO,ZERO),ONE),ALT(SEQ(CH(a),CH(b)),ONE))),SEQ(ONE,STAR(STAR(ZERO)))),STAR(STAR(ALT(SEQ(STAR(CH(a)),ALT(ONE,CH(b))),CH(b))))))),3)) | 5.052632 | random seed=20260604 case=637 rsize=38 input=aaabbb regex=STAR(ALT(SEQ(STAR(STAR(NTIMES(STAR(STAR(SEQ(ALT(SEQ(ONE,CH(b)),ONE),SEQ(ONE,CH(b))))),2))),ONE),STAR(STAR(NTIMES(ALT(SEQ(STAR(STAR(CH(a))),ONE),ALT(SEQ(STAR(STAR(ZERO)),CH(a)),CH(b))),2))))) | 0.040000 | exhaustive case 65596 rsize=5 input= regex=SEQ(ALT(CH(a),CH(a)),ZERO) | seed_20260604.log |
| 20260605 | no | 0.666667 | random seed=20260605 case=1109 rsize=18 input=bbbbab regex=NTIMES(NTIMES(STAR(STAR(NTIMES(ALT(ALT(CH(b),CH(a)),STAR(CH(b))),3))),3),1) | 6.809524 | random seed=20260605 case=6337 rsize=21 input=bb regex=STAR(SEQ(STAR(STAR(CH(b))),STAR(STAR(STAR(NTIMES(ALT(SEQ(ONE,ALT(ZERO,ZERO)),STAR(STAR(CH(b)))),3)))))) | 0.040000 | exhaustive case 65596 rsize=5 input= regex=SEQ(ALT(CH(a),CH(a)),ZERO) | seed_20260605.log |
| 20260606 | no | 0.264151 | random seed=20260606 case=2304 rsize=53 input=bbb regex=STAR(ALT(SEQ(ONE,STAR(SEQ(ALT(SEQ(ALT(SEQ(ALT(CH(a),CH(b)),ALT(SEQ(CH(b),ONE),CH(b))),SEQ(ONE,CH(a))),ALT(SEQ(NTIMES(ZERO,0),ONE),ALT(SEQ(CH(b),CH(a)),ZERO))),STAR(STAR(CH(b)))),ALT(ALT(STAR(STAR(ZERO)),ZERO),ALT(SEQ(ONE... | 6.073171 | random seed=20260606 case=4365 rsize=41 input=bbbbabbaaa regex=STAR(STAR(NTIMES(ALT(SEQ(NTIMES(NTIMES(STAR(CH(a)),3),1),SEQ(STAR(STAR(ALT(SEQ(CH(b),CH(b)),ONE))),SEQ(NTIMES(STAR(STAR(CH(a))),3),ALT(SEQ(CH(b),CH(b)),ALT(SEQ(ONE,CH(b)),CH(a)))))),NTIMES(ONE,0)),1))) | 0.040000 | exhaustive case 65596 rsize=5 input= regex=SEQ(ALT(CH(a),CH(a)),ZERO) | seed_20260606.log |

A no entry means the smoke run found no final-active witness above
the configured linear rows, linear member-size, or quadratic pair-budget. This is smoke
evidence for the strong-memo proof route, not an Isabelle proof.
