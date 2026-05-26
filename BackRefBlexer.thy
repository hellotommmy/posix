theory BackRefBlexer
  imports BackRefValues
begin

section \<open>Bitcoded Backreference Pilot\<close>

datatype bbit = BZ | BS | Backbit string

datatype barexp =
  BAZERO
| BAONE "bbit list"
| BACHAR "bbit list" char
| BASEQ "bbit list" barexp barexp
| BAALTs "bbit list" "barexp list"
| BASTAR "bbit list" barexp
| BANTIMES "bbit list" barexp nat
| BABACKREF "bbit list" barexp barexp string
| BAHALF "bbit list" barexp string string
| BARESIDUE "bbit list" string string

abbreviation BAALT :: "bbit list \<Rightarrow> barexp \<Rightarrow> barexp \<Rightarrow> barexp"
where
  "BAALT bs r1 r2 \<equiv> BAALTs bs [r1, r2]"

fun berase :: "barexp \<Rightarrow> brexp"
where
  "berase BAZERO = BZERO"
| "berase (BAONE bs) = BONE"
| "berase (BACHAR bs c) = BCH c"
| "berase (BAALTs bs []) = BZERO"
| "berase (BAALTs bs [r]) = berase r"
| "berase (BAALTs bs (r # rs)) = BALT (berase r) (berase (BAALTs [] rs))"
| "berase (BASEQ bs r1 r2) = BSEQ (berase r1) (berase r2)"
| "berase (BASTAR bs r) = BSTAR (berase r)"
| "berase (BANTIMES bs r n) = BNTIMES (berase r) n"
| "berase (BABACKREF bs r mid cs) = BBACKREF (berase r) (berase mid) cs"
| "berase (BAHALF bs mid cs rep) = BHALF (berase mid) cs rep"
| "berase (BARESIDUE bs cs rep) = BRESIDUE cs rep"

fun bfuse :: "bbit list \<Rightarrow> barexp \<Rightarrow> barexp"
where
  "bfuse bs BAZERO = BAZERO"
| "bfuse bs (BAONE cs) = BAONE (bs @ cs)"
| "bfuse bs (BACHAR cs c) = BACHAR (bs @ cs) c"
| "bfuse bs (BAALTs cs rs) = BAALTs (bs @ cs) rs"
| "bfuse bs (BASEQ cs r1 r2) = BASEQ (bs @ cs) r1 r2"
| "bfuse bs (BASTAR cs r) = BASTAR (bs @ cs) r"
| "bfuse bs (BANTIMES cs r n) = BANTIMES (bs @ cs) r n"
| "bfuse bs (BABACKREF cs r mid req) = BABACKREF (bs @ cs) r mid req"
| "bfuse bs (BAHALF cs mid req rep) = BAHALF (bs @ cs) mid req rep"
| "bfuse bs (BARESIDUE cs req rep) = BARESIDUE (bs @ cs) req rep"

lemma berase_BAALTs_ignore_bits [simp]:
  "berase (BAALTs bs rs) = berase (BAALTs bs' rs)"
proof (induct rs arbitrary: bs bs')
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  then show ?case
    by (cases rs) simp_all
qed

lemma berase_bfuse [simp]:
  "berase (bfuse bs r) = berase r"
  by (induct r arbitrary: bs) simp_all

fun baintern :: "brexp \<Rightarrow> barexp"
where
  "baintern BZERO = BAZERO"
| "baintern BONE = BAONE []"
| "baintern (BCH c) = BACHAR [] c"
| "baintern (BSEQ r1 r2) = BASEQ [] (baintern r1) (baintern r2)"
| "baintern (BALT r1 r2) =
     BAALT [] (bfuse [BZ] (baintern r1)) (bfuse [BS] (baintern r2))"
| "baintern (BSTAR r) = BASTAR [] (baintern r)"
| "baintern (BNTIMES r n) = BANTIMES [] (baintern r) n"
| "baintern (BBACKREF r mid cs) = BABACKREF [] (baintern r) (baintern mid) cs"
| "baintern (BHALF mid cs rep) = BAHALF [] (baintern mid) cs rep"
| "baintern (BRESIDUE cs rep) = BARESIDUE [] cs rep"

lemma berase_baintern [simp]:
  "berase (baintern r) = r"
  by (induct r) simp_all

fun bbnullable :: "barexp \<Rightarrow> bool"
where
  "bbnullable BAZERO = False"
| "bbnullable (BAONE bs) = True"
| "bbnullable (BACHAR bs c) = False"
| "bbnullable (BAALTs bs rs) = (\<exists>r \<in> set rs. bbnullable r)"
| "bbnullable (BASEQ bs r1 r2) = (bbnullable r1 \<and> bbnullable r2)"
| "bbnullable (BASTAR bs r) = True"
| "bbnullable (BANTIMES bs r n) = (if n = 0 then True else bbnullable r)"
| "bbnullable (BABACKREF bs r mid cs) =
     (bbnullable r \<and> bbnullable mid \<and> cs = [])"
| "bbnullable (BAHALF bs mid cs rep) = (bbnullable mid \<and> cs = [])"
| "bbnullable (BARESIDUE bs cs rep) = (cs = [])"

fun bstar_eps_bits :: "nat \<Rightarrow> bbit list \<Rightarrow> bbit list"
where
  "bstar_eps_bits 0 bs = [BS]"
| "bstar_eps_bits (Suc n) bs = BZ # bs @ bstar_eps_bits n bs"

fun bbmkeps :: "barexp \<Rightarrow> bbit list"
where
  "bbmkeps BAZERO = []"
| "bbmkeps (BAONE bs) = bs"
| "bbmkeps (BACHAR bs c) = bs"
| "bbmkeps (BAALTs bs []) = bs"
| "bbmkeps (BAALTs bs (r # rs)) =
     (if bbnullable r then bs @ bbmkeps r else bbmkeps (BAALTs bs rs))"
| "bbmkeps (BASEQ bs r1 r2) = bs @ bbmkeps r1 @ bbmkeps r2"
| "bbmkeps (BASTAR bs r) = bs @ [BS]"
| "bbmkeps (BANTIMES bs r n) = bs @ bstar_eps_bits n (bbmkeps r)"
| "bbmkeps (BABACKREF bs r mid cs) =
     bs @ [Backbit (rev cs)] @ bbmkeps r @ bbmkeps mid"
| "bbmkeps (BAHALF bs mid cs rep) = bs @ bbmkeps mid"
| "bbmkeps (BARESIDUE bs cs rep) = bs"

fun bretrieve_alts :: "bbit list \<Rightarrow> (bval \<Rightarrow> bbit list) list \<Rightarrow> bval \<Rightarrow> bbit list"
where
  "bretrieve_alts bs [] v = bs"
| "bretrieve_alts bs [f] v = bs @ f v"
| "bretrieve_alts bs (f # g # fs) v =
     (case v of
        BLeft v' \<Rightarrow> bs @ f v'
      | BRight v' \<Rightarrow> bretrieve_alts bs (g # fs) v'
      | _ \<Rightarrow> [])"

fun bretrieve_stars :: "bbit list \<Rightarrow> (bval \<Rightarrow> bbit list) \<Rightarrow> bval list \<Rightarrow> bbit list"
where
  "bretrieve_stars bs f [] = bs @ [BS]"
| "bretrieve_stars bs f (v # vs) = bs @ [BZ] @ f v @ bretrieve_stars [] f vs"

primrec bretrieve :: "barexp \<Rightarrow> bval \<Rightarrow> bbit list"
where
  "bretrieve BAZERO v = []"
| "bretrieve (BAONE bs) v =
     (case v of BVoid \<Rightarrow> bs | _ \<Rightarrow> [])"
| "bretrieve (BACHAR bs c) v =
     (case v of BChar d \<Rightarrow> bs | _ \<Rightarrow> [])"
| "bretrieve (BAALTs bs rs) v = bretrieve_alts bs (map bretrieve rs) v"
| "bretrieve (BASEQ bs r1 r2) v =
     (case v of BSeq v1 v2 \<Rightarrow> bs @ bretrieve r1 v1 @ bretrieve r2 v2 | _ \<Rightarrow> [])"
| "bretrieve (BASTAR bs r) v =
     (case v of
        BStars vs \<Rightarrow> bretrieve_stars bs (bretrieve r) vs
      | _ \<Rightarrow> [])"
| "bretrieve (BANTIMES bs r n) v =
     (case v of BStars vs \<Rightarrow> bretrieve_stars bs (bretrieve r) vs | _ \<Rightarrow> [])"
| "bretrieve (BABACKREF bs r mid cs) v =
     (case v of
        BBackref v1 v2 cs' \<Rightarrow> bs @ [Backbit (rev cs @ bflat v1)] @ bretrieve r v1 @ bretrieve mid v2
      | _ \<Rightarrow> [])"
| "bretrieve (BAHALF bs mid cs rep) v =
     (case v of BHalf v' cs' rep' \<Rightarrow> bs @ bretrieve mid v' | _ \<Rightarrow> [])"
| "bretrieve (BARESIDUE bs cs rep) v =
     (case v of BResidue cs' rep' \<Rightarrow> bs | _ \<Rightarrow> [])"

lemma xnullable_berase_BAALTs:
  "xnullable (berase (BAALTs bs rs)) =
    (\<exists>r \<in> set rs. xnullable (berase r))"
proof (induct rs arbitrary: bs)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  show ?case
  proof (cases rs)
    case Nil
    then show ?thesis
      using Cons.prems by simp
  next
    case (Cons r' rs')
    then show ?thesis
      using Cons.prems Cons.hyps by simp
  qed
qed

lemma bbnullable_correctness [simp]:
  "bbnullable r = xnullable (berase r)"
  apply (induct r)
           apply (simp_all add: xnullable_berase_BAALTs)
  done

lemma bretrieve_stars_replicate:
  assumes "bits = f v"
  shows "bretrieve_stars bs f (replicate n v) = bs @ bstar_eps_bits n bits"
  using assms
  by (induct n arbitrary: bs) simp_all

lemma bbmkeps_BAALTs_bretrieve:
  assumes step: "\<And>r. \<lbrakk>r \<in> set rs; bbnullable r\<rbrakk> \<Longrightarrow>
      bbmkeps r = bretrieve r (bmkeps (berase r))"
    and nullable: "\<exists>r \<in> set rs. bbnullable r"
  shows "bbmkeps (BAALTs bs rs) =
    bretrieve_alts bs (map bretrieve rs) (bmkeps (berase (BAALTs bs rs)))"
  using step nullable
proof (induct rs arbitrary: bs)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  then show ?case
  proof (cases rs)
    case Nil
    then show ?thesis
      using Cons.prems by simp
  next
    case (Cons r' rs')
    then show ?thesis
    proof (cases "bbnullable r")
      case True
      then show ?thesis
        using Cons.prems Cons by simp
    next
      case False
      have tail_step: "\<And>x. \<lbrakk>x \<in> set rs; bbnullable x\<rbrakk> \<Longrightarrow>
          bbmkeps x = bretrieve x (bmkeps (berase x))"
        using Cons.prems by auto
      have tail_nullable: "\<exists>x \<in> set rs. bbnullable x"
        using Cons.prems False by auto
      have "bbmkeps (BAALTs bs rs) =
        bretrieve_alts bs (map bretrieve rs) (bmkeps (berase (BAALTs bs rs)))"
        using Cons.hyps[OF tail_step tail_nullable] .
      moreover have "berase (BAALTs bs rs) = berase (BAALTs [] rs)"
        by (rule berase_BAALTs_ignore_bits)
      then have "bmkeps (berase (BAALTs bs rs)) =
        bmkeps (berase (BAALTs [] rs))"
        by (rule arg_cong)
      ultimately have tail: "bbmkeps (BAALTs bs rs) =
        bretrieve_alts bs (map bretrieve rs) (bmkeps (berase (BAALTs [] rs)))"
        by simp
      then show ?thesis
        using Cons False by simp
    qed
  qed
qed

lemma bbmkeps_bretrieve:
  assumes "bbnullable r"
  shows "bbmkeps r = bretrieve r (bmkeps (berase r))"
  using assms
proof (induct r)
  case (BAALTs bs rs)
  have step: "\<And>r. \<lbrakk>r \<in> set rs; bbnullable r\<rbrakk> \<Longrightarrow>
      bbmkeps r = bretrieve r (bmkeps (berase r))"
    using BAALTs.hyps by auto
  have nullable: "\<exists>r \<in> set rs. bbnullable r"
    using BAALTs.prems by (simp add: xnullable_berase_BAALTs)
  then show ?case
    using bbmkeps_BAALTs_bretrieve[OF step nullable, of bs] by simp
next
  case (BABACKREF bs r mid cs)
  have flat_r: "bflat (bmkeps (berase r)) = []"
    using BABACKREF.prems by (auto intro: bmkeps_flat)
  then show ?case
    using BABACKREF by auto
next
  case (BANTIMES bs r n)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    then have r_nullable: "bbnullable r"
      using BANTIMES.prems by simp
    then have "bbmkeps r = bretrieve r (bmkeps (berase r))"
      using BANTIMES.hyps by simp
    then show ?thesis
      using Suc bretrieve_stars_replicate[of "bbmkeps r" "bretrieve r" "bmkeps (berase r)" bs n]
      by simp
  qed
qed (auto simp add: bretrieve_stars_replicate)

lemma bretrieve_stars_append [simp]:
  "bretrieve_stars (bs @ cs) f vs = bs @ bretrieve_stars cs f vs"
  by (cases vs) simp_all

lemma bretrieve_alts_append:
  assumes "\<Turnstile>b v : berase (BAALTs cs rs)"
  shows "bretrieve_alts (bs @ cs) (map bretrieve rs) v =
    bs @ bretrieve_alts cs (map bretrieve rs) v"
  using assms
proof (induct rs arbitrary: bs cs v)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  show ?case
  proof (cases rs)
    case Nil
    then show ?thesis
      by simp
  next
    case (Cons r' rs')
    show ?thesis
    proof (cases v)
      case (BRight v2)
      have prf_tail0: "\<Turnstile>b v2 : berase (BAALTs [] rs)"
        using Cons.prems Cons BRight by (auto elim!: BPrf_elims)
      have same: "berase (BAALTs cs rs) = berase (BAALTs [] rs)"
        by (rule berase_BAALTs_ignore_bits)
      have prf_tail: "\<Turnstile>b v2 : berase (BAALTs cs rs)"
        using prf_tail0 by (simp only: same)
      have "bretrieve_alts (bs @ cs) (map bretrieve rs) v2 =
        bs @ bretrieve_alts cs (map bretrieve rs) v2"
        using Cons.hyps[OF prf_tail] .
      then show ?thesis
        using Cons BRight by simp
    qed (use Cons.prems Cons in \<open>auto elim!: BPrf_elims\<close>)
  qed
qed

lemma bretrieve_bfuse:
  assumes "\<Turnstile>b v : berase r"
  shows "bretrieve (bfuse bs r) v = bs @ bretrieve r v"
  using assms
proof (cases r)
  case BAZERO
  then show ?thesis
    using assms by (auto elim: BPrf_elims)
next
  case (BAONE cs)
  then show ?thesis
    using assms by (auto elim: BPrf_elims)
next
  case (BACHAR cs c)
  then show ?thesis
    using assms by (auto elim: BPrf_elims)
next
  case (BAALTs cs rs)
  then show ?thesis
    using assms bretrieve_alts_append[of v cs rs bs] by simp
next
  case (BASEQ cs r1 r2)
  then show ?thesis
    using assms by (auto elim: BPrf_elims)
next
  case (BASTAR cs r)
  then show ?thesis
    using assms by (auto elim: BPrf_elims)
next
  case (BANTIMES cs r n)
  then show ?thesis
    using assms by (auto elim: BPrf_elims)
next
  case (BABACKREF cs r mid req)
  then show ?thesis
    using assms by (auto elim: BPrf_elims)
next
  case (BAHALF cs mid req rep)
  then show ?thesis
    using assms by (auto elim: BPrf_elims)
next
  case (BARESIDUE cs req rep)
  then show ?thesis
    using assms by (auto elim: BPrf_elims)
qed

fun bbder_residue :: "char \<Rightarrow> bbit list \<Rightarrow> string \<Rightarrow> string \<Rightarrow> barexp"
where
  "bbder_residue c bs [] rep = BAZERO"
| "bbder_residue c bs (d # ds) rep =
     (if c = d then BARESIDUE bs ds rep else BAZERO)"

fun bbder :: "char \<Rightarrow> barexp \<Rightarrow> barexp"
where
  "bbder c BAZERO = BAZERO"
| "bbder c (BAONE bs) = BAZERO"
| "bbder c (BACHAR bs d) = (if c = d then BAONE bs else BAZERO)"
| "bbder c (BAALTs bs rs) = BAALTs bs (map (bbder c) rs)"
| "bbder c (BASEQ bs r1 r2) =
     (if bbnullable r1
      then BAALT bs (BASEQ [] (bbder c r1) r2)
                     (bfuse (bbmkeps r1) (bbder c r2))
      else BASEQ bs (bbder c r1) r2)"
| "bbder c (BASTAR bs r) = BASEQ (bs @ [BZ]) (bbder c r) (BASTAR [] r)"
| "bbder c (BANTIMES bs r n) =
     (if n = 0 then BAZERO else BASEQ (bs @ [BZ]) (bbder c r) (BANTIMES [] r (n - 1)))"
| "bbder c (BABACKREF bs r mid cs) =
     (if bbnullable r
      then BAALT bs
        (BABACKREF [] (bbder c r) mid (c # cs))
        (bfuse [Backbit (rev cs)]
          (if bbnullable mid
           then BAALT (bbmkeps r)
             (BAHALF [] (bbder c mid) (rev cs) (rev cs))
             (bfuse (bbmkeps mid) (bbder_residue c [] (rev cs) (rev cs)))
           else BAHALF (bbmkeps r) (bbder c mid) (rev cs) (rev cs)))
      else BABACKREF bs (bbder c r) mid (c # cs))"
| "bbder c (BAHALF bs mid cs rep) =
     (if bbnullable mid
      then BAALT bs (BAHALF [] (bbder c mid) cs rep)
                    (bfuse (bbmkeps mid) (bbder_residue c [] cs rep))
      else BAHALF bs (bbder c mid) cs rep)"
| "bbder c (BARESIDUE bs cs rep) = bbder_residue c bs cs rep"

lemma berase_bbder_residue [simp]:
  "berase (bbder_residue c bs cs rep) = xder_residue c cs rep"
  by (cases cs) auto

lemma berase_BAALTs_map_bbder:
  assumes "\<And>r. r \<in> set rs \<Longrightarrow> berase (bbder c r) = xder c (berase r)"
  shows "berase (BAALTs bs (map (bbder c) rs)) =
    xder c (berase (BAALTs bs rs))"
  using assms
proof (induct rs arbitrary: bs)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  show ?case
  proof (cases rs)
    case Nil
    then show ?thesis
      using Cons.prems by simp
  next
    case (Cons r' rs')
    then show ?thesis
      using Cons.prems Cons.hyps by simp
  qed
qed

lemma berase_bbder [simp]:
  "berase (bbder c r) = xder c (berase r)"
proof (induct r arbitrary: c)
  case (BAALTs bs rs)
  then show ?case
    by (simp add: berase_BAALTs_map_bbder)
qed simp_all

lemma bbder_residue_bretrieve:
  assumes "\<Turnstile>b v : xder_residue c cs rep"
  shows "bretrieve (bbder_residue c bs cs rep) v =
    bretrieve (BARESIDUE bs cs rep) (binjval (BRESIDUE cs rep) c v)"
  using assms
  by (cases cs) (auto elim: BPrf_elims split: if_splits)

lemma bbder_BAALTs_bretrieve:
  "(\<And>x w. \<lbrakk>x \<in> set rs; BPrf w (xder c (berase x))\<rbrakk> \<Longrightarrow>
      bretrieve (bbder c x) w = bretrieve x (binjval (berase x) c w)) \<Longrightarrow>
   BPrf v (xder c (berase (BAALTs bs rs))) \<Longrightarrow>
   bretrieve (bbder c (BAALTs bs rs)) v =
    bretrieve (BAALTs bs rs) (binjval (berase (BAALTs bs rs)) c v)"
proof (induct rs arbitrary: bs v)
  case Nil
  then show ?case
    by simp
next
  case (Cons r rs)
  show ?case
  proof (cases rs)
    case Nil
    have "bretrieve (bbder c r) v =
      bretrieve r (binjval (berase r) c v)"
      using Cons.prems Nil by simp
    then show ?thesis
      using Nil by simp
  next
    case (Cons r' rs')
    show ?thesis
    proof (cases v)
      case (BLeft v1)
      have prf_left: "BPrf v1 (xder c (berase r))"
        using Cons.prems Cons BLeft by (auto elim!: BPrf_elims)
      have "bretrieve (bbder c r) v1 =
        bretrieve r (binjval (berase r) c v1)"
        using Cons.prems(1)[OF _ prf_left] by simp
      then show ?thesis
        using Cons BLeft by simp
    next
      case (BRight v2)
      have prf_tail0: "BPrf v2 (xder c (berase (BAALTs [] rs)))"
        using Cons.prems Cons BRight by (auto elim!: BPrf_elims)
      have same: "berase (BAALTs bs rs) = berase (BAALTs [] rs)"
        by (rule berase_BAALTs_ignore_bits)
      have prf_tail: "BPrf v2 (xder c (berase (BAALTs bs rs)))"
        using prf_tail0 by (simp only: same)
      have binj_same:
        "binjval (berase (BAALTs bs rs)) c v2 =
         binjval (berase (BAALTs [] rs)) c v2"
        by (simp only: same)
      have step_tail: "\<And>x w. x \<in> set rs \<Longrightarrow> BPrf w (xder c (berase x)) \<Longrightarrow>
          bretrieve (bbder c x) w = bretrieve x (binjval (berase x) c w)"
        using Cons.prems by auto
      have "bretrieve (bbder c (BAALTs bs rs)) v2 =
        bretrieve (BAALTs bs rs) (binjval (berase (BAALTs bs rs)) c v2)"
        using Cons.hyps[OF step_tail prf_tail] .
      then show ?thesis
        using Cons BRight binj_same by simp
    qed (use Cons.prems Cons in \<open>auto elim!: BPrf_elims\<close>)
  qed
qed

lemma bbder_bretrieve:
  assumes "BPrf v (xder c (berase r))"
  shows "bretrieve (bbder c r) v = bretrieve r (binjval (berase r) c v)"
  using assms
proof (induct r arbitrary: c v)
  case (BAALTs bs rs)
  then show ?case
    by (rule bbder_BAALTs_bretrieve)
next
  case (BARESIDUE bs cs rep)
  then show ?case
    using bbder_residue_bretrieve by simp
qed (auto elim!: BPrf_elims
    simp add: bretrieve_bfuse bbmkeps_bretrieve bbder_residue_bretrieve
      binjval_flat bmkeps_flat
    split: if_splits)

fun bbders :: "barexp \<Rightarrow> string \<Rightarrow> barexp"
where
  "bbders r [] = r"
| "bbders r (c # s) = bbders (bbder c r) s"

definition bblexer :: "brexp \<Rightarrow> string \<Rightarrow> bbit list option"
where
  "bblexer r s =
    (let r' = bbders (baintern r) s in
      if bbnullable r' then Some (bbmkeps r') else None)"

lemma berase_bbders [simp]:
  "berase (bbders r s) = xders (berase r) s"
  by (induct s arbitrary: r) simp_all

lemma bblexer_defined_iff:
  "(\<exists>bs. bblexer r s = Some bs) \<longleftrightarrow> s \<in> BL r"
  by (simp add: bblexer_def xnullable_correctness xders_correctness Ders_def)

lemma bbders_bbnullable_blexer:
  assumes "blexer (berase a) s = Some v"
  shows "bbnullable (bbders a s)"
  using assms
proof (induct s arbitrary: a v)
  case Nil
  then show ?case
    by (auto split: if_splits)
next
  case (Cons c s)
  then obtain w where "blexer (xder c (berase a)) s = Some w"
    by (auto split: option.splits)
  then have tail_der: "blexer (berase (bbder c a)) s = Some w"
    by simp
  then have "bbnullable (bbders (bbder c a) s)"
    by (rule Cons.hyps)
  then show ?case
    by simp
qed

lemma bbders_bretrieve_blexer:
  assumes "blexer (berase a) s = Some v"
  shows "bbmkeps (bbders a s) = bretrieve a v"
  using assms
proof (induct s arbitrary: a v)
  case Nil
  then have nullable: "bbnullable a" and v_def: "v = bmkeps (berase a)"
    by (auto split: if_splits)
  show ?case
    using nullable v_def bbmkeps_bretrieve by simp
next
  case (Cons c s)
  then obtain w where tail: "blexer (xder c (berase a)) s = Some w"
    and v_def: "v = binjval (berase a) c w"
    by (auto split: option.splits)
  have tail_der: "blexer (berase (bbder c a)) s = Some w"
    using tail by simp
  have mkeps_tail: "bbmkeps (bbders (bbder c a) s) =
      bretrieve (bbder c a) w"
    using Cons.hyps[OF tail_der] .
  have transport: "bretrieve (bbder c a) w =
      bretrieve a (binjval (berase a) c w)"
    using tail by (intro bbder_bretrieve blexer_BPrf)
  show ?case
    using mkeps_tail transport v_def by simp
qed

lemma bblexer_bretrieve_original:
  assumes "blexer r s = Some v"
  shows "bblexer r s = Some (bretrieve (baintern r) v)"
proof -
  have nullable: "bbnullable (bbders (baintern r) s)"
    using bbders_bbnullable_blexer[of "baintern r" s v] assms by simp
  have bits: "bbmkeps (bbders (baintern r) s) = bretrieve (baintern r) v"
    using bbders_bretrieve_blexer[of "baintern r" s v] assms by simp
  show ?thesis
    using nullable bits by (simp add: bblexer_def Let_def)
qed

theorem bblexer_blexer_retrieve:
  "bblexer r s = map_option (bretrieve (baintern r)) (blexer r s)"
proof (cases "blexer r s")
  case None
  then have "s \<notin> BL r"
    using blexer_correct_None by blast
  then have "\<not> (\<exists>bs. bblexer r s = Some bs)"
    using bblexer_defined_iff by blast
  then have "bblexer r s = None"
    by (cases "bblexer r s") auto
  then show ?thesis
    using None by simp
next
  case (Some v)
  then show ?thesis
    using bblexer_bretrieve_original by simp
qed

lemma bblexer_bretrieve:
  assumes "bblexer r s = Some bs"
  shows "bs = bretrieve (bbders (baintern r) s) (bmkeps (xders r s))"
proof -
  let ?a = "bbders (baintern r) s"
  from assms have bs: "bs = bbmkeps ?a" and nullable: "bbnullable ?a"
    by (auto simp add: bblexer_def Let_def split: if_splits)
  from nullable have "bbmkeps ?a = bretrieve ?a (bmkeps (berase ?a))"
    by (rule bbmkeps_bretrieve)
  then show ?thesis
    using bs by simp
qed

theorem bblexer_retrieve_correctness:
  assumes "bblexer r s = Some bs"
  shows "bs = bretrieve (bbders (baintern r) s) (bmkeps (xders r s))"
    and "\<Turnstile>b bmkeps (xders r s) : xders r s"
    and "bflat (bmkeps (xders r s)) = []"
proof -
  let ?a = "bbders (baintern r) s"
  from assms have nullable: "bbnullable ?a"
    by (auto simp add: bblexer_def Let_def split: if_splits)
  then have xnullable: "xnullable (xders r s)"
    by simp
  show "bs = bretrieve ?a (bmkeps (xders r s))"
    using assms by (rule bblexer_bretrieve)
  show "\<Turnstile>b bmkeps (xders r s) : xders r s"
    using xnullable by (rule bmkeps_BPrf)
  show "bflat (bmkeps (xders r s)) = []"
    using xnullable by (rule bmkeps_flat)
qed

theorem bblexer_final_retrieve:
  "bblexer r s =
    (if xnullable (xders r s)
     then Some (bretrieve (bbders (baintern r) s) (bmkeps (xders r s)))
     else None)"
proof (cases "xnullable (xders r s)")
  case True
  let ?a = "bbders (baintern r) s"
  have nullable: "bbnullable ?a"
    using True by simp
  have bits: "bbmkeps ?a = bretrieve ?a (bmkeps (xders r s))"
    using nullable bbmkeps_bretrieve[of ?a] by simp
  show ?thesis
    using True bits by (simp add: bblexer_def Let_def)
next
  case False
  then show ?thesis
    by (simp add: bblexer_def Let_def)
qed

theorem bblexer_final_membership:
  "bblexer r s =
    (if s \<in> BL r
     then Some (bretrieve (bbders (baintern r) s) (bmkeps (xders r s)))
     else None)"
  by (simp add: bblexer_final_retrieve xnullable_correctness
      xders_correctness Ders_def)

lemma bblexer_None_iff:
  "bblexer r s = None \<longleftrightarrow> s \<notin> BL r"
  by (simp add: bblexer_final_membership)

lemma bblexer_Some_iff:
  "bblexer r s = Some bs \<longleftrightarrow>
    s \<in> BL r \<and>
    bs = bretrieve (bbders (baintern r) s) (bmkeps (xders r s))"
  by (auto simp add: bblexer_final_membership split: if_splits)

lemma bblexer_Some_blexer_iff:
  "bblexer r s = Some bs \<longleftrightarrow>
    (\<exists>v. blexer r s = Some v \<and> bs = bretrieve (baintern r) v)"
  by (cases "blexer r s") (auto simp add: bblexer_blexer_retrieve)

lemma bblexer_None_blexer_iff:
  "bblexer r s = None \<longleftrightarrow> blexer r s = None"
  by (cases "blexer r s") (simp_all add: bblexer_blexer_retrieve)

theorem bblexer_POSIX_retrieve_iff:
  "bblexer r s = Some bs \<longleftrightarrow>
    (\<exists>v. s \<in> r \<rightarrow> v \<and> bs = bretrieve (baintern r) v)"
proof
  assume "bblexer r s = Some bs"
  then obtain v where ble: "blexer r s = Some v"
    and bs: "bs = bretrieve (baintern r) v"
    by (cases "blexer r s") (auto simp add: bblexer_blexer_retrieve)
  from ble have "s \<in> r \<rightarrow> v"
    by (rule blexer_POSIX)
  with bs show "\<exists>v. s \<in> r \<rightarrow> v \<and> bs = bretrieve (baintern r) v"
    by blast
next
  assume "\<exists>v. s \<in> r \<rightarrow> v \<and> bs = bretrieve (baintern r) v"
  then obtain v where pos: "s \<in> r \<rightarrow> v"
    and bs: "bs = bretrieve (baintern r) v"
    by blast
  from pos have "s \<in> BL r"
    by (rule BPosix1(1))
  then have "blexer r s \<noteq> None"
    using blexer_correct_None by blast
  then obtain w where ble: "blexer r s = Some w"
    by (cases "blexer r s") auto
  then have pos_w: "s \<in> r \<rightarrow> w"
    by (rule blexer_POSIX)
  have "w = v"
    using pos_w pos by (rule BPosix_determ)
  then show "bblexer r s = Some bs"
    using ble bs by (simp add: bblexer_blexer_retrieve)
qed

theorem bblexer_POSIX_retrieve:
  assumes "s \<in> r \<rightarrow> v"
  shows "bblexer r s = Some (bretrieve (baintern r) v)"
  using assms by (auto simp add: bblexer_POSIX_retrieve_iff)

lemma bblexer_POSIX_retrieve_eq:
  assumes "bblexer r s = Some bs"
    and "s \<in> r \<rightarrow> v"
  shows "bs = bretrieve (baintern r) v"
  using assms(1) bblexer_POSIX_retrieve[OF assms(2)] by simp

section \<open>Bitcoded Backreference Simplification\<close>

fun bbsimp :: "barexp \<Rightarrow> barexp"
where
  "bbsimp BAZERO = BAZERO"
| "bbsimp (BAONE bs) = BAONE bs"
| "bbsimp (BACHAR bs c) = BACHAR bs c"
| "bbsimp (BAALTs bs []) = BAZERO"
| "bbsimp (BAALTs bs [r]) = bfuse bs (bbsimp r)"
| "bbsimp (BAALTs bs (r1 # r2 # rs)) = BAALTs bs (r1 # r2 # rs)"
| "bbsimp (BASEQ bs r1 r2) = BASEQ bs (bbsimp r1) (bbsimp r2)"
| "bbsimp (BASTAR bs r) = BASTAR bs (bbsimp r)"
| "bbsimp (BANTIMES bs r n) = BANTIMES bs (bbsimp r) n"
| "bbsimp (BABACKREF bs r mid cs) =
     BABACKREF bs (bbsimp r) (bbsimp mid) cs"
| "bbsimp (BAHALF bs mid cs rep) = BAHALF bs (bbsimp mid) cs rep"
| "bbsimp (BARESIDUE bs cs rep) = BARESIDUE bs cs rep"

lemma bfuse_append [simp]:
  "bfuse (bs1 @ bs2) r = bfuse bs1 (bfuse bs2 r)"
  by (cases r) (simp_all add: append_assoc)

lemma berase_bbsimp [simp]:
  "berase (bbsimp r) = berase r"
proof (induct r)
  case (BAALTs bs rs)
  show ?case
  proof (cases rs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons r rs')
    note outer = Cons
    show ?thesis
    proof (cases rs')
      case Nil
      then show ?thesis
        using BAALTs.hyps outer by simp
    next
      case inner: (Cons r' rs'')
      then show ?thesis
        using outer by simp
    qed
  qed
qed simp_all

lemma bbnullable_bbsimp [simp]:
  "bbnullable (bbsimp r) = bbnullable r"
  by (simp add: bbnullable_correctness)

lemma bbsimp_bfuse [simp]:
  "bbsimp (bfuse bs r) = bfuse bs (bbsimp r)"
proof (cases r)
  case (BAALTs cs rs)
  then show ?thesis
  proof (cases rs)
    case Nil
    then show ?thesis
      using BAALTs by simp
  next
    case (Cons r rs')
    then show ?thesis
      using BAALTs by (cases rs') (simp_all add: append_assoc)
  qed
qed (simp_all add: append_assoc)

lemma bretrieve_stars_bbsimp:
  assumes "\<And>v. v \<in> set vs \<Longrightarrow> bretrieve (bbsimp r) v = bretrieve r v"
  shows "bretrieve_stars bs (bretrieve (bbsimp r)) vs =
    bretrieve_stars bs (bretrieve r) vs"
  using assms
  by (induct vs arbitrary: bs) simp_all

lemma bretrieve_bbsimp:
  assumes "BPrf v (berase r)"
  shows "bretrieve (bbsimp r) v = bretrieve r v"
  using assms
proof (induct r arbitrary: v)
  case (BAALTs bs rs)
  show ?case
  proof (cases rs)
    case Nil
    then show ?thesis
      using BAALTs.prems by (auto elim: BPrf_elims)
  next
    case (Cons r rs')
    note outer = Cons
    show ?thesis
    proof (cases rs')
      case Nil
      have prf_r: "BPrf v (berase r)"
        using BAALTs.prems outer Nil by simp
      have "bretrieve (bfuse bs (bbsimp r)) v =
        bs @ bretrieve (bbsimp r) v"
        using prf_r by (simp add: bretrieve_bfuse)
      also have "... = bs @ bretrieve r v"
        using BAALTs.hyps prf_r outer Nil by simp
      finally have "bretrieve (bfuse bs (bbsimp r)) v =
        bs @ bretrieve r v" .
      then show ?thesis
        using outer Nil by simp
    next
      case inner: (Cons r' rs'')
      then show ?thesis
        using outer by simp
    qed
  qed
next
  case (BASTAR bs r)
  show ?case
  proof (cases v)
    case (BStars vs)
    have step: "\<And>w. w \<in> set vs \<Longrightarrow>
        bretrieve (bbsimp r) w = bretrieve r w"
      using BASTAR BStars by (auto elim!: BPrf_elims)
    then show ?thesis
      using BStars bretrieve_stars_bbsimp by simp
  qed (use BASTAR.prems in \<open>auto elim!: BPrf_elims\<close>)
next
  case (BANTIMES bs r n)
  show ?case
  proof (cases v)
    case (BStars vs)
    have step: "\<And>w. w \<in> set vs \<Longrightarrow>
        bretrieve (bbsimp r) w = bretrieve r w"
      using BANTIMES BStars by (auto elim!: BPrf_elims)
    then show ?thesis
      using BStars bretrieve_stars_bbsimp by simp
  qed (use BANTIMES.prems in \<open>auto elim!: BPrf_elims\<close>)
qed (auto elim!: BPrf_elims)

lemma bbmkeps_bbsimp:
  assumes "bbnullable r"
  shows "bbmkeps (bbsimp r) = bbmkeps r"
proof -
  have nullable_simp: "bbnullable (bbsimp r)"
    using assms by simp
  have "bbmkeps (bbsimp r) =
      bretrieve (bbsimp r) (bmkeps (berase (bbsimp r)))"
    using nullable_simp by (rule bbmkeps_bretrieve)
  also have "... = bretrieve (bbsimp r) (bmkeps (berase r))"
    by simp
  also have "... = bretrieve r (bmkeps (berase r))"
    using assms by (intro bretrieve_bbsimp bmkeps_BPrf)
      (simp add: bbnullable_correctness)
  also have "... = bbmkeps r"
    using assms bbmkeps_bretrieve by simp
  finally show ?thesis .
qed

fun bbders_simp :: "barexp \<Rightarrow> string \<Rightarrow> barexp"
where
  "bbders_simp r [] = bbsimp r"
| "bbders_simp r (c # s) = bbders_simp (bbsimp (bbder c r)) s"

lemma berase_bbders_simp [simp]:
  "berase (bbders_simp r s) = xders (berase r) s"
  by (induct s arbitrary: r) simp_all

lemma bbnullable_bbders_simp [simp]:
  "bbnullable (bbders_simp r s) = bbnullable (bbders r s)"
  by (simp add: bbnullable_correctness)

lemma bbders_simp_bbnullable_blexer:
  assumes "blexer (berase a) s = Some v"
  shows "bbnullable (bbders_simp a s)"
  using assms bbders_bbnullable_blexer[of a s v] by simp

lemma bbders_simp_bretrieve_blexer:
  assumes "blexer (berase a) s = Some v"
  shows "bbmkeps (bbders_simp a s) = bretrieve a v"
  using assms
proof (induct s arbitrary: a v)
  case Nil
  then have nullable: "bbnullable a" and v_def: "v = bmkeps (berase a)"
    by (auto split: if_splits)
  have "bbmkeps (bbders_simp a []) = bbmkeps (bbsimp a)"
    by simp
  also have "... = bbmkeps a"
    using nullable by (rule bbmkeps_bbsimp)
  also have "... = bretrieve a (bmkeps (berase a))"
    using nullable bbmkeps_bretrieve by simp
  finally show ?case
    using v_def by simp
next
  case (Cons c s)
  then obtain w where tail: "blexer (xder c (berase a)) s = Some w"
    and v_def: "v = binjval (berase a) c w"
    by (auto split: option.splits)
  have tail_simp: "blexer (berase (bbsimp (bbder c a))) s = Some w"
    using tail by simp
  have mkeps_tail:
    "bbmkeps (bbders_simp (bbsimp (bbder c a)) s) =
      bretrieve (bbsimp (bbder c a)) w"
    using Cons.hyps[OF tail_simp] .
  have prf_w: "BPrf w (berase (bbder c a))"
    using tail by (simp add: blexer_BPrf)
  have retrieve_simp:
    "bretrieve (bbsimp (bbder c a)) w = bretrieve (bbder c a) w"
    using prf_w by (rule bretrieve_bbsimp)
  have transport:
    "bretrieve (bbder c a) w = bretrieve a (binjval (berase a) c w)"
    using tail by (intro bbder_bretrieve blexer_BPrf)
  show ?case
    using mkeps_tail retrieve_simp transport v_def by simp
qed

definition bblexer_simp :: "brexp \<Rightarrow> string \<Rightarrow> bbit list option"
where
  "bblexer_simp r s =
    (let r' = bbsimp (bbders (baintern r) s) in
      if bbnullable r' then Some (bbmkeps r') else None)"

theorem bblexer_simp_correctness:
  "bblexer_simp r s = bblexer r s"
proof -
  show ?thesis
  proof (cases "bbnullable (bbders (baintern r) s)")
    case True
    then have "bbmkeps (bbsimp (bbders (baintern r) s)) =
        bbmkeps (bbders (baintern r) s)"
      by (rule bbmkeps_bbsimp)
    then show ?thesis
      using True by (simp add: bblexer_simp_def bblexer_def Let_def)
  next
    case False
    then show ?thesis
      by (simp add: bblexer_simp_def bblexer_def Let_def)
  qed
qed

lemma bblexer_simp_defined_iff:
  "(\<exists>bs. bblexer_simp r s = Some bs) \<longleftrightarrow> s \<in> BL r"
  by (simp add: bblexer_simp_correctness bblexer_defined_iff)

theorem bblexer_simp_blexer_retrieve:
  "bblexer_simp r s = map_option (bretrieve (baintern r)) (blexer r s)"
  by (simp add: bblexer_simp_correctness bblexer_blexer_retrieve)

theorem bblexer_simp_retrieve_correctness:
  assumes "bblexer_simp r s = Some bs"
  shows "bs = bretrieve (bbsimp (bbders (baintern r) s)) (bmkeps (xders r s))"
    and "\<Turnstile>b bmkeps (xders r s) : xders r s"
    and "bflat (bmkeps (xders r s)) = []"
proof -
  let ?a = "bbsimp (bbders (baintern r) s)"
  from assms have bs: "bs = bbmkeps ?a" and nullable: "bbnullable ?a"
    by (auto simp add: bblexer_simp_def Let_def split: if_splits)
  then have xnullable: "xnullable (xders r s)"
    by simp
  from nullable have "bbmkeps ?a = bretrieve ?a (bmkeps (berase ?a))"
    by (rule bbmkeps_bretrieve)
  then show "bs = bretrieve ?a (bmkeps (xders r s))"
    using bs by simp
  show "\<Turnstile>b bmkeps (xders r s) : xders r s"
    using xnullable by (rule bmkeps_BPrf)
  show "bflat (bmkeps (xders r s)) = []"
    using xnullable by (rule bmkeps_flat)
qed

theorem bblexer_simp_final_retrieve:
  "bblexer_simp r s =
    (if xnullable (xders r s)
     then Some (bretrieve (bbsimp (bbders (baintern r) s)) (bmkeps (xders r s)))
     else None)"
proof (cases "xnullable (xders r s)")
  case True
  let ?a = "bbsimp (bbders (baintern r) s)"
  have nullable: "bbnullable ?a"
    using True by simp
  have bits: "bbmkeps ?a = bretrieve ?a (bmkeps (xders r s))"
    using nullable bbmkeps_bretrieve[of ?a] by simp
  show ?thesis
    using True bits by (simp add: bblexer_simp_def Let_def)
next
  case False
  then show ?thesis
    by (simp add: bblexer_simp_def Let_def)
qed

theorem bblexer_simp_final_membership:
  "bblexer_simp r s =
    (if s \<in> BL r
     then Some (bretrieve (bbsimp (bbders (baintern r) s)) (bmkeps (xders r s)))
     else None)"
  by (simp add: bblexer_simp_final_retrieve xnullable_correctness
      xders_correctness Ders_def)

lemma bblexer_simp_None_iff:
  "bblexer_simp r s = None \<longleftrightarrow> s \<notin> BL r"
  by (simp add: bblexer_simp_final_membership)

lemma bblexer_simp_Some_iff:
  "bblexer_simp r s = Some bs \<longleftrightarrow>
    s \<in> BL r \<and>
    bs = bretrieve (bbsimp (bbders (baintern r) s)) (bmkeps (xders r s))"
  by (auto simp add: bblexer_simp_final_membership split: if_splits)

lemma bblexer_simp_Some_blexer_iff:
  "bblexer_simp r s = Some bs \<longleftrightarrow>
    (\<exists>v. blexer r s = Some v \<and> bs = bretrieve (baintern r) v)"
  by (cases "blexer r s") (auto simp add: bblexer_simp_blexer_retrieve)

lemma bblexer_simp_None_blexer_iff:
  "bblexer_simp r s = None \<longleftrightarrow> blexer r s = None"
  by (simp add: bblexer_simp_correctness bblexer_None_blexer_iff)

theorem bblexer_simp_POSIX_retrieve_iff:
  "bblexer_simp r s = Some bs \<longleftrightarrow>
    (\<exists>v. s \<in> r \<rightarrow> v \<and> bs = bretrieve (baintern r) v)"
  by (simp add: bblexer_simp_correctness bblexer_POSIX_retrieve_iff)

theorem bblexer_simp_POSIX_retrieve:
  assumes "s \<in> r \<rightarrow> v"
  shows "bblexer_simp r s = Some (bretrieve (baintern r) v)"
  using assms by (auto simp add: bblexer_simp_POSIX_retrieve_iff)

lemma bblexer_simp_POSIX_retrieve_eq:
  assumes "bblexer_simp r s = Some bs"
    and "s \<in> r \<rightarrow> v"
  shows "bs = bretrieve (baintern r) v"
  using assms(1) bblexer_simp_POSIX_retrieve[OF assms(2)] by simp

definition bblexer_step_simp :: "brexp \<Rightarrow> string \<Rightarrow> bbit list option"
where
  "bblexer_step_simp r s =
    (let r' = bbders_simp (baintern r) s in
      if bbnullable r' then Some (bbmkeps r') else None)"

lemma bblexer_step_simp_defined_iff:
  "(\<exists>bs. bblexer_step_simp r s = Some bs) \<longleftrightarrow> s \<in> BL r"
  by (simp add: bblexer_step_simp_def xnullable_correctness
      xders_correctness Ders_def)

theorem bblexer_step_simp_correctness:
  "bblexer_step_simp r s = bblexer r s"
proof (cases "blexer r s")
  case None
  then have "s \<notin> BL r"
    using blexer_correct_None by blast
  then have "\<not> (\<exists>bs. bblexer_step_simp r s = Some bs)"
    using bblexer_step_simp_defined_iff by blast
  then have step_none: "bblexer_step_simp r s = None"
    by (cases "bblexer_step_simp r s") auto
  moreover have "bblexer r s = None"
    using None bblexer_blexer_retrieve by simp
  ultimately show ?thesis
    by simp
next
  case (Some v)
  have nullable: "bbnullable (bbders_simp (baintern r) s)"
    using Some bbders_simp_bbnullable_blexer[of "baintern r" s v] by simp
  have bits:
    "bbmkeps (bbders_simp (baintern r) s) = bretrieve (baintern r) v"
    using Some bbders_simp_bretrieve_blexer[of "baintern r" s v] by simp
  have step: "bblexer_step_simp r s = Some (bretrieve (baintern r) v)"
    using nullable bits by (simp add: bblexer_step_simp_def Let_def)
  have original: "bblexer r s = Some (bretrieve (baintern r) v)"
    using Some bblexer_blexer_retrieve by simp
  show ?thesis
    using step original by simp
qed

theorem bblexer_step_simp_retrieve_correctness:
  assumes "bblexer_step_simp r s = Some bs"
  shows "bs = bretrieve (bbders_simp (baintern r) s) (bmkeps (xders r s))"
    and "\<Turnstile>b bmkeps (xders r s) : xders r s"
    and "bflat (bmkeps (xders r s)) = []"
proof -
  let ?a = "bbders_simp (baintern r) s"
  from assms have bs: "bs = bbmkeps ?a" and nullable: "bbnullable ?a"
    by (auto simp add: bblexer_step_simp_def Let_def split: if_splits)
  then have xnullable: "xnullable (xders r s)"
    by simp
  from nullable have "bbmkeps ?a = bretrieve ?a (bmkeps (berase ?a))"
    by (rule bbmkeps_bretrieve)
  then show "bs = bretrieve ?a (bmkeps (xders r s))"
    using bs by simp
  show "\<Turnstile>b bmkeps (xders r s) : xders r s"
    using xnullable by (rule bmkeps_BPrf)
  show "bflat (bmkeps (xders r s)) = []"
    using xnullable by (rule bmkeps_flat)
qed

theorem bblexer_step_simp_final_retrieve:
  "bblexer_step_simp r s =
    (if xnullable (xders r s)
     then Some (bretrieve (bbders_simp (baintern r) s) (bmkeps (xders r s)))
     else None)"
proof (cases "xnullable (xders r s)")
  case True
  let ?a = "bbders_simp (baintern r) s"
  have nullable: "bbnullable ?a"
    using True by simp
  have bits: "bbmkeps ?a = bretrieve ?a (bmkeps (xders r s))"
    using nullable bbmkeps_bretrieve[of ?a] by simp
  show ?thesis
    using True bits by (simp add: bblexer_step_simp_def Let_def)
next
  case False
  then show ?thesis
    by (simp add: bblexer_step_simp_def Let_def)
qed

theorem bblexer_step_simp_final_membership:
  "bblexer_step_simp r s =
    (if s \<in> BL r
     then Some (bretrieve (bbders_simp (baintern r) s) (bmkeps (xders r s)))
     else None)"
  by (simp add: bblexer_step_simp_final_retrieve xnullable_correctness
      xders_correctness Ders_def)

lemma bblexer_step_simp_None_iff:
  "bblexer_step_simp r s = None \<longleftrightarrow> s \<notin> BL r"
  by (simp add: bblexer_step_simp_final_membership)

lemma bblexer_step_simp_Some_iff:
  "bblexer_step_simp r s = Some bs \<longleftrightarrow>
    s \<in> BL r \<and>
    bs = bretrieve (bbders_simp (baintern r) s) (bmkeps (xders r s))"
  by (auto simp add: bblexer_step_simp_final_membership split: if_splits)

lemma bblexer_step_simp_Some_blexer_iff:
  "bblexer_step_simp r s = Some bs \<longleftrightarrow>
    (\<exists>v. blexer r s = Some v \<and> bs = bretrieve (baintern r) v)"
  by (cases "blexer r s")
    (auto simp add: bblexer_step_simp_correctness bblexer_blexer_retrieve)

lemma bblexer_step_simp_None_blexer_iff:
  "bblexer_step_simp r s = None \<longleftrightarrow> blexer r s = None"
  by (simp add: bblexer_step_simp_correctness bblexer_None_blexer_iff)

theorem bblexer_step_simp_POSIX_retrieve_iff:
  "bblexer_step_simp r s = Some bs \<longleftrightarrow>
    (\<exists>v. s \<in> r \<rightarrow> v \<and> bs = bretrieve (baintern r) v)"
  by (simp add: bblexer_step_simp_correctness bblexer_POSIX_retrieve_iff)

theorem bblexer_step_simp_POSIX_retrieve:
  assumes "s \<in> r \<rightarrow> v"
  shows "bblexer_step_simp r s = Some (bretrieve (baintern r) v)"
  using assms by (auto simp add: bblexer_step_simp_POSIX_retrieve_iff)

lemma bblexer_step_simp_POSIX_retrieve_eq:
  assumes "bblexer_step_simp r s = Some bs"
    and "s \<in> r \<rightarrow> v"
  shows "bs = bretrieve (baintern r) v"
  using assms(1) bblexer_step_simp_POSIX_retrieve[OF assms(2)] by simp

theorem bblexer_step_simp_blexer_retrieve:
  "bblexer_step_simp r s = map_option (bretrieve (baintern r)) (blexer r s)"
  by (simp add: bblexer_step_simp_correctness bblexer_blexer_retrieve)

theorem bblexer_simp_step_simp_eq:
  "bblexer_simp r s = bblexer_step_simp r s"
  by (simp add: bblexer_simp_correctness bblexer_step_simp_correctness)

end
