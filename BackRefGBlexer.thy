theory BackRefGBlexer
  imports BackRefLang4Values BackRefBlexer
begin

section \<open>Bitcoded Generalized Backreference Pilot\<close>

datatype gabexp =
  GABASE "bbit list" barexp
| GAALTs "bbit list" "gabexp list"
| GABACKREF4 "bbit list" barexp barexp barexp barexp string

abbreviation GAALT :: "bbit list \<Rightarrow> gabexp \<Rightarrow> gabexp \<Rightarrow> gabexp"
where
  "GAALT bs r1 r2 \<equiv> GAALTs bs [r1, r2]"

fun gerase :: "gabexp \<Rightarrow> gbrexp"
where
  "gerase (GABASE bs r) = GBASE (berase r)"
| "gerase (GAALTs bs []) = GBASE BZERO"
| "gerase (GAALTs bs [r]) = gerase r"
| "gerase (GAALTs bs (r # rs)) = GALT (gerase r) (gerase (GAALTs [] rs))"
| "gerase (GABACKREF4 bs r1 r2 r3 r4 cs) =
    GBACKREF4 (berase r1) (berase r2) (berase r3) (berase r4) cs"

fun gfuse :: "bbit list \<Rightarrow> gabexp \<Rightarrow> gabexp"
where
  "gfuse bs (GABASE cs r) = GABASE (bs @ cs) r"
| "gfuse bs (GAALTs cs rs) = GAALTs (bs @ cs) rs"
| "gfuse bs (GABACKREF4 cs r1 r2 r3 r4 req) =
    GABACKREF4 (bs @ cs) r1 r2 r3 r4 req"

lemma gerase_GAALTs_ignore_bits [simp]:
  "gerase (GAALTs bs rs) = gerase (GAALTs bs' rs)"
proof (induct rs arbitrary: bs bs')
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  then show ?case
    by (cases rs) simp_all
qed

lemma gerase_gfuse [simp]:
  "gerase (gfuse bs r) = gerase r"
  by (cases r) simp_all

fun gaintern :: "gbrexp \<Rightarrow> gabexp"
where
  "gaintern (GBASE r) = GABASE [] (baintern r)"
| "gaintern (GALT r1 r2) =
    GAALT [] (gfuse [BZ] (gaintern r1)) (gfuse [BS] (gaintern r2))"
| "gaintern (GBACKREF4 r1 r2 r3 r4 cs) =
    GABACKREF4 [] (baintern r1) (baintern r2) (baintern r3) (baintern r4) cs"

lemma gerase_gaintern [simp]:
  "gerase (gaintern r) = r"
  by (induct r) simp_all

fun gabnullable :: "gabexp \<Rightarrow> bool"
where
  "gabnullable (GABASE bs r) = bbnullable r"
| "gabnullable (GAALTs bs rs) = (\<exists>r \<in> set rs. gabnullable r)"
| "gabnullable (GABACKREF4 bs r1 r2 r3 r4 cs) =
    (bbnullable r1 \<and> bbnullable r2 \<and> bbnullable r3 \<and> bbnullable r4 \<and> cs = [])"

lemma gnullable_gerase_GAALTs:
  "gnullable (gerase (GAALTs bs rs)) =
    (\<exists>r \<in> set rs. gnullable (gerase r))"
proof (induct rs arbitrary: bs)
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
    then show ?thesis
      using Cons.hyps by simp
  qed
qed

lemma gabnullable_correctness [simp]:
  "gabnullable r = gnullable (gerase r)"
proof (induct r)
  case (GAALTs bs rs)
  then show ?case
    by (simp add: gnullable_gerase_GAALTs)
qed simp_all

fun gamkeps :: "gabexp \<Rightarrow> bbit list"
where
  "gamkeps (GABASE bs r) = bs @ bbmkeps r"
| "gamkeps (GAALTs bs []) = bs"
| "gamkeps (GAALTs bs (r # rs)) =
    (if gabnullable r then bs @ gamkeps r else gamkeps (GAALTs bs rs))"
| "gamkeps (GABACKREF4 bs r1 r2 r3 r4 cs) =
    bs @ bbmkeps r1 @ [Backbit (rev cs)] @ bbmkeps r2 @ bbmkeps r3 @ bbmkeps r4"

fun gretrieve_alts ::
  "bbit list \<Rightarrow> (gbval \<Rightarrow> bbit list) list \<Rightarrow> gbval \<Rightarrow> bbit list"
where
  "gretrieve_alts bs [] v = bs"
| "gretrieve_alts bs [f] v = bs @ f v"
| "gretrieve_alts bs (f # g # fs) v =
    (case v of
       GVLeft v' \<Rightarrow> bs @ f v'
     | GVRight v' \<Rightarrow> gretrieve_alts bs (g # fs) v'
     | _ \<Rightarrow> [])"

primrec gretrieve :: "gabexp \<Rightarrow> gbval \<Rightarrow> bbit list"
where
  "gretrieve (GABASE bs r) v =
    (case v of GVBase v' \<Rightarrow> bs @ bretrieve r v' | _ \<Rightarrow> [])"
| "gretrieve (GAALTs bs rs) v = gretrieve_alts bs (map gretrieve rs) v"
| "gretrieve (GABACKREF4 bs r1 r2 r3 r4 cs) v =
    (case v of
       GVBackref4 (BBackref4 v1 v2 v3 v4 cs') \<Rightarrow>
         bs @ bretrieve r1 v1 @ [Backbit (rev cs @ bflat v2)] @
           bretrieve r2 v2 @ bretrieve r3 v3 @ bretrieve r4 v4
     | _ \<Rightarrow> [])"

lemma gamkeps_GAALTs_gretrieve:
  assumes step: "\<And>r. \<lbrakk>r \<in> set rs; gabnullable r\<rbrakk> \<Longrightarrow>
      gamkeps r = gretrieve r (gmkeps (gerase r))"
    and nullable: "\<exists>r \<in> set rs. gabnullable r"
  shows "gamkeps (GAALTs bs rs) =
    gretrieve_alts bs (map gretrieve rs) (gmkeps (gerase (GAALTs bs rs)))"
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
    proof (cases "gabnullable r")
      case True
      then show ?thesis
        using Cons.prems Cons by simp
    next
      case False
      have tail_step: "\<And>x. \<lbrakk>x \<in> set rs; gabnullable x\<rbrakk> \<Longrightarrow>
          gamkeps x = gretrieve x (gmkeps (gerase x))"
        using Cons.prems by auto
      have tail_nullable: "\<exists>x \<in> set rs. gabnullable x"
        using Cons.prems False by auto
      have "gamkeps (GAALTs bs rs) =
        gretrieve_alts bs (map gretrieve rs) (gmkeps (gerase (GAALTs bs rs)))"
        using Cons.hyps[OF tail_step tail_nullable] .
      moreover have "gerase (GAALTs bs rs) = gerase (GAALTs [] rs)"
        by (rule gerase_GAALTs_ignore_bits)
      then have "gmkeps (gerase (GAALTs bs rs)) =
        gmkeps (gerase (GAALTs [] rs))"
        by (rule arg_cong)
      ultimately show ?thesis
        using Cons False by simp
    qed
  qed
qed

lemma gamkeps_gretrieve:
  assumes "gabnullable r"
  shows "gamkeps r = gretrieve r (gmkeps (gerase r))"
  using assms
proof (induct r)
  case (GABASE bs r)
  then show ?case
    using bbmkeps_bretrieve by simp
next
  case (GAALTs bs rs)
  have step: "\<And>r. \<lbrakk>r \<in> set rs; gabnullable r\<rbrakk> \<Longrightarrow>
      gamkeps r = gretrieve r (gmkeps (gerase r))"
    using GAALTs.hyps by auto
  have nullable: "\<exists>r \<in> set rs. gabnullable r"
    using GAALTs.prems by (simp add: gnullable_gerase_GAALTs)
  then show ?case
    using gamkeps_GAALTs_gretrieve[OF step nullable, of bs] by simp
next
  case (GABACKREF4 bs r1 r2 r3 r4 cs)
  have r1: "bbmkeps r1 = bretrieve r1 (bmkeps (berase r1))"
    using GABACKREF4.prems by (auto intro: bbmkeps_bretrieve)
  have r2: "bbmkeps r2 = bretrieve r2 (bmkeps (berase r2))"
    using GABACKREF4.prems by (auto intro: bbmkeps_bretrieve)
  have r3: "bbmkeps r3 = bretrieve r3 (bmkeps (berase r3))"
    using GABACKREF4.prems by (auto intro: bbmkeps_bretrieve)
  have r4: "bbmkeps r4 = bretrieve r4 (bmkeps (berase r4))"
    using GABACKREF4.prems by (auto intro: bbmkeps_bretrieve)
  have flat2: "bflat (bmkeps (berase r2)) = []"
    using GABACKREF4.prems by (auto intro: bmkeps_flat)
  show ?case
    using GABACKREF4.prems r1 r2 r3 r4 flat2 by simp
qed

definition gabbtail4 :: "barexp \<Rightarrow> string \<Rightarrow> barexp \<Rightarrow> barexp"
where
  "gabbtail4 r cs tail = BASEQ [] r (BASEQ [] (BARESIDUE [] cs cs) tail)"

lemma berase_gabbtail4 [simp]:
  "berase (gabbtail4 r cs tail) = gtail4 (berase r) cs (berase tail)"
  by (simp add: gabbtail4_def gtail4_def)

fun gabder :: "char \<Rightarrow> gabexp \<Rightarrow> gabexp"
where
  "gabder c (GABASE bs r) = GABASE bs (bbder c r)"
| "gabder c (GAALTs bs rs) = GAALTs bs (map (gabder c) rs)"
| "gabder c (GABACKREF4 bs r1 r2 r3 r4 cs) =
    (let prefix = GABACKREF4 [] (bbder c r1) r2 r3 r4 cs;
         capture = gfuse (bbmkeps r1)
           (GABACKREF4 [] (BAONE []) (bbder c r2) r3 r4 (c # cs));
         tail = gfuse (bbmkeps r1 @ [Backbit (rev cs)] @ bbmkeps r2)
           (GABASE [] (bbder c (gabbtail4 r3 (rev cs) r4)))
     in if bbnullable r1
        then GAALT bs prefix (if bbnullable r2 then GAALT [] capture tail else capture)
        else GABACKREF4 bs (bbder c r1) r2 r3 r4 cs)"

lemma gerase_GAALTs_map_gabder:
  assumes "\<And>r. r \<in> set rs \<Longrightarrow> gerase (gabder c r) = gxder c (gerase r)"
  shows "gerase (GAALTs bs (map (gabder c) rs)) =
    gxder c (gerase (GAALTs bs rs))"
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

lemma gerase_gabder [simp]:
  "gerase (gabder c r) = gxder c (gerase r)"
proof (induct r arbitrary: c)
  case (GAALTs bs rs)
  then show ?case
    by (simp add: gerase_GAALTs_map_gabder)
next
  case (GABACKREF4 bs r1 r2 r3 r4 cs)
  then show ?case
    by (simp add: Let_def)
qed simp_all

lemma gretrieve_alts_append:
  assumes "GPrf v (gerase (GAALTs cs rs))"
  shows "gretrieve_alts (bs @ cs) (map gretrieve rs) v =
    bs @ gretrieve_alts cs (map gretrieve rs) v"
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
      case (GVRight v2)
      have prf_tail0: "GPrf v2 (gerase (GAALTs [] rs))"
        using Cons.prems Cons GVRight by (auto elim!: GPrf_elims)
      have same: "gerase (GAALTs cs rs) = gerase (GAALTs [] rs)"
        by (rule gerase_GAALTs_ignore_bits)
      have prf_tail: "GPrf v2 (gerase (GAALTs cs rs))"
        using prf_tail0 by (simp only: same)
      have "gretrieve_alts (bs @ cs) (map gretrieve rs) v2 =
        bs @ gretrieve_alts cs (map gretrieve rs) v2"
        using Cons.hyps[OF prf_tail] .
      then show ?thesis
        using Cons GVRight by simp
    qed (use Cons.prems Cons in \<open>auto elim!: GPrf_elims\<close>)
  qed
qed

lemma gretrieve_gfuse:
  assumes "GPrf v (gerase r)"
  shows "gretrieve (gfuse bs r) v = bs @ gretrieve r v"
  using assms
proof (cases r)
  case (GAALTs cs rs)
  then show ?thesis
    using assms gretrieve_alts_append[of v cs rs bs] by simp
qed (auto elim!: GPrf_elims BPrf4_elims simp add: append_assoc)

lemma gretrieve_gbackref4_from_tail:
  assumes "\<Turnstile>b tail : gtail4 (berase r3) (rev cs) (berase r4)"
    and "bflat v2 = []"
  shows "gretrieve (GABACKREF4 bs r1 r2 r3 r4 cs)
      (gbackref4_from_tail v1 v2 cs tail) =
    bs @ bretrieve r1 v1 @ [Backbit (rev cs)] @ bretrieve r2 v2 @
      bretrieve (gabbtail4 r3 (rev cs) r4) tail"
  using assms
  unfolding gbackref4_from_tail_def gabbtail4_def gtail4_def
  by (auto elim!: BPrf_elims simp add: append_assoc)

lemma gretrieve_gbackref4_from_xder_tail:
  assumes "BPrf tail (xder c (gtail4 (berase r3) (rev cs) (berase r4)))"
    and "bbnullable r2"
  shows "gretrieve (GABACKREF4 bs r1 r2 r3 r4 cs)
      (gbackref4_from_tail (bmkeps (berase r1)) (bmkeps (berase r2)) cs
        (binjval (gtail4 (berase r3) (rev cs) (berase r4)) c tail)) =
    bs @ bretrieve r1 (bmkeps (berase r1)) @ [Backbit (rev cs)] @
      bretrieve r2 (bmkeps (berase r2)) @
      bretrieve (gabbtail4 r3 (rev cs) r4)
        (binjval (gtail4 (berase r3) (rev cs) (berase r4)) c tail)"
proof -
  have tail_prf:
    "BPrf (binjval (gtail4 (berase r3) (rev cs) (berase r4)) c tail)
      (gtail4 (berase r3) (rev cs) (berase r4))"
    using assms(1) by (rule binjval_BPrf)
  have empty2: "bflat (bmkeps (berase r2)) = []"
    using assms(2) by (auto intro: bmkeps_flat)
  show ?thesis
    using gretrieve_gbackref4_from_tail[OF tail_prf empty2] .
qed

lemma gabder_GAALTs_gretrieve:
  assumes step: "\<And>x w. x \<in> set rs \<Longrightarrow> GPrf w (gxder c (gerase x)) \<Longrightarrow> gretrieve (gabder c x) w = gretrieve x (ginjval (gerase x) c w)"
    and main: "GPrf v (gxder c (gerase (GAALTs bs rs)))"
  shows "gretrieve (gabder c (GAALTs bs rs)) v =
    gretrieve (GAALTs bs rs) (ginjval (gerase (GAALTs bs rs)) c v)"
  using step main
proof (induct rs arbitrary: bs v)
  case Nil
  then show ?case
    by simp
next
  case (Cons r rs)
  show ?case
  proof (cases rs)
    case Nil
    have "gretrieve (gabder c r) v =
      gretrieve r (ginjval (gerase r) c v)"
      using Cons.prems Nil by simp
    then show ?thesis
      using Nil by simp
  next
    case (Cons r' rs')
    show ?thesis
    proof (cases v)
      case (GVLeft v1)
      have prf_left: "GPrf v1 (gxder c (gerase r))"
        using Cons.prems Cons GVLeft by (auto elim!: GPrf_elims)
      have "gretrieve (gabder c r) v1 =
        gretrieve r (ginjval (gerase r) c v1)"
        using Cons.prems(1)[OF _ prf_left] by simp
      then show ?thesis
        using Cons GVLeft by simp
    next
      case (GVRight v2)
      have prf_tail0: "GPrf v2 (gxder c (gerase (GAALTs [] rs)))"
        using Cons.prems Cons GVRight by (auto elim!: GPrf_elims)
      have same: "gerase (GAALTs bs rs) = gerase (GAALTs [] rs)"
        by (rule gerase_GAALTs_ignore_bits)
      have prf_tail: "GPrf v2 (gxder c (gerase (GAALTs bs rs)))"
        using prf_tail0 by (simp only: same)
      have ginj_same:
        "ginjval (gerase (GAALTs bs rs)) c v2 =
         ginjval (gerase (GAALTs [] rs)) c v2"
        by (simp only: same)
      have step_tail: "\<And>x w. x \<in> set rs \<Longrightarrow> GPrf w (gxder c (gerase x)) \<Longrightarrow> gretrieve (gabder c x) w = gretrieve x (ginjval (gerase x) c w)"
        using Cons.prems by auto
      have "gretrieve (gabder c (GAALTs bs rs)) v2 =
        gretrieve (GAALTs bs rs) (ginjval (gerase (GAALTs bs rs)) c v2)"
        using Cons.hyps[OF step_tail prf_tail] .
      then show ?thesis
        using Cons GVRight ginj_same by simp
    qed (use Cons.prems Cons in \<open>auto elim!: GPrf_elims\<close>)
  qed
qed

lemma gabder_gretrieve:
  assumes "GPrf v (gxder c (gerase r))"
  shows "gretrieve (gabder c r) v = gretrieve r (ginjval (gerase r) c v)"
  using assms
proof (induct r arbitrary: c v)
  case (GABASE bs r)
  then show ?case
    by (auto elim!: GPrf_elims simp add: bbder_bretrieve)
next
  case (GAALTs bs rs)
  then show ?case
    by (rule gabder_GAALTs_gretrieve)
next
  case (GABACKREF4 bs r1 r2 r3 r4 cs)
  show ?case
  proof (cases "bbnullable r1")
    case False
    with GABACKREF4.prems show ?thesis
      by (auto elim!: GPrf_elims BPrf4_elims
          simp add: Let_def bbder_bretrieve)
  next
    case r1_null: True
    show ?thesis
    proof (cases "bbnullable r2")
      case False
      with r1_null GABACKREF4.prems show ?thesis
        by (auto elim!: GPrf_elims BPrf4_elims BPrf_elims
            simp add: Let_def gretrieve_gfuse bbmkeps_bretrieve
              bbder_bretrieve binjval_flat bmkeps_flat append_assoc)
    next
      case r2_null: True
      show ?thesis
      proof (cases v)
        case (GVLeft vp)
        with r1_null r2_null GABACKREF4.prems show ?thesis
          by (auto elim!: GPrf_elims BPrf4_elims BPrf_elims
              simp add: Let_def gretrieve_gfuse bbmkeps_bretrieve
                bbder_bretrieve binjval_flat bmkeps_flat append_assoc)
      next
        case (GVRight vR)
        note v_outer = GVRight
        show ?thesis
        proof (cases vR)
          case (GVLeft vc)
          with v_outer r1_null r2_null GABACKREF4.prems show ?thesis
            by (auto elim!: GPrf_elims BPrf4_elims BPrf_elims
                simp add: Let_def gretrieve_gfuse bbmkeps_bretrieve
                  bbder_bretrieve binjval_flat bmkeps_flat append_assoc)
        next
          case (GVRight vT)
          note v_mid = GVRight
          show ?thesis
          proof (cases vT)
            case (GVBase tail)
            note v_tail = GVBase
            have tail_prf:
              "BPrf tail (xder c (gtail4 (berase r3) (rev cs) (berase r4)))"
              using GABACKREF4.prems r1_null r2_null v_outer v_mid v_tail
              by (auto elim!: GPrf_elims)
            have lhs0:
              "gretrieve (gabder c (GABACKREF4 bs r1 r2 r3 r4 cs)) v =
                bs @ bbmkeps r1 @ [Backbit (rev cs)] @ bbmkeps r2 @
                  bretrieve (bbder c (gabbtail4 r3 (rev cs) r4)) tail"
              using r1_null r2_null v_outer v_mid v_tail
              by (simp add: Let_def append_assoc)
            have r1_bits:
              "bbmkeps r1 = bretrieve r1 (bmkeps (berase r1))"
              using r1_null by (rule bbmkeps_bretrieve)
            have r2_bits:
              "bbmkeps r2 = bretrieve r2 (bmkeps (berase r2))"
              using r2_null by (rule bbmkeps_bretrieve)
            have tail_bits:
              "bretrieve (bbder c (gabbtail4 r3 (rev cs) r4)) tail =
                bretrieve (gabbtail4 r3 (rev cs) r4)
                  (binjval (gtail4 (berase r3) (rev cs) (berase r4)) c tail)"
            proof -
              have tail_prf':
                "BPrf tail (xder c (berase (gabbtail4 r3 (rev cs) r4)))"
                using tail_prf by simp
              show ?thesis
                using bbder_bretrieve[OF tail_prf'] by simp
            qed
            have lhs:
              "gretrieve (gabder c (GABACKREF4 bs r1 r2 r3 r4 cs)) v =
                bs @ bretrieve r1 (bmkeps (berase r1)) @ [Backbit (rev cs)] @
                  bretrieve r2 (bmkeps (berase r2)) @
                  bretrieve (gabbtail4 r3 (rev cs) r4)
                    (binjval (gtail4 (berase r3) (rev cs) (berase r4)) c tail)"
              using lhs0 r1_bits r2_bits tail_bits by (simp add: append_assoc)
            have rhs0:
              "ginjval (gerase (GABACKREF4 bs r1 r2 r3 r4 cs)) c v =
                gbackref4_from_tail (bmkeps (berase r1)) (bmkeps (berase r2)) cs
                  (binjval (gtail4 (berase r3) (rev cs) (berase r4)) c tail)"
              using v_outer v_mid v_tail by simp
            have rhs:
              "gretrieve (GABACKREF4 bs r1 r2 r3 r4 cs)
                  (ginjval (gerase (GABACKREF4 bs r1 r2 r3 r4 cs)) c v) =
                bs @ bretrieve r1 (bmkeps (berase r1)) @ [Backbit (rev cs)] @
                  bretrieve r2 (bmkeps (berase r2)) @
                  bretrieve (gabbtail4 r3 (rev cs) r4)
                    (binjval (gtail4 (berase r3) (rev cs) (berase r4)) c tail)"
              using rhs0 gretrieve_gbackref4_from_xder_tail[OF tail_prf r2_null, of bs r1]
              by simp
            show ?thesis
              using lhs rhs by simp
          qed (use v_outer v_mid r1_null r2_null GABACKREF4.prems in
            \<open>auto elim!: GPrf_elims\<close>)
        qed (use v_outer r1_null r2_null GABACKREF4.prems in
          \<open>auto elim!: GPrf_elims\<close>)
      qed (use r1_null r2_null GABACKREF4.prems in
        \<open>auto elim!: GPrf_elims\<close>)
    qed
  qed
qed

fun gabders :: "gabexp \<Rightarrow> string \<Rightarrow> gabexp"
where
  "gabders r [] = r"
| "gabders r (c # s) = gabders (gabder c r) s"

definition gbblexer :: "gbrexp \<Rightarrow> string \<Rightarrow> bbit list option"
where
  "gbblexer r s =
    (let r' = gabders (gaintern r) s in
      if gabnullable r' then Some (gamkeps r') else None)"

lemma gerase_gabders [simp]:
  "gerase (gabders r s) = gxders (gerase r) s"
  by (induct s arbitrary: r) simp_all

lemma gbblexer_defined_iff:
  "(\<exists>bs. gbblexer r s = Some bs) \<longleftrightarrow> s \<in> GBL r"
  by (simp add: gbblexer_def gnullable_correctness gxders_correctness Ders_def Let_def)

lemma gabders_gabnullable_gblexer:
  assumes "gblexer (gerase a) s = Some v"
  shows "gabnullable (gabders a s)"
  using assms
proof (induct s arbitrary: a v)
  case Nil
  then show ?case
    by (auto split: if_splits)
next
  case (Cons c s)
  then obtain w where "gblexer (gxder c (gerase a)) s = Some w"
    by (auto split: option.splits)
  then have tail_der: "gblexer (gerase (gabder c a)) s = Some w"
    by simp
  then have "gabnullable (gabders (gabder c a) s)"
    by (rule Cons.hyps)
  then show ?case
    by simp
qed

lemma gabders_gretrieve_gblexer:
  assumes "gblexer (gerase a) s = Some v"
  shows "gamkeps (gabders a s) = gretrieve a v"
  using assms
proof (induct s arbitrary: a v)
  case Nil
  then have nullable: "gabnullable a" and v_def: "v = gmkeps (gerase a)"
    by (auto split: if_splits)
  show ?case
    using nullable v_def gamkeps_gretrieve by simp
next
  case (Cons c s)
  then obtain w where tail: "gblexer (gxder c (gerase a)) s = Some w"
    and v_def: "v = ginjval (gerase a) c w"
    by (auto split: option.splits)
  have tail_der: "gblexer (gerase (gabder c a)) s = Some w"
    using tail by simp
  have mkeps_tail: "gamkeps (gabders (gabder c a) s) =
      gretrieve (gabder c a) w"
    using Cons.hyps[OF tail_der] .
  have transport: "gretrieve (gabder c a) w =
      gretrieve a (ginjval (gerase a) c w)"
    using tail by (intro gabder_gretrieve gblexer_GPrf)
  show ?case
    using mkeps_tail transport v_def by simp
qed

lemma gbblexer_gretrieve_original:
  assumes "gblexer r s = Some v"
  shows "gbblexer r s = Some (gretrieve (gaintern r) v)"
proof -
  have nullable: "gabnullable (gabders (gaintern r) s)"
    using gabders_gabnullable_gblexer[of "gaintern r" s v] assms by simp
  have bits: "gamkeps (gabders (gaintern r) s) = gretrieve (gaintern r) v"
    using gabders_gretrieve_gblexer[of "gaintern r" s v] assms by simp
  show ?thesis
    using nullable bits by (simp add: gbblexer_def Let_def)
qed

theorem gbblexer_gblexer_retrieve:
  "gbblexer r s = map_option (gretrieve (gaintern r)) (gblexer r s)"
proof (cases "gblexer r s")
  case None
  then have "s \<notin> GBL r"
    using gblexer_correct_None by blast
  then have "\<not> (\<exists>bs. gbblexer r s = Some bs)"
    using gbblexer_defined_iff by blast
  then have "gbblexer r s = None"
    by (cases "gbblexer r s") auto
  then show ?thesis
    using None by simp
next
  case (Some v)
  then show ?thesis
    using gbblexer_gretrieve_original by simp
qed

lemma gbblexer_gretrieve:
  assumes "gbblexer r s = Some bs"
  shows "bs = gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s))"
proof -
  let ?a = "gabders (gaintern r) s"
  from assms have bs: "bs = gamkeps ?a" and nullable: "gabnullable ?a"
    by (auto simp add: gbblexer_def Let_def split: if_splits)
  from nullable have "gamkeps ?a = gretrieve ?a (gmkeps (gerase ?a))"
    by (rule gamkeps_gretrieve)
  then show ?thesis
    using bs by simp
qed

theorem gbblexer_retrieve_correctness:
  assumes "gbblexer r s = Some bs"
  shows "bs = gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s))"
    and "GPrf (gmkeps (gxders r s)) (gxders r s)"
    and "gflat (gmkeps (gxders r s)) = []"
proof -
  let ?a = "gabders (gaintern r) s"
  from assms have nullable: "gabnullable ?a"
    by (auto simp add: gbblexer_def Let_def split: if_splits)
  then have gnullable: "gnullable (gxders r s)"
    by simp
  show "bs = gretrieve ?a (gmkeps (gxders r s))"
    using assms by (rule gbblexer_gretrieve)
  show "GPrf (gmkeps (gxders r s)) (gxders r s)"
    using gnullable by (rule gmkeps_GPrf)
  show "gflat (gmkeps (gxders r s)) = []"
    using gnullable by (rule gmkeps_flat)
qed

theorem gbblexer_final_retrieve:
  "gbblexer r s =
    (if gnullable (gxders r s)
     then Some (gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s)))
     else None)"
proof (cases "gnullable (gxders r s)")
  case True
  let ?a = "gabders (gaintern r) s"
  have nullable: "gabnullable ?a"
    using True by simp
  have bits: "gamkeps ?a = gretrieve ?a (gmkeps (gxders r s))"
    using nullable gamkeps_gretrieve[of ?a] by simp
  show ?thesis
    using True bits by (simp add: gbblexer_def Let_def)
next
  case False
  then show ?thesis
    by (simp add: gbblexer_def Let_def)
qed

theorem gbblexer_final_membership:
  "gbblexer r s =
    (if s \<in> GBL r
     then Some (gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s)))
     else None)"
  by (simp add: gbblexer_final_retrieve gnullable_correctness
      gxders_correctness Ders_def)

lemma gbblexer_None_iff:
  "gbblexer r s = None \<longleftrightarrow> s \<notin> GBL r"
  by (simp add: gbblexer_final_membership)

lemma gbblexer_Some_iff:
  "gbblexer r s = Some bs \<longleftrightarrow>
    s \<in> GBL r \<and>
    bs = gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s))"
  by (auto simp add: gbblexer_final_membership split: if_splits)

lemma gbblexer_Some_gblexer_iff:
  "gbblexer r s = Some bs \<longleftrightarrow>
    (\<exists>v. gblexer r s = Some v \<and> bs = gretrieve (gaintern r) v)"
  by (cases "gblexer r s") (auto simp add: gbblexer_gblexer_retrieve)

lemma gbblexer_None_gblexer_iff:
  "gbblexer r s = None \<longleftrightarrow> gblexer r s = None"
  by (cases "gblexer r s") (simp_all add: gbblexer_gblexer_retrieve)

section \<open>Bitcoded Generalized Backreference Simplification\<close>

fun gabbsimp :: "gabexp \<Rightarrow> gabexp"
where
  "gabbsimp (GABASE bs r) = GABASE bs (bbsimp r)"
| "gabbsimp (GAALTs bs []) = GABASE bs BAZERO"
| "gabbsimp (GAALTs bs [r]) = gfuse bs (gabbsimp r)"
| "gabbsimp (GAALTs bs (r1 # r2 # rs)) = GAALTs bs (r1 # r2 # rs)"
| "gabbsimp (GABACKREF4 bs r1 r2 r3 r4 cs) =
    GABACKREF4 bs (bbsimp r1) (bbsimp r2) (bbsimp r3) (bbsimp r4) cs"

lemma gfuse_append [simp]:
  "gfuse (bs1 @ bs2) r = gfuse bs1 (gfuse bs2 r)"
  by (cases r) (simp_all add: append_assoc)

lemma gerase_gabbsimp [simp]:
  "gerase (gabbsimp r) = gerase r"
proof (induct r)
  case (GAALTs bs rs)
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
        using GAALTs.hyps outer by simp
    next
      case (Cons r' rs'')
      then show ?thesis
        using outer by simp
    qed
  qed
qed simp_all

lemma gabnullable_gabbsimp [simp]:
  "gabnullable (gabbsimp r) = gabnullable r"
  by (simp add: gabnullable_correctness)

lemma gabbsimp_gfuse [simp]:
  "gabbsimp (gfuse bs r) = gfuse bs (gabbsimp r)"
proof (cases r)
  case (GAALTs cs rs)
  then show ?thesis
  proof (cases rs)
    case Nil
    then show ?thesis
      using GAALTs by simp
  next
    case (Cons r rs')
    then show ?thesis
      using GAALTs by (cases rs') (simp_all add: append_assoc)
  qed
qed (simp_all add: append_assoc)

lemma gretrieve_gabbsimp:
  assumes "GPrf v (gerase r)"
  shows "gretrieve (gabbsimp r) v = gretrieve r v"
  using assms
proof (induct r arbitrary: v)
  case (GABASE bs r)
  then show ?case
    by (auto elim!: GPrf_elims simp add: bretrieve_bbsimp)
next
  case (GAALTs bs rs)
  show ?case
  proof (cases rs)
    case Nil
    then show ?thesis
      using GAALTs.prems by (auto elim!: GPrf_elims)
  next
    case (Cons r rs')
    note outer = Cons
    show ?thesis
    proof (cases rs')
      case Nil
      have prf_r: "GPrf v (gerase r)"
        using GAALTs.prems outer Nil by simp
      have "gretrieve (gfuse bs (gabbsimp r)) v =
        bs @ gretrieve (gabbsimp r) v"
        using prf_r by (simp add: gretrieve_gfuse)
      also have "... = bs @ gretrieve r v"
        using GAALTs.hyps prf_r outer Nil by simp
      finally have "gretrieve (gfuse bs (gabbsimp r)) v =
        bs @ gretrieve r v" .
      then show ?thesis
        using outer Nil by simp
    next
      case (Cons r' rs'')
      then show ?thesis
        using outer by simp
    qed
  qed
next
  case (GABACKREF4 bs r1 r2 r3 r4 cs)
  then show ?case
    by (auto elim!: GPrf_elims BPrf4_elims simp add: bretrieve_bbsimp)
qed

lemma gamkeps_gabbsimp:
  assumes "gabnullable r"
  shows "gamkeps (gabbsimp r) = gamkeps r"
proof -
  have nullable_simp: "gabnullable (gabbsimp r)"
    using assms by simp
  have "gamkeps (gabbsimp r) =
      gretrieve (gabbsimp r) (gmkeps (gerase (gabbsimp r)))"
    using nullable_simp by (rule gamkeps_gretrieve)
  also have "... = gretrieve (gabbsimp r) (gmkeps (gerase r))"
    by simp
  also have "... = gretrieve r (gmkeps (gerase r))"
    using assms by (intro gretrieve_gabbsimp gmkeps_GPrf)
      (simp add: gabnullable_correctness)
  also have "... = gamkeps r"
    using assms gamkeps_gretrieve by simp
  finally show ?thesis .
qed

fun gabders_simp :: "gabexp \<Rightarrow> string \<Rightarrow> gabexp"
where
  "gabders_simp r [] = gabbsimp r"
| "gabders_simp r (c # s) = gabders_simp (gabbsimp (gabder c r)) s"

lemma gerase_gabders_simp [simp]:
  "gerase (gabders_simp r s) = gxders (gerase r) s"
  by (induct s arbitrary: r) simp_all

lemma gabnullable_gabders_simp [simp]:
  "gabnullable (gabders_simp r s) = gabnullable (gabders r s)"
  by (simp add: gabnullable_correctness)

lemma gabders_simp_gabnullable_gblexer:
  assumes "gblexer (gerase a) s = Some v"
  shows "gabnullable (gabders_simp a s)"
  using assms gabders_gabnullable_gblexer[of a s v] by simp

lemma gabders_simp_gretrieve_gblexer:
  assumes "gblexer (gerase a) s = Some v"
  shows "gamkeps (gabders_simp a s) = gretrieve a v"
  using assms
proof (induct s arbitrary: a v)
  case Nil
  then have nullable: "gabnullable a" and v_def: "v = gmkeps (gerase a)"
    by (auto split: if_splits)
  have "gamkeps (gabders_simp a []) = gamkeps (gabbsimp a)"
    by simp
  also have "... = gamkeps a"
    using nullable by (rule gamkeps_gabbsimp)
  also have "... = gretrieve a (gmkeps (gerase a))"
    using nullable gamkeps_gretrieve by simp
  finally show ?case
    using v_def by simp
next
  case (Cons c s)
  then obtain w where tail: "gblexer (gxder c (gerase a)) s = Some w"
    and v_def: "v = ginjval (gerase a) c w"
    by (auto split: option.splits)
  have tail_simp: "gblexer (gerase (gabbsimp (gabder c a))) s = Some w"
    using tail by simp
  have mkeps_tail:
    "gamkeps (gabders_simp (gabbsimp (gabder c a)) s) =
      gretrieve (gabbsimp (gabder c a)) w"
    using Cons.hyps[OF tail_simp] .
  have prf_w: "GPrf w (gerase (gabder c a))"
    using tail by (simp add: gblexer_GPrf)
  have retrieve_simp:
    "gretrieve (gabbsimp (gabder c a)) w = gretrieve (gabder c a) w"
    using prf_w by (rule gretrieve_gabbsimp)
  have transport:
    "gretrieve (gabder c a) w = gretrieve a (ginjval (gerase a) c w)"
    using tail by (intro gabder_gretrieve gblexer_GPrf)
  show ?case
    using mkeps_tail retrieve_simp transport v_def by simp
qed

definition gbblexer_simp :: "gbrexp \<Rightarrow> string \<Rightarrow> bbit list option"
where
  "gbblexer_simp r s =
    (let r' = gabbsimp (gabders (gaintern r) s) in
      if gabnullable r' then Some (gamkeps r') else None)"

theorem gbblexer_simp_correctness:
  "gbblexer_simp r s = gbblexer r s"
proof -
  show ?thesis
  proof (cases "gabnullable (gabders (gaintern r) s)")
    case True
    then have "gamkeps (gabbsimp (gabders (gaintern r) s)) =
        gamkeps (gabders (gaintern r) s)"
      by (rule gamkeps_gabbsimp)
    then show ?thesis
      using True by (simp add: gbblexer_simp_def gbblexer_def Let_def)
  next
    case False
    then show ?thesis
      by (simp add: gbblexer_simp_def gbblexer_def Let_def)
  qed
qed

lemma gbblexer_simp_defined_iff:
  "(\<exists>bs. gbblexer_simp r s = Some bs) \<longleftrightarrow> s \<in> GBL r"
  by (simp add: gbblexer_simp_correctness gbblexer_defined_iff)

theorem gbblexer_simp_gblexer_retrieve:
  "gbblexer_simp r s = map_option (gretrieve (gaintern r)) (gblexer r s)"
  by (simp add: gbblexer_simp_correctness gbblexer_gblexer_retrieve)

theorem gbblexer_simp_retrieve_correctness:
  assumes "gbblexer_simp r s = Some bs"
  shows "bs = gretrieve (gabbsimp (gabders (gaintern r) s)) (gmkeps (gxders r s))"
    and "GPrf (gmkeps (gxders r s)) (gxders r s)"
    and "gflat (gmkeps (gxders r s)) = []"
proof -
  let ?a = "gabbsimp (gabders (gaintern r) s)"
  from assms have bs: "bs = gamkeps ?a" and nullable: "gabnullable ?a"
    by (auto simp add: gbblexer_simp_def Let_def split: if_splits)
  then have gnullable: "gnullable (gxders r s)"
    by simp
  from nullable have "gamkeps ?a = gretrieve ?a (gmkeps (gerase ?a))"
    by (rule gamkeps_gretrieve)
  then show "bs = gretrieve ?a (gmkeps (gxders r s))"
    using bs by simp
  show "GPrf (gmkeps (gxders r s)) (gxders r s)"
    using gnullable by (rule gmkeps_GPrf)
  show "gflat (gmkeps (gxders r s)) = []"
    using gnullable by (rule gmkeps_flat)
qed

theorem gbblexer_simp_final_retrieve:
  "gbblexer_simp r s =
    (if gnullable (gxders r s)
     then Some (gretrieve (gabbsimp (gabders (gaintern r) s)) (gmkeps (gxders r s)))
     else None)"
proof (cases "gnullable (gxders r s)")
  case True
  let ?a = "gabbsimp (gabders (gaintern r) s)"
  have nullable: "gabnullable ?a"
    using True by simp
  have bits: "gamkeps ?a = gretrieve ?a (gmkeps (gxders r s))"
    using nullable gamkeps_gretrieve[of ?a] by simp
  show ?thesis
    using True bits by (simp add: gbblexer_simp_def Let_def)
next
  case False
  then show ?thesis
    by (simp add: gbblexer_simp_def Let_def)
qed

theorem gbblexer_simp_final_membership:
  "gbblexer_simp r s =
    (if s \<in> GBL r
     then Some (gretrieve (gabbsimp (gabders (gaintern r) s)) (gmkeps (gxders r s)))
     else None)"
  by (simp add: gbblexer_simp_final_retrieve gnullable_correctness
      gxders_correctness Ders_def)

lemma gbblexer_simp_None_iff:
  "gbblexer_simp r s = None \<longleftrightarrow> s \<notin> GBL r"
  by (simp add: gbblexer_simp_final_membership)

lemma gbblexer_simp_Some_iff:
  "gbblexer_simp r s = Some bs \<longleftrightarrow>
    s \<in> GBL r \<and>
    bs = gretrieve (gabbsimp (gabders (gaintern r) s)) (gmkeps (gxders r s))"
  by (auto simp add: gbblexer_simp_final_membership split: if_splits)

lemma gbblexer_simp_Some_gblexer_iff:
  "gbblexer_simp r s = Some bs \<longleftrightarrow>
    (\<exists>v. gblexer r s = Some v \<and> bs = gretrieve (gaintern r) v)"
  by (cases "gblexer r s") (auto simp add: gbblexer_simp_gblexer_retrieve)

lemma gbblexer_simp_None_gblexer_iff:
  "gbblexer_simp r s = None \<longleftrightarrow> gblexer r s = None"
  by (simp add: gbblexer_simp_correctness gbblexer_None_gblexer_iff)

definition gbblexer_step_simp :: "gbrexp \<Rightarrow> string \<Rightarrow> bbit list option"
where
  "gbblexer_step_simp r s =
    (let r' = gabders_simp (gaintern r) s in
      if gabnullable r' then Some (gamkeps r') else None)"

lemma gbblexer_step_simp_defined_iff:
  "(\<exists>bs. gbblexer_step_simp r s = Some bs) \<longleftrightarrow> s \<in> GBL r"
  by (simp add: gbblexer_step_simp_def gnullable_correctness
      gxders_correctness Ders_def Let_def)

theorem gbblexer_step_simp_correctness:
  "gbblexer_step_simp r s = gbblexer r s"
proof (cases "gblexer r s")
  case None
  then have "s \<notin> GBL r"
    using gblexer_correct_None by blast
  then have "\<not> (\<exists>bs. gbblexer_step_simp r s = Some bs)"
    using gbblexer_step_simp_defined_iff by blast
  then have step_none: "gbblexer_step_simp r s = None"
    by (cases "gbblexer_step_simp r s") auto
  moreover have "gbblexer r s = None"
    using None gbblexer_gblexer_retrieve by simp
  ultimately show ?thesis
    by simp
next
  case (Some v)
  have nullable: "gabnullable (gabders_simp (gaintern r) s)"
    using Some gabders_simp_gabnullable_gblexer[of "gaintern r" s v] by simp
  have bits:
    "gamkeps (gabders_simp (gaintern r) s) = gretrieve (gaintern r) v"
    using Some gabders_simp_gretrieve_gblexer[of "gaintern r" s v] by simp
  have step: "gbblexer_step_simp r s = Some (gretrieve (gaintern r) v)"
    using nullable bits by (simp add: gbblexer_step_simp_def Let_def)
  have original: "gbblexer r s = Some (gretrieve (gaintern r) v)"
    using Some gbblexer_gblexer_retrieve by simp
  show ?thesis
    using step original by simp
qed

theorem gbblexer_step_simp_retrieve_correctness:
  assumes "gbblexer_step_simp r s = Some bs"
  shows "bs = gretrieve (gabders_simp (gaintern r) s) (gmkeps (gxders r s))"
    and "GPrf (gmkeps (gxders r s)) (gxders r s)"
    and "gflat (gmkeps (gxders r s)) = []"
proof -
  let ?a = "gabders_simp (gaintern r) s"
  from assms have bs: "bs = gamkeps ?a" and nullable: "gabnullable ?a"
    by (auto simp add: gbblexer_step_simp_def Let_def split: if_splits)
  then have gnullable: "gnullable (gxders r s)"
    by simp
  from nullable have "gamkeps ?a = gretrieve ?a (gmkeps (gerase ?a))"
    by (rule gamkeps_gretrieve)
  then show "bs = gretrieve ?a (gmkeps (gxders r s))"
    using bs by simp
  show "GPrf (gmkeps (gxders r s)) (gxders r s)"
    using gnullable by (rule gmkeps_GPrf)
  show "gflat (gmkeps (gxders r s)) = []"
    using gnullable by (rule gmkeps_flat)
qed

theorem gbblexer_step_simp_final_retrieve:
  "gbblexer_step_simp r s =
    (if gnullable (gxders r s)
     then Some (gretrieve (gabders_simp (gaintern r) s) (gmkeps (gxders r s)))
     else None)"
proof (cases "gnullable (gxders r s)")
  case True
  let ?a = "gabders_simp (gaintern r) s"
  have nullable: "gabnullable ?a"
    using True by simp
  have bits: "gamkeps ?a = gretrieve ?a (gmkeps (gxders r s))"
    using nullable gamkeps_gretrieve[of ?a] by simp
  show ?thesis
    using True bits by (simp add: gbblexer_step_simp_def Let_def)
next
  case False
  then show ?thesis
    by (simp add: gbblexer_step_simp_def Let_def)
qed

theorem gbblexer_step_simp_final_membership:
  "gbblexer_step_simp r s =
    (if s \<in> GBL r
     then Some (gretrieve (gabders_simp (gaintern r) s) (gmkeps (gxders r s)))
     else None)"
  by (simp add: gbblexer_step_simp_final_retrieve gnullable_correctness
      gxders_correctness Ders_def)

lemma gbblexer_step_simp_None_iff:
  "gbblexer_step_simp r s = None \<longleftrightarrow> s \<notin> GBL r"
  by (simp add: gbblexer_step_simp_final_membership)

lemma gbblexer_step_simp_Some_iff:
  "gbblexer_step_simp r s = Some bs \<longleftrightarrow>
    s \<in> GBL r \<and>
    bs = gretrieve (gabders_simp (gaintern r) s) (gmkeps (gxders r s))"
  by (auto simp add: gbblexer_step_simp_final_membership split: if_splits)

lemma gbblexer_step_simp_Some_gblexer_iff:
  "gbblexer_step_simp r s = Some bs \<longleftrightarrow>
    (\<exists>v. gblexer r s = Some v \<and> bs = gretrieve (gaintern r) v)"
  by (cases "gblexer r s")
    (auto simp add: gbblexer_step_simp_correctness gbblexer_gblexer_retrieve)

lemma gbblexer_step_simp_None_gblexer_iff:
  "gbblexer_step_simp r s = None \<longleftrightarrow> gblexer r s = None"
  by (simp add: gbblexer_step_simp_correctness gbblexer_None_gblexer_iff)

theorem gbblexer_step_simp_gblexer_retrieve:
  "gbblexer_step_simp r s = map_option (gretrieve (gaintern r)) (gblexer r s)"
  by (simp add: gbblexer_step_simp_correctness gbblexer_gblexer_retrieve)

theorem gbblexer_simp_step_simp_eq:
  "gbblexer_simp r s = gbblexer_step_simp r s"
  by (simp add: gbblexer_simp_correctness gbblexer_step_simp_correctness)

end
