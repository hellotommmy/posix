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

end
