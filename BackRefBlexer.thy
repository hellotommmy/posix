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

lemma xnullable_berase_BAALTs:
  "xnullable (berase (BAALTs bs rs)) =
    (\<exists>r \<in> set rs. xnullable (berase r))"
proof (induct rs arbitrary: bs)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  then show ?case
    by (cases rs) auto
qed

lemma bbnullable_correctness [simp]:
  "bbnullable r = xnullable (berase r)"
  apply (induct r)
           apply (simp_all add: xnullable_berase_BAALTs)
  done

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
           then BAALT [] (BAHALF [] (bbder c mid) (rev cs) (rev cs))
                          (bbder_residue c [] (rev cs) (rev cs))
           else BAHALF [] (bbder c mid) (rev cs) (rev cs)))
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
  then show ?case
    by (cases rs) auto
qed

lemma berase_bbder [simp]:
  "berase (bbder c r) = xder c (berase r)"
proof (induct r arbitrary: c)
  case (BAALTs bs rs)
  then show ?case
    by (simp add: berase_BAALTs_map_bbder)
qed simp_all

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

end
