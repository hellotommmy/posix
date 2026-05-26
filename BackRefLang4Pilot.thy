theory BackRefLang4Pilot
  imports BackRefLang
begin

section \<open>Generalized Backreference Expression Pilot\<close>

datatype gbrexp =
  GBASE brexp
| GALT gbrexp gbrexp
| GBACKREF4 brexp brexp brexp brexp string

fun GBL :: "gbrexp \<Rightarrow> string set"
where
  "GBL (GBASE r) = BL r"
| "GBL (GALT r1 r2) = GBL r1 \<union> GBL r2"
| "GBL (GBACKREF4 r1 r2 r3 r4 cs) =
     backref_lang4 (BL r1) (BL r2) (BL r3) (BL r4) cs"

fun gnullable :: "gbrexp \<Rightarrow> bool"
where
  "gnullable (GBASE r) = xnullable r"
| "gnullable (GALT r1 r2) = (gnullable r1 \<or> gnullable r2)"
| "gnullable (GBACKREF4 r1 r2 r3 r4 cs) =
     (xnullable r1 \<and> xnullable r2 \<and> xnullable r3 \<and> xnullable r4 \<and> cs = [])"

lemma gnullable_correctness:
  "gnullable r \<longleftrightarrow> [] \<in> GBL r"
  by (induct r) (auto simp add: xnullable_correctness backref_lang4_def)

definition gtail4 :: "brexp \<Rightarrow> string \<Rightarrow> brexp \<Rightarrow> brexp"
where
  "gtail4 r cs tail = BSEQ r (BSEQ (BRESIDUE cs cs) tail)"

lemma BL_gtail4 [simp]:
  "BL (gtail4 r cs tail) = BL r ;; ({cs} ;; BL tail)"
  by (simp add: gtail4_def)

fun gxder :: "char \<Rightarrow> gbrexp \<Rightarrow> gbrexp"
where
  "gxder c (GBASE r) = GBASE (xder c r)"
| "gxder c (GALT r1 r2) = GALT (gxder c r1) (gxder c r2)"
| "gxder c (GBACKREF4 r1 r2 r3 r4 cs) =
     (let prefix = GBACKREF4 (xder c r1) r2 r3 r4 cs;
          capture = GBACKREF4 BONE (xder c r2) r3 r4 (c # cs);
          tail = GBASE (xder c (gtail4 r3 (rev cs) r4))
      in if xnullable r1
         then GALT prefix (if xnullable r2 then GALT capture tail else capture)
         else prefix)"

lemma gxder_correctness:
  "GBL (gxder c r) = Der c (GBL r)"
  apply (induct r arbitrary: c)
    apply (simp add: xder_correctness)
   apply simp
  apply (auto simp add: Let_def Der_backref_lang4 xnullable_correctness xder_correctness)
  done

fun gxders :: "gbrexp \<Rightarrow> string \<Rightarrow> gbrexp"
where
  "gxders r [] = r"
| "gxders r (c # s) = gxders (gxder c r) s"

lemma gxders_append:
  "gxders r (s1 @ s2) = gxders (gxders r s1) s2"
  by (induct s1 arbitrary: r s2) simp_all

lemma gxders_snoc:
  "gxders r (s @ [c]) = gxder c (gxders r s)"
  by (simp add: gxders_append)

lemma gxders_correctness:
  "GBL (gxders r s) = Ders s (GBL r)"
  apply (induct s arbitrary: r)
   apply (simp add: Ders_def)
  apply (simp add: gxder_correctness Ders_def Der_def)
  done

end
