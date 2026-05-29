
theory Blexer
  imports "Lexer"
begin

section \<open>Bit-Encodings\<close>

(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation, ADMIN APPROVAL REQUIRED):
   Decide the final bit-code representation for backreference evidence before
   editing this file. Either extend the existing bit alphabet or encode
   backreference payloads without introducing a parallel bbit datatype. Do not
   add bblexer/gbblexer wrapper frontends; bounty only counts for extending the
   original code/decode/retrieve/blexer theorem chain. *)
datatype bit = Z | S

(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Extend code for the new original value constructors and the approved
   backreference bit representation. The goal remains decode (retrieve ...)
   for the original lexer pipeline, not a separate bit-output wrapper. *)
fun code :: "val \<Rightarrow> bit list"
where
  "code Void = []"
| "code (Char c) = []"
| "code (Left v) = Z # (code v)"
| "code (Right v) = S # (code v)"
| "code (Seq v1 v2) = (code v1) @ (code v2)"
| "code (Stars []) = [S]"
| "code (Stars (v # vs)) =  (Z # code v) @ code (Stars vs)"
| "code (Backref4 v1 v2 v3 v4 cs) = code v1 @ code v2 @ code v3 @ code v4"
| "code (Half v cs rep) = code v"
| "code (Residue cs rep) = []"

(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Add sz cases for BACKREF4/HALF/RESIDUE before changing decode'. *)
fun sz where
  "sz ZERO = 0"
| "sz ONE = 0"
| "sz (CH _) = 0"
| "sz (SEQ r1 r2) = 1 + sz r1 + sz r2"
| "sz (ALT r1 r2) = 1 + sz r1 + sz r2"
| "sz (STAR r) = 1 + sz r"
| "sz (NTIMES r n) = 1 + (n + 1) + sz r"
| "sz (BACKREF4 r1 r2 r3 r4 cs) = 1 + sz r1 + sz r2 + sz r3 + sz r4"
| "sz (HALF r cs rep) = 1 + sz r"
| "sz (RESIDUE cs rep) = 0"

fun 
  Stars_add :: "val \<Rightarrow> val \<Rightarrow> val"
where
  "Stars_add v (Stars vs) = Stars (v # vs)"

(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Extend decode' for BACKREF4/HALF/RESIDUE and the approved value/bit encoding.
   This is part of the original decode theorem chain, not a wrapper. *)
function (sequential)
  decode' :: "bit list \<Rightarrow> rexp \<Rightarrow> (val * bit list)"
where
  "decode' bs ZERO = (undefined, bs)"
| "decode' bs ONE = (Void, bs)"
| "decode' bs (CH d) = (Char d, bs)"
| "decode' [] (ALT r1 r2) = (Void, [])"
| "decode' (Z # bs) (ALT r1 r2) = (let (v, bs') = decode' bs r1 in (Left v, bs'))"
| "decode' (S # bs) (ALT r1 r2) = (let (v, bs') = decode' bs r2 in (Right v, bs'))"
| "decode' bs (SEQ r1 r2) = (let (v1, bs') = decode' bs r1 in
                             let (v2, bs'') = decode' bs' r2 in (Seq v1 v2, bs''))"
| "decode' [] (STAR r) = (Void, [])"
| "decode' (S # bs) (STAR r) = (Stars [], bs)"
| "decode' (Z # bs) (STAR r) = (let (v, bs') = decode' bs r in
                                     let (vs, bs'') = decode' bs' (STAR r)
                                     in (Stars_add v vs, bs''))"
| "decode' bs (NTIMES r n) = decode' bs (STAR r)"
| "decode' bs (BACKREF4 r1 r2 r3 r4 cs) =
    (let (v1, bs1) = decode' bs r1 in
     let (v2, bs2) = decode' bs1 r2 in
     let (v3, bs3) = decode' bs2 r3 in
     let (v4, bs4) = decode' bs3 r4 in
       (Backref4 v1 v2 v3 v4 cs, bs4))"
| "decode' bs (HALF r cs rep) =
    (let (v, bs') = decode' bs r in (Half v cs rep, bs'))"
| "decode' bs (RESIDUE cs rep) = (Residue cs rep, bs)"
by pat_completeness auto

lemma decode'_smaller:
  assumes "decode'_dom (bs, r)"
  shows "length (snd (decode' bs r)) \<le> length bs"
using assms
apply(induct bs r)
apply(auto simp add: decode'.psimps split: prod.split)
using dual_order.trans apply blast
apply (meson dual_order.trans le_SucI)
apply (metis dual_order.trans)
  done

termination "decode'"  
apply(relation "inv_image (measure(%cs. sz cs) <*lex*> measure(%s. size s)) (%(ds,r). (r,ds))") 
apply(auto dest!: decode'_smaller)
   apply (metis less_Suc_eq_le snd_conv)
  done

definition
  decode :: "bit list \<Rightarrow> rexp \<Rightarrow> val option"
where
  "decode ds r \<equiv> (let (v, ds') = decode' ds r 
                  in (if ds' = [] then Some v else None))"

lemma decode'_code_Stars:
  assumes "\<forall>v\<in>set vs. \<Turnstile> v : r \<and> (\<forall>x. decode' (code v @ x) r = (v, x)) \<and> flat v \<noteq> []" 
  shows "decode' (code (Stars vs) @ ds) (STAR r) = (Stars vs, ds)"
  using assms
  apply(induct vs)
  apply(auto)
  done

lemma decode'_code_NTIMES:
  assumes "\<forall>v\<in>set vs. \<Turnstile> v : r \<and> (\<forall>x. decode' (code v @ x) r = (v, x))" 
  shows "decode' (code (Stars vs) @ ds) (NTIMES r n) = (Stars vs, ds)"
  using assms
  apply(induct vs arbitrary: n r ds)
   apply(auto)
  done


lemma decode'_code:
  assumes "\<Turnstile> v : r"
  shows "decode' ((code v) @ ds) r = (v, ds)"
using assms
  apply(induct v r arbitrary: ds rule: Prf.induct) 
  apply(auto)[6]
  using decode'_code_Stars apply blast
  apply(rule decode'_code_NTIMES)
  apply(simp)
  apply(auto)
  done

lemma decode_code:
  assumes "\<Turnstile> v : r"
  shows "decode (code v) r = Some v"
  using assms unfolding decode_def
  by (smt append_Nil2 decode'_code old.prod.case)


section \<open>Annotated Regular Expressions\<close>

(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Extend the original annotated datatype arexp with approved annotated
   backreference, half, and residue constructors corresponding directly to the
   new rexp constructors. Do not introduce barexp/gabexp or any parallel
   annotated regex datatype. *)
datatype arexp = 
  AZERO
| AONE "bit list"
| ACHAR "bit list" char
| ASEQ "bit list" arexp arexp
| AALTs "bit list" "arexp list"
| ASTAR "bit list" arexp
| ANTIMES "bit list" arexp nat
| ABACKREF4 "bit list" arexp arexp arexp arexp string
| AHALF "bit list" arexp string string
| ARESIDUE "bit list" string string

abbreviation
  "AALT bs r1 r2 \<equiv> AALTs bs [r1, r2]"

(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Add size cases for the new arexp constructors. Keep termination measures
   explicit and lightweight; avoid tactics that run for minutes. *)
fun asize :: "arexp \<Rightarrow> nat" where
  "asize AZERO = 1"
| "asize (AONE cs) = 1" 
| "asize (ACHAR cs c) = 1"
| "asize (AALTs cs rs) = Suc (sum_list (map asize rs))"
| "asize (ASEQ cs r1 r2) = Suc (asize r1 + asize r2)"
| "asize (ASTAR cs r) = Suc (asize r)"
| "asize (ANTIMES cs r n) = Suc (asize r) + n"
| "asize (ABACKREF4 cs r1 r2 r3 r4 s) =
    Suc (asize r1 + asize r2 + asize r3 + asize r4)"
| "asize (AHALF cs r s rep) = Suc (asize r)"
| "asize (ARESIDUE cs s rep) = 1"

(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Add az2 cases for the new arexp constructors before changing retrieve. *)
fun az2 :: "arexp \<Rightarrow> nat" where
  "az2 AZERO = 1"
| "az2 (AONE cs) = 1" 
| "az2 (ACHAR cs c) = 1"
| "az2 (AALTs cs rs) = Suc (sum_list (map az2 rs))"
| "az2 (ASEQ cs r1 r2) = Suc (az2 r1 + az2 r2)"
| "az2 (ASTAR cs r) = Suc (az2 r)"
| "az2 (ANTIMES cs r n) = Suc (az2 r) + n + 1"
| "az2 (ABACKREF4 cs r1 r2 r3 r4 s) =
    Suc (az2 r1 + az2 r2 + az2 r3 + az2 r4)"
| "az2 (AHALF cs r s rep) = Suc (az2 r)"
| "az2 (ARESIDUE cs s rep) = 1"

(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Add erase cases for new arexp constructors and ensure erase/bder commute
   with the final rexp L/nullable/der semantics, including backref_lang4. *)
fun 
  erase :: "arexp \<Rightarrow> rexp"
where
  "erase AZERO = ZERO"
| "erase (AONE _) = ONE"
| "erase (ACHAR _ c) = CH c"
| "erase (AALTs _ []) = ZERO"
| "erase (AALTs _ [r]) = (erase r)"
| "erase (AALTs bs (r#rs)) = ALT (erase r) (erase (AALTs bs rs))"
| "erase (ASEQ _ r1 r2) = SEQ (erase r1) (erase r2)"
| "erase (ASTAR _ r) = STAR (erase r)"
| "erase (ANTIMES _ r n) = NTIMES (erase r) n"
| "erase (ABACKREF4 _ r1 r2 r3 r4 cs) =
    BACKREF4 (erase r1) (erase r2) (erase r3) (erase r4) cs"
| "erase (AHALF _ r cs rep) = HALF (erase r) cs rep"
| "erase (ARESIDUE _ cs rep) = RESIDUE cs rep"

lemma erase_AALTs_ignore_bits [simp]:
  "erase (AALTs bs rs) = erase (AALTs bs' rs)"
proof (induct rs arbitrary: bs bs')
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  then show ?case
    by (cases rs) simp_all
qed


(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Add fuse cases for the new arexp constructors while preserving bit-prefix
   behaviour used by retrieve and bsimp. *)
fun fuse :: "bit list \<Rightarrow> arexp \<Rightarrow> arexp" where
  "fuse bs AZERO = AZERO"
| "fuse bs (AONE cs) = AONE (bs @ cs)" 
| "fuse bs (ACHAR cs c) = ACHAR (bs @ cs) c"
| "fuse bs (AALTs cs rs) = AALTs (bs @ cs) rs"
| "fuse bs (ASEQ cs r1 r2) = ASEQ (bs @ cs) r1 r2"
| "fuse bs (ASTAR cs r) = ASTAR (bs @ cs) r"
| "fuse bs (ANTIMES cs r n) = ANTIMES (bs @ cs) r n"
| "fuse bs (ABACKREF4 cs r1 r2 r3 r4 s) = ABACKREF4 (bs @ cs) r1 r2 r3 r4 s"
| "fuse bs (AHALF cs r s rep) = AHALF (bs @ cs) r s rep"
| "fuse bs (ARESIDUE cs s rep) = ARESIDUE (bs @ cs) s rep"

lemma fuse_append:
  shows "fuse (bs1 @ bs2) r = fuse bs1 (fuse bs2 r)"
  apply(induct r)
  apply(auto)
  done

lemma fuse_Nil [simp]:
  shows "fuse [] r = r"
  by (induct r) auto


(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Add intern cases for the new rexp constructors, producing only the original
   arexp constructors. Do not route through pilot barexp/gabexp. *)
fun intern :: "rexp \<Rightarrow> arexp" where
  "intern ZERO = AZERO"
| "intern ONE = AONE []"
| "intern (CH c) = ACHAR [] c"
| "intern (ALT r1 r2) = AALT [] (fuse [Z] (intern r1)) 
                                (fuse [S]  (intern r2))"
| "intern (SEQ r1 r2) = ASEQ [] (intern r1) (intern r2)"
| "intern (STAR r) = ASTAR [] (intern r)"
| "intern (NTIMES r n) = ANTIMES [] (intern r) n"
| "intern (BACKREF4 r1 r2 r3 r4 cs) =
    ABACKREF4 [] (intern r1) (intern r2) (intern r3) (intern r4) cs"
| "intern (HALF r cs rep) = AHALF [] (intern r) cs rep"
| "intern (RESIDUE cs rep) = ARESIDUE [] cs rep"

(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Extend retrieve for the new value and arexp constructors under the approved
   backreference bit representation. This is the central original bitcoded
   evidence path; wrapper retrieval lemmas do not count. *)
function (sequential) retrieve  :: "arexp \<Rightarrow> val \<Rightarrow> bit list" where
  "retrieve AZERO v = undefined"
| "retrieve (AONE bs) v = (case v of Void \<Rightarrow> bs | _ \<Rightarrow> undefined)"
| "retrieve (ACHAR bs c) v = (case v of Char d \<Rightarrow> bs | _ \<Rightarrow> undefined)"
| "retrieve (AALTs bs rs) v =
    (case rs of
      [] \<Rightarrow> undefined
    | [r] \<Rightarrow> bs @ retrieve r v
    | r # r' # rs' \<Rightarrow>
        (case v of
          Left v' \<Rightarrow> bs @ retrieve r v'
        | Right v' \<Rightarrow> bs @ retrieve (AALTs [] (r' # rs')) v'
        | _ \<Rightarrow> undefined))"
| "retrieve (ASEQ bs r1 r2) v =
    (case v of Seq v1 v2 \<Rightarrow> bs @ retrieve r1 v1 @ retrieve r2 v2 | _ \<Rightarrow> undefined)"
| "retrieve (ASTAR bs r) v =
    (case v of
      Stars [] \<Rightarrow> bs @ [S]
    | Stars (v' # vs) \<Rightarrow> bs @ [Z] @ retrieve r v' @ retrieve (ASTAR [] r) (Stars vs)
    | _ \<Rightarrow> undefined)"
| "retrieve (ANTIMES bs r n) v =
    (case v of Stars vs \<Rightarrow> retrieve (ASTAR bs r) (Stars vs) | _ \<Rightarrow> undefined)"
| "retrieve (ABACKREF4 bs r1 r2 r3 r4 cs) v =
    (case v of
      Backref4 v1 v2 v3 v4 cs' \<Rightarrow>
        bs @ retrieve r1 v1 @ retrieve r2 v2 @ retrieve r3 v3 @ retrieve r4 v4
    | _ \<Rightarrow> undefined)"
| "retrieve (AHALF bs r cs rep) v =
    (case v of Half v' cs' rep' \<Rightarrow> bs @ retrieve r v' | _ \<Rightarrow> undefined)"
| "retrieve (ARESIDUE bs cs rep) v =
    (case v of Residue cs' rep' \<Rightarrow> bs | _ \<Rightarrow> undefined)"
     apply(pat_completeness)
  by simp_all

termination "retrieve" 
apply(relation "inv_image (measure(%cs. size cs) <*lex*> measure(%s. az2 s)) (%(ds,r). (r,ds))") 
  apply(auto)
done

(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Add bnullable cases for the new arexp constructors. *)
fun
 bnullable :: "arexp \<Rightarrow> bool"
where
  "bnullable (AZERO) = False"
| "bnullable (AONE bs) = True"
| "bnullable (ACHAR bs c) = False"
| "bnullable (AALTs bs rs) = (\<exists>r \<in> set rs. bnullable r)"
| "bnullable (ASEQ bs r1 r2) = (bnullable r1 \<and> bnullable r2)"
| "bnullable (ASTAR bs r) = True"
| "bnullable (ANTIMES bs r n) = (if n  = 0 then True else bnullable r)"
| "bnullable (ABACKREF4 bs r1 r2 r3 r4 cs) =
    (bnullable r1 \<and> bnullable r2 \<and> bnullable r3 \<and> bnullable r4 \<and> cs = [])"
| "bnullable (AHALF bs r cs rep) = (bnullable r \<and> cs = [])"
| "bnullable (ARESIDUE bs cs rep) = (cs = [])"

abbreviation
  bnullables :: "arexp list \<Rightarrow> bool"
where
  "bnullables rs \<equiv> (\<exists>r \<in> set rs. bnullable r)"

(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Add bmkeps cases for the new arexp constructors, matching original mkeps
   after erase and preserving retrieve correctness. *)
function (sequential)
  bmkeps :: "arexp \<Rightarrow> bit list" 
where
  "bmkeps(AONE bs) = bs"
| "bmkeps(ASEQ bs r1 r2) = bs @ (bmkeps r1) @ (bmkeps r2)"
| "bmkeps(AALTs bs (r#rs)) = 
    (if bnullable(r) then (bs @ bmkeps r) else (bmkeps (AALTs bs rs)))"
| "bmkeps(ASTAR bs r) = bs @ [S]"
| "bmkeps(ANTIMES bs r n) = 
    (if n = 0 then bs @ [S] else bs @ [Z] @ (bmkeps r) @ bmkeps(ANTIMES [] r (n - 1)))"
| "bmkeps(ABACKREF4 bs r1 r2 r3 r4 cs) =
    bs @ bmkeps r1 @ bmkeps r2 @ bmkeps r3 @ bmkeps r4"
| "bmkeps(AHALF bs r cs rep) = bs @ bmkeps r"
| "bmkeps(ARESIDUE bs cs rep) = bs"
apply(pat_completeness)
apply(auto)
done

termination "bmkeps"  
apply(relation "measure asize") 
        apply(auto)
  using asize.elims by force

fun
   bmkepss :: "arexp list \<Rightarrow> bit list"
where
  "bmkepss (r # rs) = (if bnullable(r) then (bmkeps r) else (bmkepss rs))"


lemma bmkepss1:
  assumes "\<not> bnullables rs1"
  shows "bmkepss (rs1 @ rs2) = bmkepss rs2"
  using assms
  by(induct rs1) (auto)
  

lemma bmkepss2:
  assumes "bnullables rs1"
  shows "bmkepss (rs1 @ rs2) = bmkepss rs1"
  using assms
  by (induct rs1) (auto)


(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Add bder cases for the new arexp constructors. These cases must commute with
   original der through erase; do not preserve the old two-part pilot language. *)
fun
 bder :: "char \<Rightarrow> arexp \<Rightarrow> arexp"
where
  "bder c (AZERO) = AZERO"
| "bder c (AONE bs) = AZERO"
| "bder c (ACHAR bs d) = (if c = d then AONE bs else AZERO)"
| "bder c (AALTs bs rs) = AALTs bs (map (bder c) rs)"
| "bder c (ASEQ bs r1 r2) = 
     (if bnullable r1
      then AALT bs (ASEQ [] (bder c r1) r2) (fuse (bmkeps r1) (bder c r2))
      else ASEQ bs (bder c r1) r2)"
| "bder c (ASTAR bs r) = ASEQ (bs @ [Z]) (bder c r) (ASTAR [] r)"
| "bder c (ANTIMES bs r n) = (if n = 0 then AZERO else ASEQ (bs @ [Z]) (bder c r) (ANTIMES [] r (n - 1)))"
| "bder c (ABACKREF4 bs r1 r2 r3 r4 cs) =
     (let prefix = ABACKREF4 [] (bder c r1) r2 r3 r4 cs;
          capture = ABACKREF4 (bmkeps r1) (AONE []) (bder c r2) r3 r4 (c # cs);
          res = rev cs;
          res_der = bder c (ARESIDUE [] res res);
          res_tail = (if res = []
            then AALT (bmkeps r3)
              (ASEQ [] res_der r4) (bder c r4)
            else ASEQ (bmkeps r3) res_der r4);
          tail = (if bnullable r3
            then AALT (bmkeps r1 @ bmkeps r2)
              (ASEQ [] (bder c r3) (ASEQ [] (ARESIDUE [] res res) r4)) res_tail
            else ASEQ (bmkeps r1 @ bmkeps r2)
              (bder c r3) (ASEQ [] (ARESIDUE [] res res) r4))
      in fuse bs (if bnullable r1
         then AALT [] prefix (if bnullable r2 then AALT [] capture tail else capture)
         else prefix))"
| "bder c (AHALF bs r cs rep) =
     (if bnullable r
      then AALT bs (AHALF [] (bder c r) cs rep)
        (fuse (bmkeps r) (bder c (ARESIDUE [] cs rep)))
      else AHALF bs (bder c r) cs rep)"
| "bder c (ARESIDUE bs [] rep) = AZERO"
| "bder c (ARESIDUE bs (d # ds) rep) = (if c = d then ARESIDUE bs ds rep else AZERO)"

(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   bders should keep its recursion shape, but must be rechecked after bder is
   extended with BACKREF4/HALF/RESIDUE cases. *)
fun 
  bders :: "arexp \<Rightarrow> string \<Rightarrow> arexp"
where
  "bders r [] = r"
| "bders r (c#s) = bders (bder c r) s"

lemma bders_append:
  "bders c (s1 @ s2) = bders (bders c s1) s2"
  apply(induct s1 arbitrary: c s2)
  apply(simp_all)
  done

lemma bnullable_correctness:
  shows "nullable (erase r) = bnullable r"
  apply(induct r rule: erase.induct)
  apply(simp_all)
  done

lemma erase_fuse:
  shows "erase (fuse bs r) = erase r"
  apply(induct r rule: erase.induct)
  apply(simp_all)
  done

lemma erase_intern [simp]:
  shows "erase (intern r) = r"
  apply(induct r)
  apply(simp_all add: erase_fuse)
  done

lemma erase_bder_ARESIDUE [simp]:
  shows "erase (bder a (ARESIDUE bs cs rep)) = der_residue a cs rep"
  by (cases cs) simp_all

(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend this original theorem by adding the new constructor cases. Keep the
   original interface; do not prove a renamed wrapper theorem. *)
lemma erase_bder [simp]:
  shows "erase (bder a r) = der a (erase r)"
  apply(induct r rule: erase.induct)
  apply(simp_all add: erase_fuse bnullable_correctness Let_def)
  done

lemma erase_bders [simp]:
  shows "erase (bders r s) = ders s (erase r)"
  apply(induct s arbitrary: r )
  apply(simp_all)
  done

lemma bnullable_fuse:
  shows "bnullable (fuse bs r) = bnullable r"
  apply(induct r arbitrary: bs)
  apply(auto)
  done

lemma retrieve_encode_STARS:
  assumes "\<forall>v\<in>set vs. \<Turnstile> v : r \<and> code v = retrieve (intern r) v"
  shows "code (Stars vs) = retrieve (ASTAR [] (intern r)) (Stars vs)"
  using assms
  apply(induct vs)
  apply(simp_all)
  done

lemma retrieve_encode_STARS_case:
  assumes "\<forall>v\<in>set vs. \<Turnstile> v : r \<and> code v = retrieve (intern r) v"
  shows "code (Stars vs) =
    (case vs of [] \<Rightarrow> [] @ [S]
     | v # vs' \<Rightarrow> [] @ [Z] @ retrieve (intern r) v @
        retrieve (ASTAR [] (intern r)) (Stars vs'))"
  using retrieve_encode_STARS[OF assms]
  by (cases vs) (simp_all add: retrieve.simps)

lemma retrieve_encode_NTIMES:
  assumes "\<forall>v\<in>set vs. \<Turnstile> v : r \<and> code v = retrieve (intern r) v" 
  shows "code (Stars vs) = retrieve (ANTIMES [] (intern r) n) (Stars vs)"
proof -
  have "code (Stars vs) = retrieve (ASTAR [] (intern r)) (Stars vs)"
    using assms by (rule retrieve_encode_STARS)
  then show ?thesis
    by (simp add: retrieve.simps)
qed

lemma retrieve_encode_STARS_append:
  assumes "\<forall>v\<in>set vs1. \<Turnstile> v : r \<and> code v = retrieve (intern r) v"
    and "\<forall>v\<in>set vs2. \<Turnstile> v : r \<and> code v = retrieve (intern r) v"
  shows "code (Stars (vs1 @ vs2)) =
    retrieve (ASTAR [] (intern r)) (Stars (vs1 @ vs2))"
  using assms retrieve_encode_STARS[of "vs1 @ vs2" r] by auto

lemma retrieve_encode_STARS_append_case:
  assumes "\<forall>v\<in>set vs1. \<Turnstile> v : r \<and> code v = retrieve (intern r) v"
    and "\<forall>v\<in>set vs2. \<Turnstile> v : r \<and> code v = retrieve (intern r) v"
  shows "code (Stars (vs1 @ vs2)) =
    (case vs1 @ vs2 of [] \<Rightarrow> [] @ [S]
     | v # vs \<Rightarrow> [] @ [Z] @ retrieve (intern r) v @
        retrieve (ASTAR [] (intern r)) (Stars vs))"
  using retrieve_encode_STARS_append[OF assms]
  by (cases "vs1 @ vs2") (simp_all add: retrieve.simps)

 

lemma retrieve_fuse2:
  assumes "\<Turnstile> v : (erase r)"
  shows "retrieve (fuse bs r) v = bs @ retrieve r v"
  using assms
proof (induct r arbitrary: v bs)
  case AZERO
  then show ?case by (auto elim: Prf_elims)
next
  case (AONE x)
  then show ?case by (auto elim: Prf_elims)
next
  case (ACHAR x1 x2)
  then show ?case by (auto elim: Prf_elims)
next
  case (ASEQ x1 r1 r2)
  then show ?case by (auto elim!: Prf_elims simp add: append_assoc)
next
  case (AALTs x rs)
  then show ?case
  proof (cases rs)
    case Nil
    then show ?thesis
      using AALTs.prems by (auto elim: Prf_elims)
  next
    case (Cons r rs')
    note rs_cons = Cons
    then show ?thesis
    proof (cases rs')
      case Nil
      then show ?thesis
        using rs_cons by (simp add: append_assoc)
    next
      case (Cons r' rs'')
      then show ?thesis
        using AALTs.prems rs_cons Cons
        by (cases v) (auto elim!: Prf_elims simp add: append_assoc)
    qed
  qed
next
  case (ASTAR x r)
  then show ?case
    by (cases v) (auto elim!: Prf_elims simp add: append_assoc split: list.splits)
next
  case (ANTIMES x1 r x3)
  then show ?case
    by (cases v) (auto elim!: Prf_elims simp add: append_assoc split: list.splits)
next
  case (ABACKREF4 x1 r1 r2 r3 r4 x6)
  then show ?case
    by (cases v) (auto elim!: Prf_elims simp add: append_assoc)
next
  case (AHALF x1 r x3 x4)
  then show ?case
    by (cases v) (auto elim!: Prf_elims simp add: append_assoc)
next
  case (ARESIDUE x1 x2 x3)
  then show ?case
    by (cases v) (auto elim!: Prf_elims simp add: append_assoc)
qed

lemma retrieve_fuse2_erase:
  assumes "\<Turnstile> v : erase (fuse bs r)"
  shows "retrieve (fuse bs r) v = bs @ retrieve r v"
  using assms retrieve_fuse2[of v r bs]
  by (simp add: erase_fuse)

lemma retrieve_fuse:
  assumes "\<Turnstile> v : r"
  shows "retrieve (fuse bs (intern r)) v = bs @ retrieve (intern r) v"
  using assms 
  by (simp_all add: retrieve_fuse2)


(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend retrieve_code for the new original constructors. Bounty applies only
   if this theorem keeps its original interface and passes with the extended
   datatype. *)
lemma retrieve_code:
  assumes "\<Turnstile> v : r"
  shows "code v = retrieve (intern r) v"
  using assms
  apply(induct v r )
        apply(simp_all add: retrieve_fuse retrieve_encode_STARS retrieve_encode_STARS_append
          retrieve_encode_STARS_append_case)
  apply (rule retrieve_encode_STARS_case)
  apply auto
  done



lemma retrieve_AALTs_bnullable1:
  assumes "bnullable r"
  shows "retrieve (AALTs bs (r # rs)) (mkeps (erase (AALTs bs (r # rs))))
         = bs @ retrieve r (mkeps (erase r))"
  using assms
  apply(case_tac rs)
  apply(auto simp add: bnullable_correctness)
  done

lemma retrieve_AALTs_bnullable2:
  assumes "\<not>bnullable r" "bnullables rs"
  shows "retrieve (AALTs bs (r # rs)) (mkeps (erase (AALTs bs (r # rs))))
         = retrieve (AALTs bs rs) (mkeps (erase (AALTs bs rs)))"
  using assms
  apply(induct rs arbitrary: r bs)
  apply(auto)
  using bnullable_correctness apply blast
  apply(case_tac rs)
  apply(auto)
  using bnullable_correctness apply blast
  apply(case_tac rs)
  apply(auto)
  done

lemma retrieve_AALTs_nonempty_prefix:
  assumes "rs \<noteq> []" "\<Turnstile> v : erase (AALTs bs rs)"
  shows "retrieve (AALTs bs rs) v = bs @ retrieve (AALTs [] rs) v"
proof (cases rs)
  case Nil
  then show ?thesis
    using assms by simp
next
  case (Cons r rs')
  note outer = Cons
  then show ?thesis
  proof (cases rs')
    case Nil
    then show ?thesis
      using outer by (simp add: append_assoc)
  next
    case (Cons r' rs'')
    then show ?thesis
      using outer assms by (auto elim!: Prf_elims simp add: append_assoc)
  qed
qed

lemma erase_AALTs_map_bder:
  "erase (AALTs bs (map (bder c) rs)) = der c (erase (AALTs bs rs))"
  using erase_bder[of c "AALTs bs rs"] by simp

lemma bmkeps_retrieve_AALTs: 
  assumes "\<forall>r \<in> set rs. bnullable r \<longrightarrow> bmkeps r = retrieve r (mkeps (erase r))" 
          "bnullables rs"
  shows "bs @ bmkepss rs = retrieve (AALTs bs rs) (mkeps (erase (AALTs bs rs)))"
  using assms
proof (induct rs arbitrary: bs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  show ?case
  proof (cases "bnullable a")
    case True
    then have rec_a: "bmkeps a = retrieve a (mkeps (erase a))"
      using Cons.prems(1) by simp
    show ?thesis
      using retrieve_AALTs_bnullable1[OF True, of bs rs] rec_a True
      by simp
  next
    case False
    then have tail_nullable: "bnullables rs"
      using Cons.prems(2) by simp
    have tail_hyp:
      "\<forall>r\<in>set rs. bnullable r \<longrightarrow> bmkeps r = retrieve r (mkeps (erase r))"
      using Cons.prems(1) by simp
    have ih: "bs @ bmkepss rs =
      retrieve (AALTs bs rs) (mkeps (erase (AALTs bs rs)))"
      using Cons.hyps[OF tail_hyp tail_nullable, of bs] .
    have step:
      "retrieve (AALTs bs (a # rs)) (mkeps (erase (AALTs bs (a # rs)))) =
       retrieve (AALTs bs rs) (mkeps (erase (AALTs bs rs)))"
      using retrieve_AALTs_bnullable2[OF False tail_nullable, of bs] .
    show ?thesis
      using False ih step by simp
  qed
qed

lemma bmkeps_retrieve_ANTIMES: 
  assumes "if n = 0 then True else bmkeps r = retrieve r (mkeps (erase r))" 
  and     "bnullable (ANTIMES bs r n)"
  shows "bmkeps (ANTIMES bs r n) = retrieve (ANTIMES bs r n) (Stars (replicate n (mkeps (erase r))))"
 using assms
  apply(induct n arbitrary: r bs)
  apply(auto)[1]
  apply(simp)
  done

(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend bmkeps_retrieve for the new constructor cases; no wrapper theorem. *)
lemma bmkeps_retrieve:
  assumes "bnullable r"
  shows "bmkeps r = retrieve r (mkeps (erase r))"
  using assms
  apply(induct r rule: bmkeps.induct)
        apply(auto simp add: append_assoc)
  apply (case_tac rs)
   apply (simp_all add: bnullable_correctness)
  apply (case_tac rs)
   apply (simp_all add: bnullable_correctness)
  apply (case_tac rs)
   apply simp
  apply (simp add: bnullable_correctness)
  apply (case_tac "bnullable a")
   apply (case_tac list)
    apply (simp add: bnullable_correctness)
   apply (simp add: bnullable_correctness)
  apply (subgoal_tac "bnullables list")
   apply (case_tac list)
    apply simp
   apply simp
  apply force
  apply (case_tac n)
   apply simp
  apply (simp add: replicate_Suc)
  done

lemma retrieve_bder_ARESIDUE:
  assumes "\<Turnstile> v : der_residue c cs rep"
  shows "retrieve (bder c (ARESIDUE bs cs rep)) v = bs"
  using assms
  by (cases cs; cases v) (auto elim!: Prf_elims split: if_splits)

lemma bder_retrieve_AHALF:
  assumes IH: "\<And>v. \<Turnstile> v : der c (erase r) \<Longrightarrow>
      retrieve (bder c r) v = retrieve r (injval (erase r) c v)"
    and P: "\<Turnstile> v : der c (erase (AHALF bs r cs rep))"
  shows "retrieve (bder c (AHALF bs r cs rep)) v =
    retrieve (AHALF bs r cs rep) (injval (erase (AHALF bs r cs rep)) c v)"
proof (cases "bnullable r")
  case False
  then obtain v0 where v:
    "v = Half v0 cs rep" "\<Turnstile> v0 : der c (erase r)"
    using P by (auto elim!: Prf_elims simp add: bnullable_correctness)
  then show ?thesis
    using IH[OF v(2)] False by simp
next
  case n: True
  then have alt: "\<Turnstile> v : ALT (HALF (der c (erase r)) cs rep) (der_residue c cs rep)"
    using P by (simp add: bnullable_correctness)
  then consider
    (left) v0 where "v = Left (Half v0 cs rep)" "\<Turnstile> v0 : der c (erase r)"
  | (right) vr where "v = Right vr" "\<Turnstile> vr : der_residue c cs rep"
    by (auto elim!: Prf_elims)
  then show ?thesis
  proof cases
    case left
    then show ?thesis
      using IH[OF left(2)] n by simp
  next
    case right
    have residue: "retrieve (bder c (ARESIDUE [] cs rep)) vr = []"
      using right(2) by (rule retrieve_bder_ARESIDUE)
    have inj: "inj_residue cs rep c vr = Residue cs rep"
      using right(2) by (rule Prf_der_residue_inj)
    show ?thesis
      using right residue inj bmkeps_retrieve[OF n] n
      by (simp add: retrieve_fuse2 bnullable_correctness)
  qed
qed

lemma bder_retrieve_AALTs_Cons:
  assumes IH: "\<And>v. \<Turnstile> v : der c (erase r) \<Longrightarrow>
      retrieve (bder c r) v = retrieve r (injval (erase r) c v)"
    and IHs: "\<And>v. \<Turnstile> v : der c (erase (AALTs bs rs)) \<Longrightarrow>
      retrieve (bder c (AALTs bs rs)) v =
      retrieve (AALTs bs rs) (injval (erase (AALTs bs rs)) c v)"
    and P: "\<Turnstile> v : der c (erase (AALTs bs (r # rs)))"
  shows "retrieve (bder c (AALTs bs (r # rs))) v =
    retrieve (AALTs bs (r # rs)) (injval (erase (AALTs bs (r # rs))) c v)"
proof (cases rs)
  case Nil
  then show ?thesis
    using IH P by simp
next
  case (Cons r' rs')
  then have Palt: "\<Turnstile> v : ALT (der c (erase r)) (der c (erase (AALTs bs rs)))"
    using P by simp
  then consider
    (left) v1 where "v = Left v1" "\<Turnstile> v1 : der c (erase r)"
  | (right) v2 where "v = Right v2" "\<Turnstile> v2 : der c (erase (AALTs bs rs))"
    by (auto elim!: Prf_elims)
  then show ?thesis
  proof cases
    case left
    then show ?thesis
      using IH[OF left(2)] Cons by simp
  next
    case right
    have rs_ne: "rs \<noteq> []"
      using Cons by simp
    have map_ne: "map (bder c) rs \<noteq> []"
      using rs_ne by simp
    have map_prf: "\<Turnstile> v2 : erase (AALTs bs (map (bder c) rs))"
      using right(2) by (simp add: erase_AALTs_map_bder)
    have lhs_prefix:
      "retrieve (bder c (AALTs bs rs)) v2 =
       bs @ retrieve (AALTs [] (map (bder c) rs)) v2"
      using retrieve_AALTs_nonempty_prefix[OF map_ne map_prf] by simp
    have inj_prf: "\<Turnstile> injval (erase (AALTs bs rs)) c v2 : erase (AALTs bs rs)"
      using right(2) by (rule Prf_injval)
    have rhs_prefix:
      "retrieve (AALTs bs rs) (injval (erase (AALTs bs rs)) c v2) =
       bs @ retrieve (AALTs [] rs) (injval (erase (AALTs bs rs)) c v2)"
      using retrieve_AALTs_nonempty_prefix[OF rs_ne inj_prf] .
    have "retrieve (bder c (AALTs bs rs)) v2 =
      retrieve (AALTs bs rs) (injval (erase (AALTs bs rs)) c v2)"
      using IHs[OF right(2)] .
    then have "retrieve (AALTs [] (map (bder c) rs)) v2 =
      retrieve (AALTs [] rs) (injval (erase (AALTs bs rs)) c v2)"
      using lhs_prefix rhs_prefix by simp
    then show ?thesis
      using right Cons by simp
  qed
qed

lemma bder_retrieve_ABACKREF4:
  assumes IH1: "\<And>v. \<Turnstile> v : der c (erase r1) \<Longrightarrow>
      retrieve (bder c r1) v = retrieve r1 (injval (erase r1) c v)"
    and IH2: "\<And>v. \<Turnstile> v : der c (erase r2) \<Longrightarrow>
      retrieve (bder c r2) v = retrieve r2 (injval (erase r2) c v)"
    and IH3: "\<And>v. \<Turnstile> v : der c (erase r3) \<Longrightarrow>
      retrieve (bder c r3) v = retrieve r3 (injval (erase r3) c v)"
    and IH4: "\<And>v. \<Turnstile> v : der c (erase r4) \<Longrightarrow>
      retrieve (bder c r4) v = retrieve r4 (injval (erase r4) c v)"
    and P: "\<Turnstile> v : der c (erase (ABACKREF4 bs r1 r2 r3 r4 cs))"
  shows "retrieve (bder c (ABACKREF4 bs r1 r2 r3 r4 cs)) v =
    retrieve (ABACKREF4 bs r1 r2 r3 r4 cs)
      (injval (erase (ABACKREF4 bs r1 r2 r3 r4 cs)) c v)"
  using assms
  apply (cases "bnullable r1"; cases "bnullable r2"; cases "bnullable r3"; cases "rev cs")
                 apply (auto elim!: Prf_elims
                  simp add: Let_def append_assoc bmkeps_retrieve bnullable_correctness
                    retrieve_fuse2 retrieve_fuse2_erase Prf_der_residue_inj retrieve_bder_ARESIDUE
                  split: val.splits if_splits)[1]
                apply (auto elim!: Prf_elims
                  simp add: Let_def append_assoc bmkeps_retrieve bnullable_correctness
                    retrieve_fuse2 retrieve_fuse2_erase Prf_der_residue_inj retrieve_bder_ARESIDUE
                  split: val.splits if_splits)[1]
               apply (auto elim!: Prf_elims
                 simp add: Let_def append_assoc bmkeps_retrieve bnullable_correctness
                   retrieve_fuse2 retrieve_fuse2_erase Prf_der_residue_inj retrieve_bder_ARESIDUE
                 split: val.splits if_splits)[1]
              apply (auto elim!: Prf_elims
                simp add: Let_def append_assoc bmkeps_retrieve bnullable_correctness
                  retrieve_fuse2 retrieve_fuse2_erase Prf_der_residue_inj retrieve_bder_ARESIDUE
                split: val.splits if_splits)[1]
             apply (auto elim!: Prf_elims
               simp add: Let_def append_assoc bmkeps_retrieve bnullable_correctness
                 retrieve_fuse2 retrieve_fuse2_erase Prf_der_residue_inj retrieve_bder_ARESIDUE
               split: val.splits if_splits)[1]
            apply (auto elim!: Prf_elims
              simp add: Let_def append_assoc bmkeps_retrieve bnullable_correctness
                retrieve_fuse2 retrieve_fuse2_erase Prf_der_residue_inj retrieve_bder_ARESIDUE
              split: val.splits if_splits)[1]
           apply (auto elim!: Prf_elims
             simp add: Let_def append_assoc bmkeps_retrieve bnullable_correctness
               retrieve_fuse2 retrieve_fuse2_erase Prf_der_residue_inj retrieve_bder_ARESIDUE
             split: val.splits if_splits)[1]
          apply (auto elim!: Prf_elims
            simp add: Let_def append_assoc bmkeps_retrieve bnullable_correctness
              retrieve_fuse2 retrieve_fuse2_erase Prf_der_residue_inj retrieve_bder_ARESIDUE
            split: val.splits if_splits)[1]
         apply (auto elim!: Prf_elims
           simp add: Let_def append_assoc bmkeps_retrieve bnullable_correctness
             retrieve_fuse2 retrieve_fuse2_erase Prf_der_residue_inj retrieve_bder_ARESIDUE
           split: val.splits if_splits)[1]
        apply (auto elim!: Prf_elims
          simp add: Let_def append_assoc bmkeps_retrieve bnullable_correctness
            retrieve_fuse2 retrieve_fuse2_erase Prf_der_residue_inj retrieve_bder_ARESIDUE
          split: val.splits if_splits)[1]
       apply (auto elim!: Prf_elims
         simp add: Let_def append_assoc bmkeps_retrieve bnullable_correctness
           retrieve_fuse2 retrieve_fuse2_erase Prf_der_residue_inj retrieve_bder_ARESIDUE
         split: val.splits if_splits)[1]
      apply (auto elim!: Prf_elims
        simp add: Let_def append_assoc bmkeps_retrieve bnullable_correctness
          retrieve_fuse2 retrieve_fuse2_erase Prf_der_residue_inj retrieve_bder_ARESIDUE
        split: val.splits if_splits)[1]
     apply (auto elim!: Prf_elims
       simp add: Let_def append_assoc bmkeps_retrieve bnullable_correctness
         retrieve_fuse2 retrieve_fuse2_erase Prf_der_residue_inj retrieve_bder_ARESIDUE
       split: val.splits if_splits)[1]
    apply (auto elim!: Prf_elims
      simp add: Let_def append_assoc bmkeps_retrieve bnullable_correctness
        retrieve_fuse2 retrieve_fuse2_erase Prf_der_residue_inj retrieve_bder_ARESIDUE
      split: val.splits if_splits)[1]
   apply (auto elim!: Prf_elims
     simp add: Let_def append_assoc bmkeps_retrieve bnullable_correctness
       retrieve_fuse2 retrieve_fuse2_erase Prf_der_residue_inj retrieve_bder_ARESIDUE
     split: val.splits if_splits)[1]
  apply (auto elim!: Prf_elims
    simp add: Let_def append_assoc bmkeps_retrieve bnullable_correctness
      retrieve_fuse2 retrieve_fuse2_erase Prf_der_residue_inj retrieve_bder_ARESIDUE
    split: val.splits if_splits)[1]
  done

 

(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend bder_retrieve for the new constructor cases. This is one of the main
   original bitcoded proof obligations. *)
lemma bder_retrieve:
  assumes "\<Turnstile> v : der c (erase r)"
  shows "retrieve (bder c r) v = retrieve r (injval (erase r) c v)"
  using assms  
  apply(induct r arbitrary: v rule: erase.induct)
  using Prf_elims(1) apply auto[1]
  using Prf_elims(1) apply auto[1]
  apply(auto)[1]
  apply(erule Prf_elims)
  apply simp
  using Prf_elims(1) apply blast
  (* AALTs case *)
  apply(simp)
  apply simp
  apply (rule bder_retrieve_AALTs_Cons; assumption)
  (* ASEQ case *) 
  apply(simp)
  apply(case_tac "nullable (erase r1)")
  apply(simp)
  apply(erule Prf_elims)
  using Prf_elims(2) bnullable_correctness apply force
  apply (simp add: bmkeps_retrieve bnullable_correctness retrieve_fuse2)
  apply (simp add: bmkeps_retrieve bnullable_correctness retrieve_fuse2)
  using Prf_elims(2) apply force
  (* ASTAR case *)  
  apply(rename_tac bs r v)
  apply(simp)  
  apply(erule Prf_elims)
  apply(clarify)
  apply(erule Prf_elims)
  apply(clarify)
   apply (simp add: retrieve_fuse2)
  (* ANTIMES case *)
  apply(simp)
  apply(auto)[1]
  apply(erule Prf_elims)
  apply(erule Prf_elims)
  apply(clarify)
  apply(erule Prf_elims)
  apply(clarify)
  apply simp

  (* BACKREF4/HALF/RESIDUE cases *)
  apply (rule bder_retrieve_ABACKREF4; assumption)
  apply (rule bder_retrieve_AHALF; assumption)
  apply (simp add: retrieve_bder_ARESIDUE Prf_der_residue_inj)
  done

(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend MAIN_decode over the new constructor cases after retrieve_code and
   bder_retrieve are repaired. *)
lemma MAIN_decode:
  assumes "\<Turnstile> v : ders s r"
  shows "Some (flex r id s v) = decode (retrieve (bders (intern r) s) v) r"
  using assms
proof (induct s arbitrary: v rule: rev_induct)
  case Nil
  have "\<Turnstile> v : ders [] r" by fact
  then have "\<Turnstile> v : r" by simp
  then have "Some v = decode (retrieve (intern r) v) r"
    using decode_code retrieve_code by auto
  then show "Some (flex r id [] v) = decode (retrieve (bders (intern r) []) v) r"
    by simp
next
  case (snoc c s v)
  have IH: "\<And>v. \<Turnstile> v : ders s r \<Longrightarrow> 
     Some (flex r id s v) = decode (retrieve (bders (intern r) s) v) r" by fact
  have asm: "\<Turnstile> v : ders (s @ [c]) r" by fact
  then have asm2: "\<Turnstile> injval (ders s r) c v : ders s r" 
    by (simp add: Prf_injval ders_append)
  have "Some (flex r id (s @ [c]) v) = Some (flex r id s (injval (ders s r) c v))"
    by (simp add: flex_append)
  also have "... = decode (retrieve (bders (intern r) s) (injval (ders s r) c v)) r"
    using asm2 IH by simp
  also have "... = decode (retrieve (bder c (bders (intern r) s)) v) r"
    using asm by (simp_all add: bder_retrieve ders_append)
  finally show "Some (flex r id (s @ [c]) v) = 
                 decode (retrieve (bders (intern r) (s @ [c])) v) r" by (simp add: bders_append)
qed

definition blexer where
 "blexer r s \<equiv> if bnullable (bders (intern r) s) then 
                decode (bmkeps (bders (intern r) s)) r else None"

(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend the original blexer_correctness theorem. Separate bblexer/gbblexer
   wrappers do not count as bounty. *)
lemma blexer_correctness:
  shows "blexer r s = lexer r s"
proof -
  { define bds where "bds \<equiv> bders (intern r) s"
    define ds  where "ds \<equiv> ders s r"
    assume asm: "nullable ds"
    have era: "erase bds = ds" 
      unfolding ds_def bds_def by simp
    have mke: "\<Turnstile> mkeps ds : ds"
      using asm by (simp add: mkeps_nullable)
    have "decode (bmkeps bds) r = decode (retrieve bds (mkeps ds)) r"
      using bmkeps_retrieve
      using asm era
      using bnullable_correctness by force 
    also have "... =  Some (flex r id s (mkeps ds))"
      using mke by (simp_all add: MAIN_decode ds_def bds_def)
    finally have "decode (bmkeps bds) r = Some (flex r id s (mkeps ds))" 
      unfolding bds_def ds_def .
  }
  then show "blexer r s = lexer r s"
    unfolding blexer_def lexer_flex
    by (auto simp add: bnullable_correctness[symmetric])
qed

end
