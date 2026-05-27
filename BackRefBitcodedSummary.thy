theory BackRefBitcodedSummary
  imports BackRefBlexer BackRefGBlexer
begin

section \<open>Bitcoded lexer summary facts\<close>

theorem bblexer_frontends_eq:
  "bblexer r s = bblexer_simp r s"
  "bblexer r s = bblexer_step_simp r s"
  "bblexer_simp r s = bblexer_step_simp r s"
  by (simp_all add: bblexer_simp_correctness bblexer_step_simp_correctness
      bblexer_simp_step_simp_eq)

theorem bblexer_frontends_blexer_retrieve:
  "bblexer r s = map_option (bretrieve (baintern r)) (blexer r s)"
  "bblexer_simp r s = map_option (bretrieve (baintern r)) (blexer r s)"
  "bblexer_step_simp r s = map_option (bretrieve (baintern r)) (blexer r s)"
  by (simp_all add: bblexer_blexer_retrieve bblexer_simp_blexer_retrieve
      bblexer_step_simp_blexer_retrieve)

theorem bblexer_frontends_blexer_Some_retrieve:
  assumes "blexer r s = Some v"
  shows "bblexer r s = Some (bretrieve (baintern r) v)"
    and "bblexer_simp r s = Some (bretrieve (baintern r) v)"
    and "bblexer_step_simp r s = Some (bretrieve (baintern r) v)"
  using assms by (simp_all add: bblexer_blexer_retrieve
      bblexer_simp_blexer_retrieve bblexer_step_simp_blexer_retrieve)

theorem bblexer_frontends_blexer_iff:
  "bblexer r s = Some bs \<longleftrightarrow>
    (\<exists>v. blexer r s = Some v \<and> bs = bretrieve (baintern r) v)"
  "bblexer_simp r s = Some bs \<longleftrightarrow>
    (\<exists>v. blexer r s = Some v \<and> bs = bretrieve (baintern r) v)"
  "bblexer_step_simp r s = Some bs \<longleftrightarrow>
    (\<exists>v. blexer r s = Some v \<and> bs = bretrieve (baintern r) v)"
  "bblexer r s = None \<longleftrightarrow> blexer r s = None"
  "bblexer_simp r s = None \<longleftrightarrow> blexer r s = None"
  "bblexer_step_simp r s = None \<longleftrightarrow> blexer r s = None"
  by (simp_all add: bblexer_Some_blexer_iff
      bblexer_simp_Some_blexer_iff bblexer_step_simp_Some_blexer_iff
      bblexer_None_blexer_iff bblexer_simp_None_blexer_iff
      bblexer_step_simp_None_blexer_iff)

theorem bblexer_frontends_POSIX_retrieve:
  assumes "s \<in> r \<rightarrow> v"
  shows "bblexer r s = Some (bretrieve (baintern r) v)"
    and "bblexer_simp r s = Some (bretrieve (baintern r) v)"
    and "bblexer_step_simp r s = Some (bretrieve (baintern r) v)"
  using assms by (simp_all add: bblexer_POSIX_retrieve
      bblexer_simp_POSIX_retrieve bblexer_step_simp_POSIX_retrieve)

theorem bblexer_frontends_POSIX_retrieve_iff:
  "bblexer r s = Some bs \<longleftrightarrow>
    (\<exists>v. s \<in> r \<rightarrow> v \<and> bs = bretrieve (baintern r) v)"
  "bblexer_simp r s = Some bs \<longleftrightarrow>
    (\<exists>v. s \<in> r \<rightarrow> v \<and> bs = bretrieve (baintern r) v)"
  "bblexer_step_simp r s = Some bs \<longleftrightarrow>
    (\<exists>v. s \<in> r \<rightarrow> v \<and> bs = bretrieve (baintern r) v)"
  by (simp_all add: bblexer_POSIX_retrieve_iff
      bblexer_simp_POSIX_retrieve_iff bblexer_step_simp_POSIX_retrieve_iff)

theorem bblexer_frontends_BPrf_retrieve_iff:
  "bblexer r s = Some bs \<longleftrightarrow>
    (\<exists>v. blexer r s = Some v \<and> \<Turnstile>b v : r \<and> bflat v = s \<and>
      bs = bretrieve (baintern r) v)"
  "bblexer_simp r s = Some bs \<longleftrightarrow>
    (\<exists>v. blexer r s = Some v \<and> \<Turnstile>b v : r \<and> bflat v = s \<and>
      bs = bretrieve (baintern r) v)"
  "bblexer_step_simp r s = Some bs \<longleftrightarrow>
    (\<exists>v. blexer r s = Some v \<and> \<Turnstile>b v : r \<and> bflat v = s \<and>
      bs = bretrieve (baintern r) v)"
  by (simp_all add: bblexer_BPrf_retrieve_iff
      bblexer_simp_BPrf_retrieve_iff bblexer_step_simp_BPrf_retrieve_iff)

theorem bblexer_frontends_defined_POSIX_iff:
  "(\<exists>bs. bblexer r s = Some bs) \<longleftrightarrow> (\<exists>v. s \<in> r \<rightarrow> v)"
  "(\<exists>bs. bblexer_simp r s = Some bs) \<longleftrightarrow> (\<exists>v. s \<in> r \<rightarrow> v)"
  "(\<exists>bs. bblexer_step_simp r s = Some bs) \<longleftrightarrow> (\<exists>v. s \<in> r \<rightarrow> v)"
  by (simp_all add: bblexer_defined_POSIX_iff
      bblexer_simp_defined_POSIX_iff bblexer_step_simp_defined_POSIX_iff)

theorem bblexer_frontends_defined_BPrf_iff:
  "(\<exists>bs. bblexer r s = Some bs) \<longleftrightarrow>
    (\<exists>v. \<Turnstile>b v : r \<and> bflat v = s)"
  "(\<exists>bs. bblexer_simp r s = Some bs) \<longleftrightarrow>
    (\<exists>v. \<Turnstile>b v : r \<and> bflat v = s)"
  "(\<exists>bs. bblexer_step_simp r s = Some bs) \<longleftrightarrow>
    (\<exists>v. \<Turnstile>b v : r \<and> bflat v = s)"
  by (simp_all add: bblexer_defined_BPrf_iff
      bblexer_simp_defined_BPrf_iff bblexer_step_simp_defined_BPrf_iff)

theorem bblexer_frontends_None_POSIX_iff:
  "bblexer r s = None \<longleftrightarrow> \<not> (\<exists>v. s \<in> r \<rightarrow> v)"
  "bblexer_simp r s = None \<longleftrightarrow> \<not> (\<exists>v. s \<in> r \<rightarrow> v)"
  "bblexer_step_simp r s = None \<longleftrightarrow> \<not> (\<exists>v. s \<in> r \<rightarrow> v)"
  by (simp_all add: bblexer_None_POSIX_iff
      bblexer_simp_None_POSIX_iff bblexer_step_simp_None_POSIX_iff)

theorem bblexer_frontends_None_BPrf_iff:
  "bblexer r s = None \<longleftrightarrow>
    \<not> (\<exists>v. \<Turnstile>b v : r \<and> bflat v = s)"
  "bblexer_simp r s = None \<longleftrightarrow>
    \<not> (\<exists>v. \<Turnstile>b v : r \<and> bflat v = s)"
  "bblexer_step_simp r s = None \<longleftrightarrow>
    \<not> (\<exists>v. \<Turnstile>b v : r \<and> bflat v = s)"
  by (simp_all add: bblexer_None_BPrf_iff
      bblexer_simp_None_BPrf_iff bblexer_step_simp_None_BPrf_iff)

theorem bblexer_frontends_final_membership:
  "bblexer r s =
    (if s \<in> BL r
     then Some (bretrieve (bbders (baintern r) s) (bmkeps (xders r s)))
     else None)"
  "bblexer_simp r s =
    (if s \<in> BL r
     then Some (bretrieve (bbsimp (bbders (baintern r) s)) (bmkeps (xders r s)))
     else None)"
  "bblexer_step_simp r s =
    (if s \<in> BL r
     then Some (bretrieve (bbders_simp (baintern r) s) (bmkeps (xders r s)))
     else None)"
  by (simp_all add: bblexer_final_membership bblexer_simp_final_membership
      bblexer_step_simp_final_membership)

theorem bblexer_frontends_final_same:
  "bblexer r s =
    (if s \<in> BL r
     then Some (bretrieve (bbders (baintern r) s) (bmkeps (xders r s)))
     else None)"
  "bblexer_simp r s =
    (if s \<in> BL r
     then Some (bretrieve (bbders (baintern r) s) (bmkeps (xders r s)))
     else None)"
  "bblexer_step_simp r s =
    (if s \<in> BL r
     then Some (bretrieve (bbders (baintern r) s) (bmkeps (xders r s)))
     else None)"
  by (simp_all add: bblexer_final_membership bblexer_simp_correctness
      bblexer_step_simp_correctness)

theorem bblexer_frontends_BL_same_iff:
  "bblexer r s = Some bs \<longleftrightarrow>
    s \<in> BL r \<and>
    bs = bretrieve (bbders (baintern r) s) (bmkeps (xders r s))"
  "bblexer_simp r s = Some bs \<longleftrightarrow>
    s \<in> BL r \<and>
    bs = bretrieve (bbders (baintern r) s) (bmkeps (xders r s))"
  "bblexer_step_simp r s = Some bs \<longleftrightarrow>
    s \<in> BL r \<and>
    bs = bretrieve (bbders (baintern r) s) (bmkeps (xders r s))"
  by (auto simp add: bblexer_frontends_final_same split: if_splits)

theorem bblexer_frontends_BL_iff:
  "bblexer r s = None \<longleftrightarrow> s \<notin> BL r"
  "bblexer_simp r s = None \<longleftrightarrow> s \<notin> BL r"
  "bblexer_step_simp r s = None \<longleftrightarrow> s \<notin> BL r"
  "bblexer r s = Some bs \<longleftrightarrow>
    s \<in> BL r \<and>
    bs = bretrieve (bbders (baintern r) s) (bmkeps (xders r s))"
  "bblexer_simp r s = Some bs \<longleftrightarrow>
    s \<in> BL r \<and>
    bs = bretrieve (bbsimp (bbders (baintern r) s)) (bmkeps (xders r s))"
  "bblexer_step_simp r s = Some bs \<longleftrightarrow>
    s \<in> BL r \<and>
    bs = bretrieve (bbders_simp (baintern r) s) (bmkeps (xders r s))"
  by (simp_all add: bblexer_None_iff bblexer_simp_None_iff
      bblexer_step_simp_None_iff bblexer_Some_iff bblexer_simp_Some_iff
      bblexer_step_simp_Some_iff)

theorem bblexer_frontends_defined_BL_iff:
  "(\<exists>bs. bblexer r s = Some bs) \<longleftrightarrow> s \<in> BL r"
  "(\<exists>bs. bblexer_simp r s = Some bs) \<longleftrightarrow> s \<in> BL r"
  "(\<exists>bs. bblexer_step_simp r s = Some bs) \<longleftrightarrow> s \<in> BL r"
  by (simp_all add: bblexer_defined_iff bblexer_simp_defined_iff
      bblexer_step_simp_defined_iff)

theorem bblexer_frontends_Some_BL:
  "bblexer r s = Some bs \<Longrightarrow> s \<in> BL r"
  "bblexer_simp r s = Some bs \<Longrightarrow> s \<in> BL r"
  "bblexer_step_simp r s = Some bs \<Longrightarrow> s \<in> BL r"
  by (auto simp add: bblexer_frontends_BL_iff)

theorem bblexer_frontends_BL_obtains:
  assumes "s \<in> BL r"
  obtains bs1 bs2 bs3 where "bblexer r s = Some bs1"
    and "bblexer_simp r s = Some bs2"
    and "bblexer_step_simp r s = Some bs3"
proof -
  from assms obtain bs1 where bs1: "bblexer r s = Some bs1"
    using bblexer_frontends_defined_BL_iff(1) by blast
  from assms obtain bs2 where bs2: "bblexer_simp r s = Some bs2"
    using bblexer_frontends_defined_BL_iff(2) by blast
  from assms obtain bs3 where bs3: "bblexer_step_simp r s = Some bs3"
    using bblexer_frontends_defined_BL_iff(3) by blast
  show thesis by (rule that[OF bs1 bs2 bs3])
qed

theorem bblexer_frontends_BL_obtains_same:
  assumes "s \<in> BL r"
  obtains bs where "bblexer r s = Some bs"
    and "bblexer_simp r s = Some bs"
    and "bblexer_step_simp r s = Some bs"
proof -
  from assms obtain bs where bs: "bblexer r s = Some bs"
    using bblexer_frontends_defined_BL_iff(1) by blast
  then have simp: "bblexer_simp r s = Some bs"
    by (simp add: bblexer_frontends_eq)
  from bs have step_simp: "bblexer_step_simp r s = Some bs"
    by (simp add: bblexer_frontends_eq)
  show thesis by (rule that[OF bs simp step_simp])
qed

theorem bblexer_frontends_BL_cases:
  obtains (reject) "s \<notin> BL r"
    "bblexer r s = None"
    "bblexer_simp r s = None"
    "bblexer_step_simp r s = None"
  | (accept) bs where "s \<in> BL r"
    "bblexer r s = Some bs"
    "bblexer_simp r s = Some bs"
    "bblexer_step_simp r s = Some bs"
proof (cases "s \<in> BL r")
  case True
  then obtain bs where bs: "bblexer r s = Some bs"
    and simp: "bblexer_simp r s = Some bs"
    and step_simp: "bblexer_step_simp r s = Some bs"
    by (rule bblexer_frontends_BL_obtains_same)
  show thesis by (rule accept[OF True bs simp step_simp])
next
  case False
  have none: "bblexer r s = None"
    using False by (simp add: bblexer_frontends_BL_iff(1))
  have simp_none: "bblexer_simp r s = None"
    using False by (simp add: bblexer_frontends_BL_iff(2))
  have step_simp_none: "bblexer_step_simp r s = None"
    using False by (simp add: bblexer_frontends_BL_iff(3))
  show thesis by (rule reject[OF False none simp_none step_simp_none])
qed

theorem bblexer_frontends_all_None_iff:
  "bblexer r s = None \<and>
    bblexer_simp r s = None \<and>
    bblexer_step_simp r s = None \<longleftrightarrow> s \<notin> BL r"
  by (auto simp add: bblexer_frontends_BL_iff)

theorem bblexer_frontends_same_Some_iff:
  "(\<exists>bs. bblexer r s = Some bs \<and>
    bblexer_simp r s = Some bs \<and>
    bblexer_step_simp r s = Some bs) \<longleftrightarrow> s \<in> BL r"
proof
  assume "\<exists>bs. bblexer r s = Some bs \<and>
    bblexer_simp r s = Some bs \<and>
    bblexer_step_simp r s = Some bs"
  then show "s \<in> BL r"
    by (auto intro: bblexer_frontends_Some_BL(1))
next
  assume "s \<in> BL r"
  then show "\<exists>bs. bblexer r s = Some bs \<and>
    bblexer_simp r s = Some bs \<and>
    bblexer_step_simp r s = Some bs"
    using bblexer_frontends_BL_obtains_same by blast
qed

theorem bblexer_frontends_xnullable_iff:
  "bblexer r s = None \<longleftrightarrow> \<not> xnullable (xders r s)"
  "bblexer_simp r s = None \<longleftrightarrow> \<not> xnullable (xders r s)"
  "bblexer_step_simp r s = None \<longleftrightarrow> \<not> xnullable (xders r s)"
  "bblexer r s = Some bs \<longleftrightarrow>
    xnullable (xders r s) \<and>
    bs = bretrieve (bbders (baintern r) s) (bmkeps (xders r s))"
  "bblexer_simp r s = Some bs \<longleftrightarrow>
    xnullable (xders r s) \<and>
    bs = bretrieve (bbsimp (bbders (baintern r) s)) (bmkeps (xders r s))"
  "bblexer_step_simp r s = Some bs \<longleftrightarrow>
    xnullable (xders r s) \<and>
    bs = bretrieve (bbders_simp (baintern r) s) (bmkeps (xders r s))"
  by (simp_all add: bblexer_None_xnullable_iff
      bblexer_simp_None_xnullable_iff bblexer_step_simp_None_xnullable_iff
      bblexer_Some_xnullable_iff bblexer_simp_Some_xnullable_iff
      bblexer_step_simp_Some_xnullable_iff)

theorem bblexer_frontends_xnullable_same_iff:
  "bblexer r s = None \<and>
    bblexer_simp r s = None \<and>
    bblexer_step_simp r s = None \<longleftrightarrow> \<not> xnullable (xders r s)"
  "(\<exists>bs. bblexer r s = Some bs \<and>
    bblexer_simp r s = Some bs \<and>
    bblexer_step_simp r s = Some bs) \<longleftrightarrow> xnullable (xders r s)"
proof -
  show "bblexer r s = None \<and>
      bblexer_simp r s = None \<and>
      bblexer_step_simp r s = None \<longleftrightarrow> \<not> xnullable (xders r s)"
    by (simp add: bblexer_frontends_xnullable_iff)
  show "(\<exists>bs. bblexer r s = Some bs \<and>
      bblexer_simp r s = Some bs \<and>
      bblexer_step_simp r s = Some bs) \<longleftrightarrow> xnullable (xders r s)"
  proof
    assume "\<exists>bs. bblexer r s = Some bs \<and>
      bblexer_simp r s = Some bs \<and>
      bblexer_step_simp r s = Some bs"
    then show "xnullable (xders r s)"
      by (auto simp add: bblexer_frontends_xnullable_iff)
  next
    assume nullable: "xnullable (xders r s)"
    let ?bs = "bretrieve (bbders (baintern r) s) (bmkeps (xders r s))"
    have b: "bblexer r s = Some ?bs"
      using nullable by (simp add: bblexer_frontends_xnullable_iff)
    then have simp: "bblexer_simp r s = Some ?bs"
      by (simp add: bblexer_frontends_eq)
    from b have step_simp: "bblexer_step_simp r s = Some ?bs"
      by (simp add: bblexer_frontends_eq)
    show "\<exists>bs. bblexer r s = Some bs \<and>
      bblexer_simp r s = Some bs \<and>
      bblexer_step_simp r s = Some bs"
      using b simp step_simp by blast
  qed
qed

theorem bblexer_frontends_BL_final_cases:
  obtains (reject) "s \<notin> BL r"
    "bblexer r s = None"
    "bblexer_simp r s = None"
    "bblexer_step_simp r s = None"
  | (accept) "s \<in> BL r"
    "bblexer r s =
      Some (bretrieve (bbders (baintern r) s) (bmkeps (xders r s)))"
    "bblexer_simp r s =
      Some (bretrieve (bbders (baintern r) s) (bmkeps (xders r s)))"
    "bblexer_step_simp r s =
      Some (bretrieve (bbders (baintern r) s) (bmkeps (xders r s)))"
proof (cases "s \<in> BL r")
  case True
  have b: "bblexer r s =
      Some (bretrieve (bbders (baintern r) s) (bmkeps (xders r s)))"
    using True by (simp add: bblexer_frontends_final_same)
  have simp: "bblexer_simp r s =
      Some (bretrieve (bbders (baintern r) s) (bmkeps (xders r s)))"
    using True by (simp add: bblexer_frontends_final_same)
  have step_simp: "bblexer_step_simp r s =
      Some (bretrieve (bbders (baintern r) s) (bmkeps (xders r s)))"
    using True by (simp add: bblexer_frontends_final_same)
  show thesis by (rule accept[OF True b simp step_simp])
next
  case False
  have none: "bblexer r s = None"
    using False by (simp add: bblexer_frontends_final_same)
  have simp_none: "bblexer_simp r s = None"
    using False by (simp add: bblexer_frontends_final_same)
  have step_simp_none: "bblexer_step_simp r s = None"
    using False by (simp add: bblexer_frontends_final_same)
  show thesis by (rule reject[OF False none simp_none step_simp_none])
qed

theorem gbblexer_frontends_eq:
  "gbblexer r s = gbblexer_simp r s"
  "gbblexer r s = gbblexer_step_simp r s"
  "gbblexer_simp r s = gbblexer_step_simp r s"
  by (simp_all add: gbblexer_simp_correctness gbblexer_step_simp_correctness
      gbblexer_simp_step_simp_eq)

theorem gbblexer_frontends_gblexer_retrieve:
  "gbblexer r s = map_option (gretrieve (gaintern r)) (gblexer r s)"
  "gbblexer_simp r s = map_option (gretrieve (gaintern r)) (gblexer r s)"
  "gbblexer_step_simp r s =
    map_option (gretrieve (gaintern r)) (gblexer r s)"
  by (simp_all add: gbblexer_gblexer_retrieve
      gbblexer_simp_gblexer_retrieve gbblexer_step_simp_gblexer_retrieve)

theorem gbblexer_frontends_gblexer_Some_retrieve:
  assumes "gblexer r s = Some v"
  shows "gbblexer r s = Some (gretrieve (gaintern r) v)"
    and "gbblexer_simp r s = Some (gretrieve (gaintern r) v)"
    and "gbblexer_step_simp r s = Some (gretrieve (gaintern r) v)"
  using assms by (simp_all add: gbblexer_gblexer_retrieve
      gbblexer_simp_gblexer_retrieve gbblexer_step_simp_gblexer_retrieve)

theorem gbblexer_frontends_gblexer_iff:
  "gbblexer r s = Some bs \<longleftrightarrow>
    (\<exists>v. gblexer r s = Some v \<and> bs = gretrieve (gaintern r) v)"
  "gbblexer_simp r s = Some bs \<longleftrightarrow>
    (\<exists>v. gblexer r s = Some v \<and> bs = gretrieve (gaintern r) v)"
  "gbblexer_step_simp r s = Some bs \<longleftrightarrow>
    (\<exists>v. gblexer r s = Some v \<and> bs = gretrieve (gaintern r) v)"
  "gbblexer r s = None \<longleftrightarrow> gblexer r s = None"
  "gbblexer_simp r s = None \<longleftrightarrow> gblexer r s = None"
  "gbblexer_step_simp r s = None \<longleftrightarrow> gblexer r s = None"
  by (simp_all add: gbblexer_Some_gblexer_iff
      gbblexer_simp_Some_gblexer_iff gbblexer_step_simp_Some_gblexer_iff
      gbblexer_None_gblexer_iff gbblexer_simp_None_gblexer_iff
      gbblexer_step_simp_None_gblexer_iff)

theorem gbblexer_frontends_GPrf_retrieve_iff:
  "gbblexer r s = Some bs \<longleftrightarrow>
    (\<exists>v. gblexer r s = Some v \<and> \<Turnstile>g v : r \<and> gflat v = s \<and>
      bs = gretrieve (gaintern r) v)"
  "gbblexer_simp r s = Some bs \<longleftrightarrow>
    (\<exists>v. gblexer r s = Some v \<and> \<Turnstile>g v : r \<and> gflat v = s \<and>
      bs = gretrieve (gaintern r) v)"
  "gbblexer_step_simp r s = Some bs \<longleftrightarrow>
    (\<exists>v. gblexer r s = Some v \<and> \<Turnstile>g v : r \<and> gflat v = s \<and>
      bs = gretrieve (gaintern r) v)"
  by (simp_all add: gbblexer_GPrf_retrieve_iff
      gbblexer_simp_GPrf_retrieve_iff gbblexer_step_simp_GPrf_retrieve_iff)

theorem gbblexer_frontends_defined_GPrf_iff:
  "(\<exists>bs. gbblexer r s = Some bs) \<longleftrightarrow>
    (\<exists>v. \<Turnstile>g v : r \<and> gflat v = s)"
  "(\<exists>bs. gbblexer_simp r s = Some bs) \<longleftrightarrow>
    (\<exists>v. \<Turnstile>g v : r \<and> gflat v = s)"
  "(\<exists>bs. gbblexer_step_simp r s = Some bs) \<longleftrightarrow>
    (\<exists>v. \<Turnstile>g v : r \<and> gflat v = s)"
  by (simp_all add: gbblexer_defined_GPrf_iff
      gbblexer_simp_defined_GPrf_iff gbblexer_step_simp_defined_GPrf_iff)

theorem gbblexer_frontends_None_GPrf_iff:
  "gbblexer r s = None \<longleftrightarrow>
    \<not> (\<exists>v. \<Turnstile>g v : r \<and> gflat v = s)"
  "gbblexer_simp r s = None \<longleftrightarrow>
    \<not> (\<exists>v. \<Turnstile>g v : r \<and> gflat v = s)"
  "gbblexer_step_simp r s = None \<longleftrightarrow>
    \<not> (\<exists>v. \<Turnstile>g v : r \<and> gflat v = s)"
  by (simp_all add: gbblexer_None_GPrf_iff
      gbblexer_simp_None_GPrf_iff gbblexer_step_simp_None_GPrf_iff)

theorem gbblexer_frontends_final_membership:
  "gbblexer r s =
    (if s \<in> GBL r
     then Some (gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s)))
     else None)"
  "gbblexer_simp r s =
    (if s \<in> GBL r
     then Some (gretrieve (gabbsimp (gabders (gaintern r) s)) (gmkeps (gxders r s)))
     else None)"
  "gbblexer_step_simp r s =
    (if s \<in> GBL r
     then Some (gretrieve (gabders_simp (gaintern r) s) (gmkeps (gxders r s)))
     else None)"
  by (simp_all add: gbblexer_final_membership gbblexer_simp_final_membership
      gbblexer_step_simp_final_membership)

theorem gbblexer_frontends_final_same:
  "gbblexer r s =
    (if s \<in> GBL r
     then Some (gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s)))
     else None)"
  "gbblexer_simp r s =
    (if s \<in> GBL r
     then Some (gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s)))
     else None)"
  "gbblexer_step_simp r s =
    (if s \<in> GBL r
     then Some (gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s)))
     else None)"
  by (simp_all add: gbblexer_final_membership gbblexer_simp_correctness
      gbblexer_step_simp_correctness)

theorem gbblexer_frontends_GBL_same_iff:
  "gbblexer r s = Some bs \<longleftrightarrow>
    s \<in> GBL r \<and>
    bs = gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s))"
  "gbblexer_simp r s = Some bs \<longleftrightarrow>
    s \<in> GBL r \<and>
    bs = gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s))"
  "gbblexer_step_simp r s = Some bs \<longleftrightarrow>
    s \<in> GBL r \<and>
    bs = gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s))"
  by (auto simp add: gbblexer_frontends_final_same split: if_splits)

theorem gbblexer_frontends_GBL_iff:
  "gbblexer r s = None \<longleftrightarrow> s \<notin> GBL r"
  "gbblexer_simp r s = None \<longleftrightarrow> s \<notin> GBL r"
  "gbblexer_step_simp r s = None \<longleftrightarrow> s \<notin> GBL r"
  "gbblexer r s = Some bs \<longleftrightarrow>
    s \<in> GBL r \<and>
    bs = gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s))"
  "gbblexer_simp r s = Some bs \<longleftrightarrow>
    s \<in> GBL r \<and>
    bs = gretrieve (gabbsimp (gabders (gaintern r) s)) (gmkeps (gxders r s))"
  "gbblexer_step_simp r s = Some bs \<longleftrightarrow>
    s \<in> GBL r \<and>
    bs = gretrieve (gabders_simp (gaintern r) s) (gmkeps (gxders r s))"
  by (simp_all add: gbblexer_None_iff gbblexer_simp_None_iff
      gbblexer_step_simp_None_iff gbblexer_Some_iff gbblexer_simp_Some_iff
      gbblexer_step_simp_Some_iff)

theorem gbblexer_frontends_defined_GBL_iff:
  "(\<exists>bs. gbblexer r s = Some bs) \<longleftrightarrow> s \<in> GBL r"
  "(\<exists>bs. gbblexer_simp r s = Some bs) \<longleftrightarrow> s \<in> GBL r"
  "(\<exists>bs. gbblexer_step_simp r s = Some bs) \<longleftrightarrow> s \<in> GBL r"
  by (simp_all add: gbblexer_defined_iff gbblexer_simp_defined_iff
      gbblexer_step_simp_defined_iff)

theorem gbblexer_frontends_Some_GBL:
  "gbblexer r s = Some bs \<Longrightarrow> s \<in> GBL r"
  "gbblexer_simp r s = Some bs \<Longrightarrow> s \<in> GBL r"
  "gbblexer_step_simp r s = Some bs \<Longrightarrow> s \<in> GBL r"
  by (auto simp add: gbblexer_frontends_GBL_iff)

theorem gbblexer_frontends_GBL_obtains:
  assumes "s \<in> GBL r"
  obtains bs1 bs2 bs3 where "gbblexer r s = Some bs1"
    and "gbblexer_simp r s = Some bs2"
    and "gbblexer_step_simp r s = Some bs3"
proof -
  from assms obtain bs1 where bs1: "gbblexer r s = Some bs1"
    using gbblexer_frontends_defined_GBL_iff(1) by blast
  from assms obtain bs2 where bs2: "gbblexer_simp r s = Some bs2"
    using gbblexer_frontends_defined_GBL_iff(2) by blast
  from assms obtain bs3 where bs3: "gbblexer_step_simp r s = Some bs3"
    using gbblexer_frontends_defined_GBL_iff(3) by blast
  show thesis by (rule that[OF bs1 bs2 bs3])
qed

theorem gbblexer_frontends_GBL_obtains_same:
  assumes "s \<in> GBL r"
  obtains bs where "gbblexer r s = Some bs"
    and "gbblexer_simp r s = Some bs"
    and "gbblexer_step_simp r s = Some bs"
proof -
  from assms obtain bs where bs: "gbblexer r s = Some bs"
    using gbblexer_frontends_defined_GBL_iff(1) by blast
  then have simp: "gbblexer_simp r s = Some bs"
    by (simp add: gbblexer_frontends_eq)
  from bs have step_simp: "gbblexer_step_simp r s = Some bs"
    by (simp add: gbblexer_frontends_eq)
  show thesis by (rule that[OF bs simp step_simp])
qed

theorem gbblexer_frontends_GBL_cases:
  obtains (reject) "s \<notin> GBL r"
    "gbblexer r s = None"
    "gbblexer_simp r s = None"
    "gbblexer_step_simp r s = None"
  | (accept) bs where "s \<in> GBL r"
    "gbblexer r s = Some bs"
    "gbblexer_simp r s = Some bs"
    "gbblexer_step_simp r s = Some bs"
proof (cases "s \<in> GBL r")
  case True
  then obtain bs where bs: "gbblexer r s = Some bs"
    and simp: "gbblexer_simp r s = Some bs"
    and step_simp: "gbblexer_step_simp r s = Some bs"
    by (rule gbblexer_frontends_GBL_obtains_same)
  show thesis by (rule accept[OF True bs simp step_simp])
next
  case False
  have none: "gbblexer r s = None"
    using False by (simp add: gbblexer_frontends_GBL_iff(1))
  have simp_none: "gbblexer_simp r s = None"
    using False by (simp add: gbblexer_frontends_GBL_iff(2))
  have step_simp_none: "gbblexer_step_simp r s = None"
    using False by (simp add: gbblexer_frontends_GBL_iff(3))
  show thesis by (rule reject[OF False none simp_none step_simp_none])
qed

theorem gbblexer_frontends_all_None_iff:
  "gbblexer r s = None \<and>
    gbblexer_simp r s = None \<and>
    gbblexer_step_simp r s = None \<longleftrightarrow> s \<notin> GBL r"
  by (auto simp add: gbblexer_frontends_GBL_iff)

theorem gbblexer_frontends_same_Some_iff:
  "(\<exists>bs. gbblexer r s = Some bs \<and>
    gbblexer_simp r s = Some bs \<and>
    gbblexer_step_simp r s = Some bs) \<longleftrightarrow> s \<in> GBL r"
proof
  assume "\<exists>bs. gbblexer r s = Some bs \<and>
    gbblexer_simp r s = Some bs \<and>
    gbblexer_step_simp r s = Some bs"
  then show "s \<in> GBL r"
    by (auto intro: gbblexer_frontends_Some_GBL(1))
next
  assume "s \<in> GBL r"
  then show "\<exists>bs. gbblexer r s = Some bs \<and>
    gbblexer_simp r s = Some bs \<and>
    gbblexer_step_simp r s = Some bs"
    using gbblexer_frontends_GBL_obtains_same by blast
qed

theorem gbblexer_frontends_gnullable_iff:
  "gbblexer r s = None \<longleftrightarrow> \<not> gnullable (gxders r s)"
  "gbblexer_simp r s = None \<longleftrightarrow> \<not> gnullable (gxders r s)"
  "gbblexer_step_simp r s = None \<longleftrightarrow> \<not> gnullable (gxders r s)"
  "gbblexer r s = Some bs \<longleftrightarrow>
    gnullable (gxders r s) \<and>
    bs = gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s))"
  "gbblexer_simp r s = Some bs \<longleftrightarrow>
    gnullable (gxders r s) \<and>
    bs = gretrieve (gabbsimp (gabders (gaintern r) s)) (gmkeps (gxders r s))"
  "gbblexer_step_simp r s = Some bs \<longleftrightarrow>
    gnullable (gxders r s) \<and>
    bs = gretrieve (gabders_simp (gaintern r) s) (gmkeps (gxders r s))"
  by (simp_all add: gbblexer_None_gnullable_iff
      gbblexer_simp_None_gnullable_iff gbblexer_step_simp_None_gnullable_iff
      gbblexer_Some_gnullable_iff gbblexer_simp_Some_gnullable_iff
      gbblexer_step_simp_Some_gnullable_iff)

theorem gbblexer_frontends_gnullable_same_iff:
  "gbblexer r s = None \<and>
    gbblexer_simp r s = None \<and>
    gbblexer_step_simp r s = None \<longleftrightarrow> \<not> gnullable (gxders r s)"
  "(\<exists>bs. gbblexer r s = Some bs \<and>
    gbblexer_simp r s = Some bs \<and>
    gbblexer_step_simp r s = Some bs) \<longleftrightarrow> gnullable (gxders r s)"
proof -
  show "gbblexer r s = None \<and>
      gbblexer_simp r s = None \<and>
      gbblexer_step_simp r s = None \<longleftrightarrow> \<not> gnullable (gxders r s)"
    by (simp add: gbblexer_frontends_gnullable_iff)
  show "(\<exists>bs. gbblexer r s = Some bs \<and>
      gbblexer_simp r s = Some bs \<and>
      gbblexer_step_simp r s = Some bs) \<longleftrightarrow> gnullable (gxders r s)"
  proof
    assume "\<exists>bs. gbblexer r s = Some bs \<and>
      gbblexer_simp r s = Some bs \<and>
      gbblexer_step_simp r s = Some bs"
    then show "gnullable (gxders r s)"
      by (auto simp add: gbblexer_frontends_gnullable_iff)
  next
    assume nullable: "gnullable (gxders r s)"
    let ?bs = "gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s))"
    have b: "gbblexer r s = Some ?bs"
      using nullable by (simp add: gbblexer_frontends_gnullable_iff)
    then have simp: "gbblexer_simp r s = Some ?bs"
      by (simp add: gbblexer_frontends_eq)
    from b have step_simp: "gbblexer_step_simp r s = Some ?bs"
      by (simp add: gbblexer_frontends_eq)
    show "\<exists>bs. gbblexer r s = Some bs \<and>
      gbblexer_simp r s = Some bs \<and>
      gbblexer_step_simp r s = Some bs"
      using b simp step_simp by blast
  qed
qed

theorem gbblexer_frontends_GBL_final_cases:
  obtains (reject) "s \<notin> GBL r"
    "gbblexer r s = None"
    "gbblexer_simp r s = None"
    "gbblexer_step_simp r s = None"
  | (accept) "s \<in> GBL r"
    "gbblexer r s =
      Some (gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s)))"
    "gbblexer_simp r s =
      Some (gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s)))"
    "gbblexer_step_simp r s =
      Some (gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s)))"
proof (cases "s \<in> GBL r")
  case True
  have b: "gbblexer r s =
      Some (gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s)))"
    using True by (simp add: gbblexer_frontends_final_same)
  have simp: "gbblexer_simp r s =
      Some (gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s)))"
    using True by (simp add: gbblexer_frontends_final_same)
  have step_simp: "gbblexer_step_simp r s =
      Some (gretrieve (gabders (gaintern r) s) (gmkeps (gxders r s)))"
    using True by (simp add: gbblexer_frontends_final_same)
  show thesis by (rule accept[OF True b simp step_simp])
next
  case False
  have none: "gbblexer r s = None"
    using False by (simp add: gbblexer_frontends_final_same)
  have simp_none: "gbblexer_simp r s = None"
    using False by (simp add: gbblexer_frontends_final_same)
  have step_simp_none: "gbblexer_step_simp r s = None"
    using False by (simp add: gbblexer_frontends_final_same)
  show thesis by (rule reject[OF False none simp_none step_simp_none])
qed

end
