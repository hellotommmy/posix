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

end
