
theory ClosedFormsBounds
  imports "GeneralRegexBound" "ClosedForms"
begin
lemma alts_ders_lambda_shape_ders:
  shows "\<forall>r \<in> set (map (\<lambda>r. rders_simp r ( s)) rs ). \<exists>r1 \<in> set rs. r = rders_simp r1 s"
  by (simp add: image_iff)

lemma rlist_bound:
  assumes "\<forall>r \<in> set rs. rsize r \<le> N"
  shows "rsizes rs \<le> N * (length rs)"
  using assms
  apply(induct rs)
  apply simp
  by simp

(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Recheck this bound after the new constructor cases are added to the shared
   size universe and simplifier. Keep the original theorem name and statement
   shape unless admin approves a stronger bound. *)
lemma alts_closed_form_bounded: 
  assumes "\<forall>r \<in> set rs. \<forall>s. rsize (rders_simp r s) \<le> N"
  shows "rsize (rders_simp (RALTS rs) s) \<le> max (Suc (N * (length rs))) (rsize (RALTS rs))"
proof (cases s)
  case Nil
  then show "rsize (rders_simp (RALTS rs) s) \<le> max (Suc (N * length rs)) (rsize (RALTS rs))"
    by simp
next
  case (Cons a s)
  
  from assms have "\<forall>r \<in> set (map (\<lambda>r. rders_simp r (a # s)) rs ). rsize r \<le> N"
    by (metis alts_ders_lambda_shape_ders)
  then have a: "rsizes (map (\<lambda>r. rders_simp r (a # s)) rs ) \<le> N *  (length rs)"
    by (metis length_map rlist_bound) 
     
  have "rsize (rders_simp (RALTS rs) (a # s)) 
          = rsize (rsimp (RALTS (map (\<lambda>r. rders_simp r (a # s)) rs)))"
    by (metis alts_closed_form_variant list.distinct(1)) 
  also have "... \<le> rsize (RALTS (map (\<lambda>r. rders_simp r (a # s)) rs))"
    using rsimp_mono by blast
  also have "... = Suc (rsizes (map (\<lambda>r. rders_simp r (a # s)) rs))"
    by simp
  also have "... \<le> Suc (N * (length rs))"
    using a by blast
  finally have "rsize (rders_simp (RALTS rs) (a # s)) \<le> max (Suc (N * length rs)) (rsize (RALTS rs))" 
    by auto
  then show ?thesis using local.Cons by simp 
qed

lemma alts_simp_ineq_unfold:
  shows "rsize (rsimp (RALTS rs)) \<le> Suc (rsizes (rdistinct (rflts (map rsimp rs)) {}))"
  using rsimp_aalts_smaller by auto


lemma rdistinct_mono_list:
  shows "rsizes (rdistinct (x5 @ rs) rset) \<le> rsizes x5 + rsizes (rdistinct  rs ((set x5 ) \<union> rset))"
  apply(induct x5 arbitrary: rs rset)
   apply simp
  apply(case_tac "a \<in> rset")
   apply simp
   apply (simp add: add.assoc insert_absorb trans_le_add2)
  apply simp
  by (metis Un_insert_right)


lemma flts_size_reduction_alts:
  assumes a: "\<And>noalts_set alts_set corr_set.
           (\<forall>r\<in>noalts_set. \<forall>xs. r \<noteq> RALTS xs) \<and>
           (\<forall>a\<in>alts_set. \<exists>xs. a = RALTS xs \<and> set xs \<subseteq> corr_set) \<Longrightarrow>
           Suc (rsizes (rdistinct (rflts rs) (noalts_set \<union> corr_set)))
           \<le> Suc (rsizes (rdistinct rs (insert RZERO (noalts_set \<union> alts_set))))"
 and b: "\<forall>r\<in>noalts_set. \<forall>xs. r \<noteq> RALTS xs"
 and c: "\<forall>a\<in>alts_set. \<exists>xs. a = RALTS xs \<and> set xs \<subseteq> corr_set"
 and d: "a = RALTS x5"
 shows "rsizes (rdistinct (rflts (a # rs)) (noalts_set \<union> corr_set))
           \<le> rsizes (rdistinct (a # rs) (insert RZERO (noalts_set \<union> alts_set)))"
  
  apply(case_tac "a \<in> alts_set")
  using a b c d
   apply simp
   apply(subgoal_tac "set x5 \<subseteq> corr_set")
  apply(subst rdistinct_concat)
  apply auto[1]
    apply presburger
   apply fastforce
  using a b c d
  apply (subgoal_tac "a \<notin> noalts_set")
  prefer 2
  apply blast
  apply simp
  apply(subgoal_tac "rsizes (rdistinct (x5 @ rflts rs) (noalts_set \<union> corr_set)) 
                   \<le> rsizes x5 + rsizes (rdistinct (rflts rs) ((set x5) \<union> (noalts_set \<union> corr_set)))")
  prefer 2
  using rdistinct_mono_list apply presburger
  apply(subgoal_tac "insert (RALTS x5) (noalts_set \<union> alts_set) = noalts_set \<union> (insert (RALTS x5) alts_set)")
   apply(simp only:)
  apply(subgoal_tac "rsizes x5 + rsizes (rdistinct (rflts rs) (noalts_set \<union> (corr_set \<union> (set x5)))) \<le>
           rsizes x5 + rsizes (rdistinct rs (insert RZERO (noalts_set \<union> insert (RALTS x5) alts_set)))")
  
  apply (simp add: Un_left_commute inf_sup_aci(5))
   apply(subgoal_tac "rsizes (rdistinct (rflts rs) (noalts_set \<union> (corr_set \<union> set x5))) \<le> 
                    rsizes (rdistinct rs (insert RZERO (noalts_set \<union> insert (RALTS x5) alts_set)))")
    apply linarith
   apply(subgoal_tac "\<forall>r \<in> insert (RALTS x5) alts_set. \<exists>xs1.( r = RALTS xs1 \<and> set xs1 \<subseteq> corr_set \<union> set x5)")
    apply presburger
   apply (meson insert_iff sup.cobounded2 sup.coboundedI1)
  by blast



lemma flts_vs_nflts1:
  assumes "\<forall>r \<in> noalts_set. \<forall>xs. r \<noteq> RALTS xs"
  and "\<forall>a \<in> alts_set. (\<exists>xs. a = RALTS xs \<and> set xs \<subseteq> corr_set)" 
  shows "rsizes (rdistinct (rflts rs) (noalts_set \<union> corr_set))
         \<le> rsizes (rdistinct rs (insert RZERO (noalts_set \<union> alts_set)))"
  using assms
    apply(induct rs arbitrary: noalts_set alts_set corr_set)
   apply simp
  apply(case_tac a)
       apply(case_tac "RZERO \<in> noalts_set")
        apply simp
       apply(subgoal_tac "RZERO \<notin> alts_set")
        apply simp
       apply fastforce
      apply(case_tac "RONE \<in> noalts_set")
       apply simp
      apply(subgoal_tac "RONE \<notin> alts_set")
  prefer 2
  apply fastforce
      apply(case_tac "RONE \<in> corr_set")
       apply(subgoal_tac "rflts (a # rs) = RONE # rflts rs")
        apply(simp only:)
        apply(subgoal_tac "rdistinct (RONE # rflts rs) (noalts_set \<union> corr_set) = 
                           rdistinct (rflts rs) (noalts_set \<union> corr_set)")
         apply(simp only:)
  apply(subgoal_tac "rdistinct (RONE # rs) (insert RZERO (noalts_set \<union> alts_set)) =
                     RONE # (rdistinct rs (insert RONE (insert RZERO (noalts_set \<union> alts_set)))) ")
          apply(simp only:)
  apply(subgoal_tac "rdistinct (rflts rs) (noalts_set \<union> corr_set) = 
                     rdistinct (rflts rs) (insert RONE (noalts_set \<union> corr_set))")
  apply (simp only:)
  apply(subgoal_tac "insert RONE (noalts_set \<union> corr_set) = (insert RONE noalts_set) \<union> corr_set")
            apply(simp only:)
  apply(subgoal_tac "insert RONE (insert RZERO (noalts_set \<union> alts_set)) = 
                     insert RZERO ((insert RONE noalts_set) \<union> alts_set)")
             apply(simp only:)
  apply(subgoal_tac "rsizes (rdistinct rs (insert RZERO (insert RONE noalts_set \<union> alts_set)))
                   \<le>  rsizes (RONE # rdistinct rs (insert RZERO (insert RONE noalts_set \<union> alts_set)))")
                apply (smt (verit, ccfv_threshold) dual_order.trans insertE rrexp.distinct)
  apply (metis (no_types, opaque_lifting)  le_add_same_cancel2 list.simps(9) sum_list.Cons zero_le)
            apply fastforce
           apply fastforce
  apply (metis Un_iff insert_absorb)
         apply (metis UnE insertE insert_is_Un rdistinct.simps(2) rrexp.distinct(1))
        apply (meson UnCI rdistinct.simps(2))
  using rflts.simps(4) apply presburger
      apply simp
      apply(subgoal_tac "insert RONE (noalts_set \<union> corr_set) = (insert RONE noalts_set) \<union> corr_set")
        apply(simp only:)
  apply (metis Un_insert_left insertE rrexp.distinct)
      apply fastforce
     apply(case_tac "a \<in> noalts_set")
      apply simp
  apply(subgoal_tac "a \<notin> alts_set")
      prefer 2
      apply blast
  apply(case_tac "a \<in> corr_set")
      apply(subgoal_tac "noalts_set \<union> corr_set = insert a ( noalts_set  \<union> corr_set)")
  prefer 2
  apply fastforce
      apply(simp only:)
      apply(subgoal_tac "rsizes (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set))) \<le>
              rsizes (rdistinct (a # rs) (insert RZERO (noalts_set \<union> alts_set)))")

       apply(subgoal_tac  "rsizes (rdistinct (rflts (a # rs)) ((insert a noalts_set) \<union> corr_set)) \<le>
              rsizes (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set)))")
  apply fastforce
       apply simp
  apply(subgoal_tac "(insert a (noalts_set \<union> alts_set)) = (insert a noalts_set) \<union> alts_set")
        apply(simp only:)
        apply(subgoal_tac "noalts_set \<union> corr_set = (insert a noalts_set) \<union> corr_set")
          apply(simp only:)
  apply (metis insertE nonalt.simps(1) nonalt.simps(4))
        apply blast
  
  apply fastforce
  apply force
      apply simp
  apply (metis Un_insert_left insertE nonalt.simps(1) nonalt.simps(4))
    apply(case_tac "a \<in> noalts_set")
     apply simp
  apply(subgoal_tac "a \<notin> alts_set")
      prefer 2
      apply blast
  apply(case_tac "a \<in> corr_set")
      apply(subgoal_tac "noalts_set \<union> corr_set = insert a ( noalts_set  \<union> corr_set)")
  prefer 2
  apply fastforce
      apply(simp only:)
      apply(subgoal_tac "rsizes (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set))) \<le>
             rsizes (rdistinct (a # rs) (insert RZERO (noalts_set \<union> alts_set)))")

       apply(subgoal_tac "rsizes (rdistinct (rflts (a # rs)) ((insert a noalts_set) \<union> corr_set)) \<le>
          rsizes (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set)))")
  apply fastforce
       apply simp
  apply(subgoal_tac "(insert a (noalts_set \<union> alts_set)) = (insert a noalts_set) \<union> alts_set")
        apply(simp only:)
        apply(subgoal_tac "noalts_set \<union> corr_set = (insert a noalts_set) \<union> corr_set")
  apply(simp only:)

         apply (metis insertE rrexp.distinct)
  apply blast
  apply fastforce
  apply force
     apply simp
  
    apply (metis Un_insert_left insertE rrexp.distinct)

  using Suc_le_mono flts_size_reduction_alts apply presburger



     apply(case_tac "a \<in> noalts_set")
      apply simp
  apply(subgoal_tac "a \<notin> alts_set")
      prefer 2
      apply blast
  apply(case_tac "a \<in> corr_set")
      apply(subgoal_tac "noalts_set \<union> corr_set = insert a ( noalts_set  \<union> corr_set)")
  prefer 2
  apply fastforce
      apply(simp only:)
      apply(subgoal_tac "rsizes (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set))) \<le>
               rsizes (rdistinct (a # rs) (insert RZERO (noalts_set \<union> alts_set)))")

       apply(subgoal_tac "rsizes (rdistinct (rflts (a # rs)) ((insert a noalts_set) \<union> corr_set)) \<le>
          rsizes (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set)))")
  apply fastforce
       apply simp
  apply(subgoal_tac "(insert a (noalts_set \<union> alts_set)) = (insert a noalts_set) \<union> alts_set")
        apply(simp only:)
        apply(subgoal_tac "noalts_set \<union> corr_set = (insert a noalts_set) \<union> corr_set")
       apply(simp only:)
  apply (metis insertE rrexp.distinct)

        apply blast
  
  apply fastforce
  apply force
     apply simp
    apply (metis Un_insert_left insert_iff rrexp.distinct)




  apply(case_tac "a \<in> noalts_set")
      apply simp
  apply(subgoal_tac "a \<notin> alts_set")
     prefer 2
      apply blast
  apply(case_tac "a \<in> corr_set")
      apply(subgoal_tac "noalts_set \<union> corr_set = insert a ( noalts_set  \<union> corr_set)")
  prefer 2
  apply fastforce
   apply(simp only:)
   apply(subgoal_tac "rsizes (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set))) \<le>
               rsizes (rdistinct (a # rs) (insert RZERO (noalts_set \<union> alts_set)))")

       apply(subgoal_tac "rsizes (rdistinct (rflts (a # rs)) ((insert a noalts_set) \<union> corr_set)) \<le>
          rsizes (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set)))")
  apply fastforce
       apply simp
  apply(subgoal_tac "(insert a (noalts_set \<union> alts_set)) = (insert a noalts_set) \<union> alts_set")
        apply(simp only:)
        apply(subgoal_tac "noalts_set \<union> corr_set = (insert a noalts_set) \<union> corr_set")
       apply(simp only:)
  apply (metis insertE nonalt.simps)
  apply blast
  apply blast
  apply force
   apply(auto)[1]
   apply (metis Un_insert_left insertE nonalt.simps)




  apply(case_tac "a \<in> noalts_set")
      apply simp
  apply(subgoal_tac "a \<notin> alts_set")
     prefer 2
      apply blast
  apply(case_tac "a \<in> corr_set")
      apply(subgoal_tac "noalts_set \<union> corr_set = insert a ( noalts_set  \<union> corr_set)")
  prefer 2
  apply fastforce
   apply(simp only:)
   apply(subgoal_tac "rsizes (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set))) \<le>
               rsizes (rdistinct (a # rs) (insert RZERO (noalts_set \<union> alts_set)))")

       apply(subgoal_tac "rsizes (rdistinct (rflts (a # rs)) ((insert a noalts_set) \<union> corr_set)) \<le>
          rsizes (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set)))")
  apply fastforce
       apply simp
  apply(subgoal_tac "(insert a (noalts_set \<union> alts_set)) = (insert a noalts_set) \<union> alts_set")
        apply(simp only:)
        apply(subgoal_tac "noalts_set \<union> corr_set = (insert a noalts_set) \<union> corr_set")
       apply(simp only:)
  apply (metis insertE nonalt.simps)
  apply blast
  apply blast
  apply force
   apply(auto)[1]
   apply (metis Un_insert_left insertE nonalt.simps)




  apply(case_tac "a \<in> noalts_set")
      apply simp
  apply(subgoal_tac "a \<notin> alts_set")
     prefer 2
      apply blast
  apply(case_tac "a \<in> corr_set")
      apply(subgoal_tac "noalts_set \<union> corr_set = insert a ( noalts_set  \<union> corr_set)")
  prefer 2
  apply fastforce
   apply(simp only:)
   apply(subgoal_tac "rsizes (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set))) \<le>
               rsizes (rdistinct (a # rs) (insert RZERO (noalts_set \<union> alts_set)))")

       apply(subgoal_tac "rsizes (rdistinct (rflts (a # rs)) ((insert a noalts_set) \<union> corr_set)) \<le>
          rsizes (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set)))")
  apply fastforce
       apply simp
  apply(subgoal_tac "(insert a (noalts_set \<union> alts_set)) = (insert a noalts_set) \<union> alts_set")
        apply(simp only:)
        apply(subgoal_tac "noalts_set \<union> corr_set = (insert a noalts_set) \<union> corr_set")
       apply(simp only:)
  apply (metis insertE nonalt.simps)
  apply blast
  apply blast
  apply force
   apply(auto)[1]
   apply (metis Un_insert_left insertE nonalt.simps)




  apply(case_tac "a \<in> noalts_set")
      apply simp
  apply(subgoal_tac "a \<notin> alts_set")
     prefer 2
      apply blast
  apply(case_tac "a \<in> corr_set")
      apply(subgoal_tac "noalts_set \<union> corr_set = insert a ( noalts_set  \<union> corr_set)")
  prefer 2
  apply fastforce
   apply(simp only:)
   apply(subgoal_tac "rsizes (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set))) \<le>
               rsizes (rdistinct (a # rs) (insert RZERO (noalts_set \<union> alts_set)))")

       apply(subgoal_tac "rsizes (rdistinct (rflts (a # rs)) ((insert a noalts_set) \<union> corr_set)) \<le>
          rsizes (rdistinct (a # rs) (insert RZERO ((insert a noalts_set) \<union> alts_set)))")
  apply fastforce
       apply simp
  apply(subgoal_tac "(insert a (noalts_set \<union> alts_set)) = (insert a noalts_set) \<union> alts_set")
        apply(simp only:)
        apply(subgoal_tac "noalts_set \<union> corr_set = (insert a noalts_set) \<union> corr_set")
       apply(simp only:)
  apply (metis insertE nonalt.simps)
  apply blast
  apply blast
  apply force
   apply(auto)[1]
   apply (metis Un_insert_left insertE nonalt.simps)
  done




lemma flts_vs_nflts:
  assumes "\<forall>r \<in> noalts_set. \<forall>xs. r \<noteq> RALTS xs"
  and "\<forall>a \<in> alts_set. (\<exists>xs. a = RALTS xs \<and> set xs \<subseteq> corr_set)"
  shows "rsizes (rdistinct (rflts rs) (noalts_set \<union> corr_set))
         \<le> rsizes (rdistinct rs (insert RZERO (noalts_set \<union> alts_set)))"
  by (simp add: assms flts_vs_nflts1)

lemma distinct_simp_ineq_general:
  assumes "rsimp ` no_simp = has_simp" "finite no_simp"
  shows "rsizes (rdistinct (map rsimp rs) has_simp) \<le> rsizes (rdistinct rs no_simp)"
  using assms
  apply(induct rs no_simp arbitrary: has_simp rule: rdistinct.induct)
  apply simp
  apply(auto)
  using add_le_mono rsimp_mono by presburger

lemma larger_acc_smaller_distinct_res0:
  assumes "ss \<subseteq> SS"
  shows "rsizes (rdistinct rs SS) \<le> rsizes (rdistinct rs ss)"
  using assms
  apply(induct rs arbitrary: ss SS)
   apply simp
  by (metis distinct_early_app1 rdistinct_smaller)

lemma without_flts_ineq:
  shows "rsizes (rdistinct (rflts rs) {}) \<le> rsizes (rdistinct rs {})"
proof -
  have "rsizes (rdistinct (rflts rs) {}) \<le>  rsizes (rdistinct rs (insert RZERO {}))"
    by (metis empty_iff flts_vs_nflts sup_bot_left)
  also have "... \<le>  rsizes (rdistinct rs {})" 
    by (simp add: larger_acc_smaller_distinct_res0)
  finally show ?thesis
    by blast
qed


lemma distinct_simp_ineq:
  shows "rsizes (rdistinct (map rsimp rs) {}) \<le> rsizes (rdistinct rs {})"
  using distinct_simp_ineq_general by blast


lemma alts_simp_control:
  shows "rsize (rsimp (RALTS rs)) \<le> Suc (rsizes (rdistinct rs {}))"
proof -
  have "rsize (rsimp (RALTS rs)) \<le> Suc (rsizes (rdistinct (rflts (map rsimp rs)) {}))"
     using alts_simp_ineq_unfold by auto
   moreover have "\<dots> \<le> Suc (rsizes (rdistinct (map rsimp rs) {}))"
    using without_flts_ineq by blast
  ultimately show "rsize (rsimp (RALTS rs)) \<le> Suc (rsizes (rdistinct rs {}))"
    by (meson Suc_le_mono distinct_simp_ineq le_trans)
qed


lemma larger_acc_smaller_distinct_res:
  shows "rsizes (rdistinct rs (insert a ss)) \<le> rsizes (rdistinct rs ss)"
  by (simp add: larger_acc_smaller_distinct_res0 subset_insertI)

lemma triangle_inequality_distinct:
  shows "rsizes (rdistinct (a # rs) ss) \<le> rsize a + rsizes (rdistinct rs ss)"
  apply(case_tac "a \<in> ss")
   apply simp
  by (simp add: larger_acc_smaller_distinct_res)


lemma distinct_list_size_len_bounded:
  assumes "\<forall>r \<in> set rs. rsize r \<le> N" "length rs \<le> lrs"
  shows "rsizes rs \<le> lrs * N "
  using assms
  by (metis rlist_bound dual_order.trans mult.commute mult_le_mono1)



lemma rdistinct_same_set:
  shows "r \<in> set rs \<longleftrightarrow> r \<in> set (rdistinct rs {})"
  apply(induct rs)
   apply simp
  by (metis rdistinct_set_equality)

(* distinct_list_rexp_up_to_certain_size_bouded_by_set_enumerating_up_to_that_size *)
lemma distinct_list_rexp_upto:
  assumes size: "\<forall>r\<in> set rs. (rsize r) \<le> N"
      and legacy: "\<forall>r\<in> set rs. legacy_rrexp r"
  shows "rsizes (rdistinct rs {}) \<le> (card (sizeNregex N)) * N"
proof -
  have distinct: "distinct (rdistinct rs {})"
    using rdistinct_does_the_job by blast
  have elems_size: "\<forall>r \<in> set (rdistinct rs {}). rsize r \<le> N"
    using size by (simp add: rdistinct_set_equality)
  have elems_legacy: "\<forall>r \<in> set (rdistinct rs {}). legacy_rrexp r"
    using legacy by (simp add: rdistinct_set_equality)
  have subset: "set (rdistinct rs {}) \<subseteq> sizeNregex N"
    using elems_size elems_legacy unfolding sizeNregex_def by blast
  have len_le: "length (rdistinct rs {}) \<le> card (sizeNregex N)"
  proof -
    have "card (set (rdistinct rs {})) \<le> card (sizeNregex N)"
      by (rule card_mono[OF finite_size_n subset])
    then show ?thesis
      using distinct by (simp add: distinct_card)
  qed
  show ?thesis
    by (rule distinct_list_size_len_bounded) (use elems_size len_le in auto)
qed


lemma star_control_bounded:
  assumes size: "\<forall>s. rsize (rders_simp r s) \<le> N"
      and legacy: "\<forall>s. legacy_rrexp (rders_simp r s)"
  shows "rsizes (rdistinct (map (\<lambda>s1. RSEQ (rders_simp r s1) (RSTAR r)) (star_updates s r [[c]])) {}) 
     \<le> (card (sizeNregex (Suc (N + rsize (RSTAR r))))) * (Suc (N + rsize (RSTAR r)))"
proof -
  let ?rs = "map (\<lambda>s1. RSEQ (rders_simp r s1) (RSTAR r)) (star_updates s r [[c]])"
  let ?N = "Suc (N + rsize (RSTAR r))"
  have elems_size: "\<forall>r' \<in> set ?rs. rsize r' \<le> ?N"
    using size by auto
  have legacy_r: "legacy_rrexp r"
    using legacy[rule_format, of "[]"] by simp
  have elems_legacy: "\<forall>r' \<in> set ?rs. legacy_rrexp r'"
    using legacy legacy_r by auto
  show ?thesis
    using distinct_list_rexp_upto[OF elems_size elems_legacy] .
qed


(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Recheck this bound after the new constructor cases are added to the shared
   size universe and simplifier. Keep the original theorem name and statement
   shape unless admin approves a stronger bound. *)
lemma star_closed_form_bounded:
  assumes "\<forall>s. rsize (rders_simp r s) \<le> N"
      and "\<forall>s. legacy_rrexp (rders_simp r s)"
  shows "rsize (rders_simp (RSTAR r) s) \<le> 
           max ((Suc (card (sizeNregex (Suc (N + rsize (RSTAR r))))) * (Suc (N + rsize (RSTAR r))))) (rsize (RSTAR r))"
proof(cases s)
  case Nil
  then show "rsize (rders_simp (RSTAR r) s)
    \<le> max (Suc (card (sizeNregex (Suc (N + rsize (RSTAR r))))) * Suc (N + rsize (RSTAR r))) (rsize (RSTAR r))" 
    by simp
next
  case (Cons a list)
  then have "rsize (rders_simp (RSTAR r) s) = 
    rsize (rsimp (RALTS ((map (\<lambda>s1. RSEQ (rders_simp r s1) (RSTAR r)) (star_updates list r [[a]])))))"
    using star_closed_form by fastforce
  also have "... \<le> Suc (rsizes (rdistinct (map (\<lambda>s1. RSEQ (rders_simp r s1) (RSTAR r)) (star_updates list r [[a]])) {}))"
    using alts_simp_control by blast 
  also have "... \<le> Suc (card (sizeNregex (Suc (N + rsize (RSTAR r))))) * (Suc (N + rsize (RSTAR r)))" 
    using star_control_bounded[OF assms] by (metis add_mono le_add1 mult_Suc plus_1_eq_Suc)
  also have "... \<le> max (Suc (card (sizeNregex (Suc (N + rsize (RSTAR r))))) * Suc (N + rsize (RSTAR r))) (rsize (RSTAR r))"
    by simp    
  finally show ?thesis by simp  
qed


thm ntimes_closed_form

thm rsize.simps

lemma nupdates_snoc:
  shows " (nupdates (xs @ [x]) r optlist) = nupdate x r (nupdates xs r optlist)"
  by (simp add: nupdates_append)

lemma nupdate_elems:
  shows "\<forall>opt \<in> set (nupdate c r optlist). opt = None \<or> (\<exists>s n. opt = Some (s, n))"
  using nonempty_string.cases by auto

lemma nupdates_elems:
  shows "\<forall>opt \<in> set (nupdates s r optlist). opt = None \<or> (\<exists>s n. opt = Some (s, n))"
  by (meson nonempty_string.cases)


lemma opterm_optlist_result_shape:
  shows "\<forall>r' \<in> set (map (optermsimp r) optlist). r' = RZERO \<or> (\<exists>s m. r' = RSEQ (rders_simp r s) (RNTIMES r m))"
  apply(induct optlist)
   apply simp
  apply(case_tac a)
  apply simp+
  by fastforce


lemma opterm_optlist_result_shape2:
  shows "\<And>optlist. \<forall>r' \<in> set (map (optermsimp r) optlist). r' = RZERO \<or> (\<exists>s m. r' = RSEQ (rders_simp r s) (RNTIMES r m))"  
  using opterm_optlist_result_shape by presburger


lemma nupdate_n_leq_n:
  shows "\<forall>r \<in> set (nupdate c' r [Some ([c], n)]). r = None \<or>( \<exists>s' m. r = Some (s', m) \<and> m \<le> n)"
  apply(case_tac n)
   apply simp
  apply simp
  done
(*
lemma nupdate_induct_leqn:
  shows "\<lbrakk>\<forall>opt \<in> set optlist. opt = None \<or> (\<exists>s' m. opt = Some(s', m) \<and> m \<le> n) \<rbrakk> \<Longrightarrow> 
       \<forall>opt \<in> set (nupdate c' r optlist). opt = None \<or> (\<exists>s' m. opt = Some (s', m) \<and> m \<le> n)"
  apply (case_tac optlist)
   apply simp
  apply(case_tac a)
   apply simp
  sledgehammer
*)


lemma nupdates_n_leq_n:
  shows "\<forall>r \<in> set (nupdates s r [Some ([c], n)]). r = None \<or>( \<exists>s' m. r = Some (s', m) \<and> m \<le> n)"
  apply(induct s rule: rev_induct)
   apply simp
  apply(subst nupdates_append)
  by (metis nupdates_elems_leqn nupdates_snoc)
  


lemma ntimes_closed_form_list_elem_shape:
  shows "\<forall>r' \<in> set (map (optermsimp r) (nupdates s r [Some ([c], n)])). 
r' = RZERO \<or> (\<exists>s' m. r' = RSEQ (rders_simp r s') (RNTIMES r m) \<and> m \<le> n)"
  apply(insert opterm_optlist_result_shape2)
  apply(case_tac s)
   apply(auto)
  apply (metis rders_simp_one_char)
  by (metis case_prod_conv nupdates.simps(2) nupdates_n_leq_n option.simps(4) option.simps(5))

thm nupdates_n_leq_n

lemma ntimes_trivial1:
  shows "rsize RZERO \<le> N + rsize (RNTIMES r n)"
  by simp


lemma ntimes_trivial20:
  shows "m \<le> n \<Longrightarrow> rsize (RNTIMES r m) \<le> rsize (RNTIMES r n)"
  by simp


lemma ntimes_trivial2:
  assumes "\<forall>s. rsize (rders_simp r s) \<le> N"
  shows "    r' = RSEQ (rders_simp r s1) (RNTIMES r m) \<and> m \<le> n
       \<Longrightarrow> rsize r' \<le> Suc (N + rsize (RNTIMES r n))"
  apply simp
  by (simp add: add_mono_thms_linordered_semiring(1) assms)

lemma ntimes_closed_form_list_elem_bounded:
  assumes "\<forall>s. rsize (rders_simp r s) \<le> N"
  shows "\<forall>r' \<in>  set  (map (optermsimp r) (nupdates s r [Some ([c], n)])). rsize r' \<le> Suc (N + rsize (RNTIMES r n))"
  apply(rule ballI)
  apply(subgoal_tac  "r' = RZERO \<or> (\<exists>s' m. r' = RSEQ (rders_simp r s') (RNTIMES r m) \<and> m \<le> n)")
  prefer 2
  using ntimes_closed_form_list_elem_shape apply blast
  apply(case_tac "r' = RZERO")
  using le_SucI ntimes_trivial1 apply presburger
  apply(subgoal_tac "\<exists>s1 m. r' = RSEQ (rders_simp r s1) (RNTIMES r m) \<and> m \<le> n")
  apply(erule exE)+
  using assms ntimes_trivial2 apply presburger
  by blast

lemma ntimes_closed_form_list_elem_legacy:
  assumes "\<forall>s. legacy_rrexp (rders_simp r s)"
  shows "\<forall>r' \<in> set (map (optermsimp r) (nupdates s r [Some ([c], n)])). legacy_rrexp r'"
proof (rule ballI)
  fix r'
  assume in_set: "r' \<in> set (map (optermsimp r) (nupdates s r [Some ([c], n)]))"
  have shape:
    "r' = RZERO \<or> (\<exists>s' m. r' = RSEQ (rders_simp r s') (RNTIMES r m) \<and> m \<le> n)"
    using ntimes_closed_form_list_elem_shape in_set by blast
  have legacy_r: "legacy_rrexp r"
    using assms[rule_format, of "[]"] by simp
  show "legacy_rrexp r'"
    using shape assms legacy_r by auto
qed


lemma P_holds_after_distinct:
  assumes "\<forall>r \<in> set rs. P r"
  shows "\<forall>r \<in> set (rdistinct rs rset). P r"
  by (simp add: assms rdistinct_set_equality1)

lemma ntimes_control_bounded:
  assumes size: "\<forall>s. rsize (rders_simp r s) \<le> N"
      and legacy: "\<forall>s. legacy_rrexp (rders_simp r s)"
  shows "rsizes (rdistinct (map (optermsimp r) (nupdates s r [Some ([c], n)])) {}) 
     \<le> (card (sizeNregex (Suc (N + rsize (RNTIMES r n))))) * (Suc (N + rsize (RNTIMES r n)))"
proof -
  let ?rs = "map (optermsimp r) (nupdates s r [Some ([c], n)])"
  let ?N = "Suc (N + rsize (RNTIMES r n))"
  have elems_size: "\<forall>r' \<in> set ?rs. rsize r' \<le> ?N"
    using ntimes_closed_form_list_elem_bounded[OF size] by blast
  have elems_legacy: "\<forall>r' \<in> set ?rs. legacy_rrexp r'"
    using ntimes_closed_form_list_elem_legacy[OF legacy] by blast
  show ?thesis
    using distinct_list_rexp_upto[OF elems_size elems_legacy] .
qed



lemma ntimes_closed_form_bounded0:
  assumes "\<forall>s. rsize (rders_simp r s) \<le> N"
  shows " (rders_simp (RNTIMES r 0) s)  = RZERO \<or> (rders_simp (RNTIMES r 0) s)  = RNTIMES r 0
           "
  apply(induct s)
   apply simp
  by (metis always0 list.simps(3) rder.simps(7) rders.simps(2) rders_simp_same_simpders rsimp.simps(3))

lemma ntimes_closed_form_bounded1:
  assumes "\<forall>s. rsize (rders_simp r s) \<le> N"
  shows " rsize (rders_simp (RNTIMES r 0) s) \<le> max (rsize  RZERO) (rsize (RNTIMES r 0))"
  
  by (metis assms max.cobounded1 max.cobounded2 ntimes_closed_form_bounded0)

lemma self_smaller_than_bound:
  shows "\<forall>s. rsize (rders_simp r s) \<le> N \<Longrightarrow> rsize r \<le> N"
  apply(drule_tac x = "[]" in spec)
  apply simp
  done

lemma ntimes_closed_form_bounded_nil_aux:
  shows "max (rsize  RZERO) (rsize (RNTIMES r 0)) = 1 + rsize r"
  by auto

lemma ntimes_closed_form_bounded_nil:
  assumes "\<forall>s. rsize (rders_simp r s) \<le> N"
  shows " rsize (rders_simp (RNTIMES r 0) s) \<le> 1 + rsize r"
  using assms ntimes_closed_form_bounded1 by auto

lemma ntimes_ineq1:
  shows "(rsize (RNTIMES r n)) \<ge> 1 + rsize r"
  by simp

lemma ntimes_ineq2:
  shows "1 + rsize r \<le>  
max ((Suc (card (sizeNregex (Suc (N + rsize (RNTIMES r n))))) * (Suc (N + rsize (RNTIMES r n))))) (rsize (RNTIMES r n))"
  by (meson le_max_iff_disj ntimes_ineq1)

lemma ntimes_closed_form_bounded:
  assumes "\<forall>s. rsize (rders_simp r s) \<le> N"
      and "\<forall>s. legacy_rrexp (rders_simp r s)"
  shows "rsize (rders_simp (RNTIMES r (Suc n)) s) \<le> 
           max ((Suc (card (sizeNregex (Suc (N + rsize (RNTIMES r n))))) * (Suc (N + rsize (RNTIMES r n))))) (rsize (RNTIMES r n))"
proof(cases s)
  case Nil
  then show "rsize (rders_simp (RNTIMES r (Suc n)) s)
    \<le> max (Suc (card (sizeNregex (Suc (N + rsize (RNTIMES r n))))) * Suc (N + rsize (RNTIMES r n))) (rsize (RNTIMES r n))" 
    by simp
next
  case (Cons a list)

  then have "rsize (rders_simp (RNTIMES r (Suc n)) s) = 
             rsize (rsimp (RALTS ((map (optermsimp r)    (nupdates list r [Some ([a], n)])))))"
    using ntimes_closed_form by fastforce
  also have "... \<le> Suc (rsizes (rdistinct ((map (optermsimp r) (nupdates list r [Some ([a], n)]))) {}))"
    using alts_simp_control by blast 
  also have "... \<le> Suc (card (sizeNregex (Suc (N + rsize (RNTIMES r n))))) * (Suc (N + rsize (RNTIMES r n)))" 
    using ntimes_control_bounded[OF assms]
    by (metis add_mono le_add1 mult_Suc plus_1_eq_Suc)
  also have "... \<le> max (Suc (card (sizeNregex (Suc (N + rsize (RNTIMES r n))))) * Suc (N + rsize (RNTIMES r n))) (rsize (RNTIMES r n))"
    by simp    
  finally show ?thesis by simp  
qed


(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Recheck this bound after the new constructor cases are added to the shared
   size universe and simplifier. Keep the original theorem name and statement
   shape unless admin approves a stronger bound. *)
lemma ntimes_closed_form_boundedA:
  assumes "\<forall>s. rsize (rders_simp r s) \<le> N"
      and "\<forall>s. legacy_rrexp (rders_simp r s)"
  shows "\<exists>N'. \<forall>s. rsize (rders_simp (RNTIMES r n) s) \<le> N'"
  apply(case_tac n)
  using assms ntimes_closed_form_bounded_nil apply blast
  using assms ntimes_closed_form_bounded by blast


lemma star_closed_form_nonempty_bounded:
  assumes "\<forall>s. rsize (rders_simp r s) \<le> N"
      and "\<forall>s. legacy_rrexp (rders_simp r s)"
      and "s \<noteq> []"
  shows "rsize (rders_simp (RSTAR r) s) \<le> 
            ((Suc (card (sizeNregex (Suc (N + rsize (RSTAR r))))) * (Suc (N + rsize (RSTAR r))))) "
proof(cases s)
  case Nil
  then show ?thesis 
    using local.Nil by fastforce
next
  case (Cons a list)
  then have "rsize (rders_simp (RSTAR r) s) = 
    rsize (rsimp (RALTS ((map (\<lambda>s1. RSEQ (rders_simp r s1) (RSTAR r)) (star_updates list r [[a]])))))"
    using star_closed_form by fastforce
  also have "... \<le> Suc (rsizes (rdistinct (map (\<lambda>s1. RSEQ (rders_simp r s1) (RSTAR r)) (star_updates list r [[a]])) {}))"
    using alts_simp_control by blast 
  also have "... \<le> Suc (card (sizeNregex (Suc (N + rsize (RSTAR r))))) * (Suc (N + rsize (RSTAR r)))" 
    using star_control_bounded[OF assms(1,2)]
    by (metis add_mono le_add1 mult_Suc plus_1_eq_Suc)
  also have "... \<le> max (Suc (card (sizeNregex (Suc (N + rsize (RSTAR r))))) * Suc (N + rsize (RSTAR r))) (rsize (RSTAR r))"
    by simp    
  finally show ?thesis by simp  
qed



lemma seq_estimate_bounded: 
  assumes "\<forall>s. rsize (rders_simp r1 s) \<le> N1" 
      and "\<forall>s. rsize (rders_simp r2 s) \<le> N2"
      and "\<forall>s. legacy_rrexp (rders_simp r2 s)"
  shows
    "rsizes (rdistinct (RSEQ (rders_simp r1 s) r2 # map (rders_simp r2) (vsuf s r1)) {}) 
       \<le> (Suc (N1 + (rsize r2)) + (N2 * card (sizeNregex N2)))"
proof -
  have elems_size: "\<forall>r \<in> set (map (rders_simp r2) (vsuf s r1)). rsize r \<le> N2"
    using assms(2) by auto
  have elems_legacy: "\<forall>r \<in> set (map (rders_simp r2) (vsuf s r1)). legacy_rrexp r"
    using assms(3) by auto
  have a: "rsizes (rdistinct (map (rders_simp r2) (vsuf s r1)) {}) \<le> N2 * card (sizeNregex N2)"
    using distinct_list_rexp_upto[OF elems_size elems_legacy] by (simp add: mult.commute)

  have "rsizes (rdistinct (RSEQ (rders_simp r1 s) r2 # map (rders_simp r2) (vsuf s r1)) {}) \<le>
          rsize (RSEQ (rders_simp r1 s) r2) + rsizes (rdistinct (map (rders_simp r2) (vsuf s r1)) {})"
    using triangle_inequality_distinct by blast    
  also have "... \<le> rsize (RSEQ (rders_simp r1 s) r2) + N2 * card (sizeNregex N2)"
    by (simp add: a)
  also have "... \<le> Suc (N1 + (rsize r2) + N2 * card (sizeNregex N2))"
    by (simp add: assms(1))
  finally show ?thesis
    by force
qed    


(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Recheck this bound after the new constructor cases are added to the shared
   size universe and simplifier. Keep the original theorem name and statement
   shape unless admin approves a stronger bound. *)
lemma seq_closed_form_bounded2: 
  assumes "\<forall>s. rsize (rders_simp r1 s) \<le> N1"
  and     "\<forall>s. rsize (rders_simp r2 s) \<le> N2"
  and     "\<forall>s. legacy_rrexp (rders_simp r2 s)"
shows "rsize (rders_simp (RSEQ r1 r2) s) 
          \<le> max (2 + N1 + (rsize r2) + (N2 * card (sizeNregex N2))) (rsize (RSEQ r1 r2))"
proof(cases s)
  case Nil
  then show "rsize (rders_simp (RSEQ r1 r2) s)
     \<le> max (2 + N1 + (rsize r2) + (N2 * card (sizeNregex N2))) (rsize (RSEQ r1 r2))" 
    by simp
next
  case (Cons a list)
  then have "rsize (rders_simp (RSEQ r1 r2) s) = 
    rsize (rsimp (RALTS ((RSEQ (rders_simp r1 s) r2) # (map (rders_simp r2) (vsuf s r1)))))" 
    using seq_closed_form_variant by (metis list.distinct(1)) 
  also have "... \<le> Suc (rsizes (rdistinct (RSEQ (rders_simp r1 s) r2 # map (rders_simp r2) (vsuf s r1)) {}))"
    using alts_simp_control by blast
  also have "... \<le> 2 + N1 + (rsize r2) + (N2 * card (sizeNregex N2))"
  using seq_estimate_bounded[OF assms] by auto
  ultimately show "rsize (rders_simp (RSEQ r1 r2) s)
       \<le> max (2 + N1 + (rsize r2) + N2 * card (sizeNregex N2)) (rsize (RSEQ r1 r2))"
    by auto 
qed

lemma list_rders_simp_bounded:
  assumes "\<forall>r \<in> set rs. \<exists>N. \<forall>s. rsize (rders_simp r s) \<le> N"
  shows "\<exists>N. \<forall>r \<in> set rs. \<forall>s. rsize (rders_simp r s) \<le> N"
  using assms
proof (induction rs)
  case Nil
  then show ?case
    by auto
next
  case (Cons r rs)
  then obtain N1 where N1: "\<forall>s. rsize (rders_simp r s) \<le> N1"
    by auto
  from Cons obtain N2 where N2: "\<forall>r \<in> set rs. \<forall>s. rsize (rders_simp r s) \<le> N2"
    by auto
  show ?case
  proof (intro exI[of _ "max N1 N2"] ballI allI)
    fix ra s
    assume "ra \<in> set (r # rs)"
    then consider "ra = r" | "ra \<in> set rs"
      by auto
    then show "rsize (rders_simp ra s) \<le> max N1 N2"
    proof cases
      case 1
      then show ?thesis
        using N1 max.cobounded1 order_trans by blast
    next
      case 2
      then show ?thesis
        using N2 max.cobounded2 order_trans by blast
    qed
  qed
qed

(* BACKREF-MIGRATION-TODO (bounds invariant):
   This is the original regular-expression boundedness theorem, now made
   explicit about its legacy skeleton invariant. Backreference payload states
   need a separate payload-aware or quotient-based bound; proving the old
   unrestricted statement would be false because strings are unbounded while
   rsize intentionally ignores payload length. *)
lemma rders_simp_bounded: 
  assumes legacy: "legacy_rrexp r"
  shows "\<exists>N. \<forall>s. rsize (rders_simp r s) \<le> N"
  using legacy
proof (induction r)
  case RZERO
  then show ?case
    using three_easy_cases0 by blast
next
  case RONE
  then show ?case
    using three_easy_cases1 by blast
next
  case (RCHAR c)
  then show ?case
    using three_easy_casesC by blast
next
  case (RALTS rs)
  then have elem_bounds: "\<forall>r \<in> set rs. \<exists>N. \<forall>s. rsize (rders_simp r s) \<le> N"
    by auto
  then obtain N where N: "\<forall>r \<in> set rs. \<forall>s. rsize (rders_simp r s) \<le> N"
    using list_rders_simp_bounded by blast
  show ?case
    using alts_closed_form_bounded[OF N] by blast
next
  case (RSEQ r1 r2)
  then obtain N1 where N1: "\<forall>s. rsize (rders_simp r1 s) \<le> N1"
    by auto
  from RSEQ obtain N2 where N2: "\<forall>s. rsize (rders_simp r2 s) \<le> N2"
    by auto
  have L2: "\<forall>s. legacy_rrexp (rders_simp r2 s)"
    using RSEQ.prems legacy_rders_simp by auto
  show ?case
    using seq_closed_form_bounded2[OF N1 N2 L2] by blast
next
  case (RSTAR r)
  then obtain N where N: "\<forall>s. rsize (rders_simp r s) \<le> N"
    by auto
  have L: "\<forall>s. legacy_rrexp (rders_simp r s)"
    using RSTAR.prems legacy_rders_simp by auto
  show ?case
    using star_closed_form_bounded[OF N L] by blast
next
  case (RNTIMES r n)
  then obtain N where N: "\<forall>s. rsize (rders_simp r s) \<le> N"
    by auto
  have L: "\<forall>s. legacy_rrexp (rders_simp r s)"
    using RNTIMES.prems legacy_rders_simp by auto
  show ?case
    using ntimes_closed_form_boundedA[OF N L] by blast
qed simp_all

end
