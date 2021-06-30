(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchArch_AC
imports Arch_AC
begin

text\<open>

Arch-specific access control.

\<close>

context Arch begin global_naming RISCV64

named_theorems Arch_AC_assms

lemma set_mrs_state_vrefs[Arch_AC_assms, wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and (\<lambda>s. P (state_vrefs s))\<rbrace>
   set_mrs thread buf msgs
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_mrs_def split_def set_object_def get_object_def split del: if_split)
  apply (wpsimp wp: gets_the_wp get_wp put_wp mapM_x_wp'
              simp: zipWithM_x_mapM_x split_def store_word_offs_def
         split_del: if_split)
  apply (subst state_vrefs_eqI)
        prefer 7
        apply assumption
       apply (clarsimp simp: opt_map_def)
      apply (fastforce simp: opt_map_def aobj_of_def)
     apply clarsimp
    apply (auto simp: valid_arch_state_def)
  done

lemma mul_add_word_size_lt_msg_align_bits_ofnat[Arch_AC_assms]:
  "\<lbrakk> p < 2 ^ (msg_align_bits - word_size_bits); k < word_size \<rbrakk>
     \<Longrightarrow> of_nat p * of_nat word_size + k < (2 :: obj_ref) ^ msg_align_bits"
  apply (rule is_aligned_add_less_t2n[where n=word_size_bits])
     apply (simp_all add: msg_align_bits' word_size_word_size_bits is_aligned_mult_triv2)
   apply (simp_all add: word_size_word_size_bits word_size_bits_def)
   apply (simp add: word_size_def)
  apply (erule word_less_power_trans_ofnat[where k=3 and m=10, simplified], simp)
  done

lemma zero_less_word_size[Arch_AC_assms, simp]:
    "0 < (word_size :: obj_ref)"
  by (simp add: word_size_def)

end


global_interpretation Arch_AC_1?: Arch_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact Arch_AC_assms)
qed


context Arch begin global_naming RISCV64

lemma store_pte_respects:
  "\<lbrace>integrity aag X st and K (is_subject aag (p && ~~ mask pt_bits))\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wp get_object_wp set_object_integrity_autarch)
  apply simp
  done

lemma integrity_arch_state [iff]:
  "riscv_asid_table v = riscv_asid_table (arch_state s)
   \<Longrightarrow> integrity aag X st (s\<lparr>arch_state := v\<rparr>) = integrity aag X st s"
  unfolding integrity_def by simp

lemma integrity_arm_asid_map[iff]:
  "integrity aag X st (s\<lparr>arch_state := ((arch_state s)\<lparr>riscv_global_pts := v\<rparr>)\<rparr>) =
   integrity aag X st s"
  unfolding integrity_def by simp

lemma integrity_arm_hwasid_table[iff]:
  "integrity aag X st (s\<lparr>arch_state := ((arch_state s)\<lparr>riscv_kernel_vspace := v\<rparr>)\<rparr>) =
   integrity aag X st s"
  unfolding integrity_def by simp

lemma ptes_of_idx:
  "\<lbrakk> ptes_of s (pt_slot_offset level pt_ptr p) = Some pte;
     pts_of s pt_ptr = Some pt; pspace_aligned s \<rbrakk> \<Longrightarrow>
    pt (table_index (pt_slot_offset level pt_ptr p)) = pte"
  apply (drule_tac pt_ptr=pt_ptr in pspace_aligned_pts_ofD, simp)
  apply (fastforce simp: pte_of_def)
  done

lemma [simp]: "mask 12 >> 3 = (0x1FF :: obj_ref)"
by (clarsimp simp: mask_def)


lemma ucast_thingy:
 "UCAST(64 \<rightarrow> 9) (ptr && mask ptTranslationBits)
\<le> mask ptTranslationBits"
  by (metis AND_twice and_mask_eq_iff_le_mask ucast_and_mask)


lemma pt_lookup_from_level_is_subject:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<and>
        is_subject aag pt_ptr \<and> level \<le> max_pt_level \<and> vref \<in> user_region \<and>
        (\<exists>asid pt. vs_lookup_table level asid vref s = Some (level, pt_ptr) \<and>
                   aobjs_of s pt_ptr = Some (PageTable pt))\<rbrace>
   pt_lookup_from_level level pt_ptr vref pt
   \<lbrace>\<lambda>rv _. is_subject aag (table_base rv)\<rbrace>,-"
  apply (induct level arbitrary: pt_ptr)
   apply (subst pt_lookup_from_level_simps, simp)
   apply wpsimp

   apply (subst pt_lookup_from_level_simps, simp)
apply wp
apply (erule meta_allE)+
apply assumption
apply wpsimp+
apply safe

apply (subst pt_slot_offset_id)
apply (rule is_aligned_pt)
apply (fastforce simp add: opt_map_def aobj_of_def pte_of_def obj_at_def split: option.splits kernel_object.splits)
apply clarsimp
apply clarsimp

prefer 4
apply (subst pt_slot_offset_id)
apply (rule is_aligned_pt)
apply (fastforce simp add: opt_map_def aobj_of_def pte_of_def obj_at_def split: option.splits kernel_object.splits)
apply clarsimp
apply clarsimp

apply (subst aag_has_Control_iff_owns[symmetric])
apply assumption

apply (clarsimp simp: pas_refined_def)
apply (erule subsetD)
apply (clarsimp simp: auth_graph_map_def)
apply (rule_tac x=pt_ptr in exI, rule conjI)
apply simp
apply (rule exI, rule conjI, rule refl)


apply (rule sta_vref)

apply (simp add: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
apply (rule exI, rule exI, rule conjI, rule refl)
apply (rule exI, rule exI, rule exI, rule conjI, assumption)
apply simp

apply (subst vs_refs_aux_def)
apply clarsimp

apply (frule ptes_of_idx)
apply (simp add: opt_map_def)
apply clarsimp
apply (case_tac rv; clarsimp)

apply (clarsimp simp: graph_of_def
pte_ref2_def
)
apply (clarsimp simp: Bex_def)

apply (case_tac "level = max_pt_level"; clarsimp)

prefer 2

apply (rule_tac x="table_index (pt_slot_offset level pt_ptr vref)" in exI)
apply_trace clarsimp

apply (intro conjI)

apply (clarsimp simp: pptr_from_pte_def)
apply (rule refl)
apply (rule refl)

apply (rule_tac x="table_index (pt_slot_offset max_pt_level pt_ptr vref)" in exI)
apply_trace clarsimp

apply (intro conjI)

apply (rule table_index_max_level_slots)
apply clarsimp
  using pts_of_Some pts_of_Some_alignedD apply blast

apply (clarsimp simp: pptr_from_pte_def)

apply (rule_tac x=asid in exI)
apply (rule vs_lookup_table_step)
apply assumption
apply simp
apply simp
apply simp
apply simp
apply (case_tac rv; clarsimp simp: pptr_from_pte_def)


apply (prop_tac "\<exists>asid. vs_lookup_table (level - 1) asid vref s = Some (level - 1, pptr_from_pte rv)")
apply (rule_tac x=asid in exI)
apply (rule vs_lookup_table_step)
apply assumption
apply simp
apply simp
apply simp
apply simp
apply (case_tac rv; clarsimp simp: pptr_from_pte_def)

apply clarsimp
apply (drule vs_lookup_table_pt_at) back
apply simp
apply simp
apply simp
apply simp
apply simp

apply (clarsimp simp: opt_map_def obj_at_def)
done

lemma unmap_page_table_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs and K (is_subject_asid aag asid \<and> vaddr \<in> user_region)\<rbrace>
   unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: unmap_page_table_def  )
  apply (rule hoare_pre)
apply wpsimp
   apply ((wpsimp wp:  hoare_vcg_all_lift_R dmo_mol_respects store_pte_respects pt_lookup_from_level_wrp
               simp: sfence_def
          | wp (once) hoare_drop_imps)+)[1]
   apply ((wpsimp wp:  hoare_vcg_all_lift_R dmo_mol_respects store_pte_respects pt_lookup_from_level_wrp
               simp: sfence_def
          | wp (once) hoare_drop_imps)+)[1]
apply clarsimp

apply (rule hoare_vcg_conj_liftE)
   apply ((wpsimp wp:  hoare_vcg_all_lift_R dmo_mol_respects store_pte_respects pt_lookup_from_level_wrp
               simp: sfence_def
          | wp (once) hoare_drop_imps)+)[1]

apply (rule hoare_vcg_E_elim)
prefer 2
apply (rule pt_lookup_from_level_is_subject)
apply wp
   apply ((wpsimp wp:  hoare_vcg_all_lift_R dmo_mol_respects store_pte_respects pt_lookup_from_level_wrp

               simp: sfence_def
          | wp (once) hoare_drop_imps)+)[1]

apply clarsimp

apply auto

(*****************************)
apply (subst aag_has_Control_iff_owns[symmetric])
apply assumption

  apply (clarsimp simp: vspace_for_asid_def)
  apply (clarsimp simp: obj_at_def pas_refined_def)
apply (drule sym)
apply clarsimp
apply (erule subsetD) back
apply (rule sata_asid_lookup)
apply (simp add: vspace_for_pool_def pool_for_asid_def)

apply (clarsimp simp: state_vrefs_def)

apply (prop_tac "vs_lookup_table max_pt_level asid 0 s = Some (max_pt_level, pt)")
apply (clarsimp simp: vs_lookup_table_def obind_def)
apply (clarsimp simp: vspace_for_pool_def pool_for_asid_def obind_def opt_map_def split: option.splits)

apply (rule exI)
apply (rule conjI)
apply (rule_tac x=asid_pool_level in exI)
apply (rule exI)
apply (rule conjI)
apply (rule refl)
apply (rule_tac x=asid_pool_level in exI)
apply (rule_tac x=asid in exI)
apply (rule_tac x=0 in exI)
apply (rule conjI)
apply (simp add: vs_lookup_table_def)
apply (simp add: obind_def)
apply (simp add: vspace_for_pool_def pool_for_asid_def obind_def opt_map_def
split: option.splits)
apply simp

apply (subst vs_refs_aux_def)
apply clarsimp
apply (clarsimp simp: map_set_in)

apply (prop_tac "(asid_low_bits_of asid, pt) \<in> graph_of x2")
apply (clarsimp simp: graph_of_def)
apply (erule bexI[rotated])
apply clarsimp
apply (subst ucast_up_ucast[symmetric])
prefer 2
apply (subst asid_low_bits_of_mask_eq)
apply simp
  apply (simp add: is_up_def source_size_def target_size_def word_size)
(*************************)

apply (rule_tac x=asid in exI)
apply (clarsimp simp: vs_lookup_table_def vspace_for_asid_def vspace_for_pool_def pool_for_asid_def)
apply (clarsimp simp: obind_def)

apply (prop_tac "\<exists>asid. vs_lookup_table max_pt_level asid vaddr s = Some (max_pt_level, pt)")
apply (rule_tac x=asid in exI)
apply (clarsimp simp: vs_lookup_table_def vspace_for_asid_def vspace_for_pool_def pool_for_asid_def)
apply (clarsimp simp: obind_def)

apply clarsimp
apply (drule vs_lookup_table_pt_at)
apply simp
apply simp
apply fastforce
apply fastforce
apply fastforce

apply (clarsimp simp: opt_map_def obj_at_def)

done


lemma perform_page_table_invocation_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs and valid_pti page_table_invocation
                       and K (authorised_page_table_inv aag page_table_invocation)\<rbrace>
   perform_page_table_invocation page_table_invocation
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: perform_page_table_invocation_def perform_pt_inv_map_def perform_pt_inv_unmap_def
             cong: page_table_invocation.case_cong option.case_cong prod.case_cong
                   cap.case_cong arch_cap.case_cong)
apply (cases page_table_invocation; clarsimp)
  apply (wpsimp wp: set_cap_integrity_autarch
                    store_pte_respects unmap_page_table_respects mapM_wp'
              simp: mapM_x_mapM authorised_page_table_inv_def  sfence_def
)
apply (rename_tac cap fst_cslot_ptr snd_cslot_ptr)
apply (wpsimp wp: set_cap_integrity_autarch )
apply (rule mapM_x_inv_wp)
apply (prop_tac "integrity aag X st s \<and> is_subject aag fst_cslot_ptr \<and> is_PageTableCap cap")
apply assumption
apply clarsimp
apply clarsimp
apply (rule hoare_vcg_conj_lift)

apply (wpsimp wp: store_pte_respects)
apply (prop_tac "integrity aag X st s \<and> is_PageTableCap cap")
apply assumption
apply (clarsimp simp: authorised_page_table_inv_def)
apply (case_tac cap; clarsimp)
  apply (wpsimp wp: set_cap_integrity_autarch
                    store_pte_respects unmap_page_table_respects mapM_wp'
              simp: mapM_x_mapM authorised_page_table_inv_def  sfence_def
)
apply clarsimp
  apply (wpsimp wp: set_cap_integrity_autarch
                    store_pte_respects unmap_page_table_respects mapM_wp'
              simp: mapM_x_mapM authorised_page_table_inv_def  sfence_def
)
apply wp
apply clarsimp
apply (rule conjI)
apply (clarsimp simp: authorised_page_table_inv_def)
apply clarsimp
apply (rule conjI)
apply (case_tac cap; clarsimp simp: authorised_page_table_inv_def)
apply (rule conjI)
prefer 2
apply (clarsimp simp: authorised_page_table_inv_def)

apply (clarsimp simp: valid_pti_def)
apply (clarsimp simp: valid_arch_cap_def)
apply (clarsimp simp: wellformed_acap_def)
apply (case_tac cap; clarsimp)
apply (clarsimp simp: wellformed_mapdata_def)
done


lemma is_transferable_is_arch_update:
  "is_arch_update cap cap' \<Longrightarrow> is_transferable (Some cap) = is_transferable (Some cap')"
  using is_transferable.simps is_arch_cap_def is_arch_update_def cap_master_cap_def
  by (simp split: cap.splits arch_cap.splits)

lemma perform_page_table_invocation_pas_refined [wp]:
  "\<lbrace>pas_refined aag and invs and valid_pti iv and K (authorised_page_table_inv aag iv)\<rbrace>
   perform_page_table_invocation iv
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  by (wpsimp wp: perform_page_table_invocation_pas_refined)


term valid_vspace_objs
definition authorised_slots :: "'a PAS \<Rightarrow> pte \<times> obj_ref \<Rightarrow> 's :: state_ext state \<Rightarrow>  bool" where
 "authorised_slots aag m s \<equiv> case m of
    (pte, slot) \<Rightarrow>
      (\<forall>level asid vref x.
vs_lookup_slot level asid vref s = Some (level, slot) \<longrightarrow>
vref \<in> user_region \<longrightarrow>
level \<le> max_pt_level \<longrightarrow>
pte_ref2 level pte = Some x
           \<longrightarrow> (\<forall>a \<in> snd (snd x). \<forall>p \<in> ptr_range (fst x) (fst (snd x)). aag_has_auth_to aag a p)) \<and>
      (is_subject aag (slot && ~~ mask pt_bits))"

(* FIXME ryanb - pass level to authorised slots *)
definition authorised_page_inv :: "'a PAS \<Rightarrow> page_invocation \<Rightarrow> 's :: state_ext state \<Rightarrow>  bool" where
  "authorised_page_inv aag pgi s \<equiv> case pgi of
     PageMap cap ptr slots \<Rightarrow>
       pas_cap_cur_auth aag (ArchObjectCap cap) \<and> is_subject aag (fst ptr) \<and> authorised_slots aag slots s
   | PageUnmap cap ptr \<Rightarrow> pas_cap_cur_auth aag (ArchObjectCap cap) \<and> is_subject aag (fst ptr)
   | PageGetAddr ptr \<Rightarrow> True"


lemma perform_pg_inv_get_addr_pas_refined [wp]:
  "\<lbrace>pas_refined aag and invs\<rbrace>
   perform_pg_inv_get_addr ptr
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
unfolding perform_pg_inv_get_addr_def
apply wpsimp
apply fastforce
done


lemma unmap_page_pas_refined:
  "\<lbrace>pas_refined aag and invs and K (vptr \<in> user_region)\<rbrace>
   unmap_page pgsz asid vptr pptr
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding unmap_page_def
  apply (clarsimp simp: conj_ac | wpsimp wp: set_cap_pas_refined_not_transferable hoare_vcg_all_lift
                                             hoare_vcg_imp_lift' get_cap_wp store_pte_pas_refined
                                             store_pte_valid_arch_state_unreachable)+
  apply (frule (1) pt_lookup_slot_vs_lookup_slotI0)
  apply (drule vs_lookup_slot_level)
  apply (case_tac "x = asid_pool_level")
   apply (fastforce dest: vs_lookup_slot_no_asid)
  apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
  apply (intro conjI)
    apply (clarsimp simp: reachable_page_table_not_global)
   apply (frule vs_lookup_table_pt_at; clarsimp?)
   apply (drule vs_lookup_table_valid_cap; clarsimp?)
   apply (fastforce simp: valid_cap_def valid_arch_cap_def valid_arch_cap_ref_def obj_at_def
                    dest: caps_of_state_valid split: cap.splits arch_cap.splits)
  apply (metis vs_lookup_table_vspace user_region_slots is_aligned_neg_mask2 pt_slot_offset_offset)
  done

lemma perform_pg_inv_unmap_pas_refined:
   "\<lbrace>pas_refined aag and invs and valid_page_inv (PageUnmap cap ct_slot)
                     and authorised_page_inv aag (PageUnmap cap ct_slot)\<rbrace>
    perform_pg_inv_unmap cap ct_slot
    \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pg_inv_unmap_def
  apply (strengthen invs_psp_aligned invs_vspace_objs invs_arch_state
         | wpsimp wp: unmap_page_pas_refined set_cap_pas_refined_not_transferable
                      unmap_page_invs get_cap_wp hoare_vcg_all_lift hoare_vcg_imp_lift)+
  apply (fastforce simp: authorised_page_inv_def valid_page_inv_def valid_arch_cap_def
                         cte_wp_at_caps_of_state update_map_data_def aag_cap_auth_def
                         cap_auth_conferred_def arch_cap_auth_conferred_def
                         cap_links_asid_slot_def cap_links_irq_def wellformed_mapdata_def)
  done

lemma set_cap_vs_lookup_slot[wp]:
  "set_cap param_a param_b \<lbrace>\<lambda>s. P (vs_lookup_slot level asid vref s)\<rbrace> "
  apply (clarsimp simp: vs_lookup_slot_def obind_def)
  apply (rule hoare_pre)
   apply (rule hoare_lift_Pf3[where f="\<lambda>s level asid vref. vs_lookup_table level asid vref s"])
    apply (clarsimp split: option.splits)
    apply wpsimp
   apply wpsimp
  apply (auto split: if_splits)
  done

crunches set_cap
  for ptes_of[wp]: "\<lambda>s. P (ptes_of s)"
and level_of_table[wp]: "\<lambda>s. P (level_of_table p s)"
 (simp: level_of_table_def)

lemma set_cap_authorised_page_inv[wp]:
  "set_cap param_a param_b \<lbrace>\<lambda>s. P (authorised_page_inv aag (PageMap cap ct_slot (pte,slot)) s)\<rbrace> "
apply (clarsimp simp: authorised_page_inv_def authorised_slots_def)
apply (rule hoare_pre)
apply wps
apply (wpsimp)
apply clarsimp
done

thm same_ref_def
lemma set_cap_same_ref[wp]:
  "set_cap param_a param_b \<lbrace>\<lambda>s. P (same_ref pte_slot cap s)\<rbrace> "
apply (case_tac pte_slot; clarsimp)
apply (clarsimp simp: same_ref_def)
apply (rule hoare_pre)
apply wps
apply wpsimp
apply assumption
done



lemma perform_pg_inv_map_pas_refined:
  "\<lbrace>pas_refined aag and invs and valid_page_inv (PageMap cap ct_slot (pte,slot))
                    and authorised_page_inv aag (PageMap cap ct_slot (pte,slot))\<rbrace>
   perform_pg_inv_map cap ct_slot pte slot
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pg_inv_map_def
  apply wpsimp
    apply (clarsimp simp: pas_refined_def state_objs_to_policy_def)

apply wps
apply wpsimp
apply (subst conj_commute) back
apply (subst conj_commute)
apply clarsimp
apply (rule hoare_vcg_conj_lift)
apply wpsimp
apply (rule state_vrefs_store_NonPageTablePTE_wp')

apply (rule_tac Q="\<lambda>_. invs and pas_refined aag and K (\<not> is_PageTablePTE pte)
and authorised_page_inv aag (PageMap cap ct_slot (pte,slot))
and same_ref (pte,slot) (ArchObjectCap cap)" in hoare_strengthen_post[rotated])
apply (clarsimp simp: pas_refined_def)
apply (rule conjI)
apply clarsimp
apply (intro exI, rule conjI, assumption)
apply clarsimp
apply (rule conjI)
apply clarsimp
apply (erule subsetD) back

apply (erule state_asids_to_policy_aux.cases)
      apply (fastforce dest: sata_asid)
     apply (clarsimp simp: cte_wp_at_caps_of_state)
apply (clarsimp simp only: split: if_splits)
apply (clarsimp simp: vs_refs_aux_def)
apply (erule sata_asid_lookup)
apply assumption
apply (fastforce dest: sata_asidpool)

apply (clarsimp simp: auth_graph_map_def)
apply (clarsimp simp: authorised_page_inv_def)

apply (erule state_bits_to_policy.cases)
apply (fastforce dest: sbta_caps simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_untyped simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_ts simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_bounds simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_cdt simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_cdt_transferable simp: state_objs_to_policy_def)

apply (clarsimp simp only: split: if_split_asm)
prefer 2

apply (erule subsetD)
apply (simp only: state_objs_to_policy_def)
apply (drule sbta_vref)
apply fastforce

apply (clarsimp simp: vs_refs_aux_def)
apply (clarsimp simp: graph_of_def)

apply (case_tac "level \<noteq> max_pt_level \<or> a \<notin> kernel_mapping_slots"; clarsimp simp: word_le_not_less)
apply (subgoal_tac "(pasObjectAbs aag (table_base slot), ba, pasObjectAbs aag ac) \<in> pasPolicy aag")
apply clarsimp
apply (thin_tac "_ \<notin> _")


apply (case_tac "level = asid_pool_level")
apply clarsimp
apply (frule vs_lookup_slot_no_asid)
apply (fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
apply fastforce
apply fastforce
apply fastforce

apply (clarsimp split: if_split_asm)
apply (case_tac pte; clarsimp)
apply (clarsimp simp: pte_ref2_def)
apply (clarsimp simp: authorised_slots_def)

apply (subst (asm) vs_lookup_slot_table_unfold)
apply fastforce
apply fastforce
apply fastforce

apply (erule subsetD)
apply (simp only: state_objs_to_policy_def)
apply clarsimp
apply (rule exI, rule conjI, rule refl)+
apply (rule sbta_vref)
apply (clarsimp simp: state_vrefs_def)
apply (intro exI conjI)
apply (rule refl)
apply assumption
apply (fastforce simp: aobjs_of_Some obj_at_def)
apply fastforce
apply (fastforce simp: vs_refs_aux_def graph_of_def)

apply (clarsimp simp: same_ref_def)

apply (wpsimp wp: arch_update_cap_invs_map set_cap_pas_refined_not_transferable)
apply (clarsimp simp: valid_page_inv_def authorised_page_inv_def)
apply (clarsimp simp: cte_wp_at_caps_of_state is_frame_cap_def is_FrameCap_def)
apply (intro conjI)

apply (clarsimp simp: is_arch_update_def cap_master_cap_def)
apply (case_tac cap; clarsimp)
apply (clarsimp simp: same_ref_def parent_for_refs_def)
  using vs_lookup_slot_unique_level apply blast

apply (clarsimp simp: is_arch_update_def cap_master_cap_def)
apply (case_tac cap; clarsimp)
apply (clarsimp simp: is_arch_cap_def)
apply (drule (1) caps_of_state_valid)
apply (clarsimp simp: valid_arch_cap_def)
apply (clarsimp simp: valid_cap_def cap_aligned_def)

apply fastforce+
done



lemma perform_page_invocation_pas_refined [wp]:
  "\<lbrace>pas_refined aag and invs and authorised_page_inv aag pgi and valid_page_inv pgi\<rbrace>
   perform_page_invocation pgi
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
apply (simp add: perform_page_invocation_def)
apply (wpsimp wp: perform_pg_inv_map_pas_refined perform_pg_inv_unmap_pas_refined)
apply auto
done



lemma is_subject_trans:
  "\<lbrakk> is_subject aag x;  pas_refined aag s; (pasObjectAbs aag x, Control, pasObjectAbs aag y) \<in> pasPolicy aag \<rbrakk>
     \<Longrightarrow> is_subject aag y"
apply (subst aag_has_Control_iff_owns[symmetric])
apply simp
apply simp
done

lemma is_subject_asid_trans:
  "\<lbrakk> is_subject_asid aag x;  pas_refined aag s; (pasASIDAbs aag x, Control, pasObjectAbs aag y) \<in> pasPolicy aag \<rbrakk>
     \<Longrightarrow> is_subject aag y"
apply (subst aag_has_Control_iff_owns[symmetric])
apply simp
apply simp
done



lemma pt_walk_is_subject:
  "\<lbrakk> pas_refined aag s; valid_vspace_objs s; valid_asid_table s; pspace_aligned s;
     pt_walk level bot_level pt_ptr vptr (ptes_of s) = Some (level', pt);
     vs_lookup_table level asid vptr s = Some (level, pt_ptr);
     level \<le> max_pt_level; vptr \<in> user_region; is_subject aag pt_ptr \<rbrakk>
     \<Longrightarrow> is_subject aag pt"
apply (induct level arbitrary: pt_ptr)
apply (subst (asm) pt_walk.simps, simp)


apply (subst (asm) pt_walk.simps) back
apply (clarsimp simp: obind_def split: if_splits option.splits)
apply (erule meta_allE)
apply (drule meta_mp)
apply assumption
apply (drule meta_mp)
prefer 2
apply (drule meta_mp)
prefer 2
apply simp
prefer 2

apply (rule vs_lookup_table_extend)
apply assumption
apply (subst pt_walk.simps)
apply simp
apply (clarsimp simp: obind_def)

apply clarsimp


apply (frule vs_lookup_table_pt_at)
apply clarsimp
apply clarsimp
apply clarsimp

apply clarsimp
apply clarsimp


apply (clarsimp simp: typ_at_eq_kheap_obj)


apply (erule (1) is_subject_trans)
apply (clarsimp simp: pas_refined_def)
apply (erule subsetD)
apply (clarsimp simp: auth_graph_map_def)
apply (rule exI, rule conjI, rule refl)+
apply (rule sta_vref)
apply (subst state_vrefs_def)
apply clarsimp

apply (rule exI)
apply (rule conjI)
apply (rule exI, rule exI, rule conjI, rule refl)

apply (rule exI, rule exI, rule exI)
apply (rule conjI)
apply (assumption)

apply (rule conjI)
apply (simp add: opt_map_def)
apply clarsimp

apply (frule ptes_of_idx)
apply (simp add: opt_map_def)
apply clarsimp
apply clarsimp

apply (clarsimp simp: ptes_of_def obind_def is_PageTablePTE_def split: option.splits)

apply (clarsimp simp: vs_refs_aux_def)

apply (case_tac "level = max_pt_level"; clarsimp)

prefer 2

apply (prop_tac "(table_index (pt_slot_offset level pt_ptr vptr), ptrFromPAddr (addr_from_ppn x31), 0, {Control}) \<in>graph_of (pte_ref2 level \<circ> pta)")
apply (clarsimp simp: graph_of_def pte_ref2_def)

apply (rule bexI)
prefer 2
apply assumption
apply clarsimp
apply (rule conjI)
apply (clarsimp simp: pptr_from_pte_def)
apply fastforce


apply (prop_tac "(table_index (pt_slot_offset max_pt_level pt_ptr vptr), ptrFromPAddr (addr_from_ppn x31), 0, {Control}) \<in>graph_of (pte_ref2 max_pt_level \<circ> pta)")
apply (clarsimp simp: graph_of_def pte_ref2_def)

apply (rule bexI)
prefer 2
apply clarsimp
apply (rule conjI)
apply assumption
apply clarsimp
apply (drule table_index_max_level_slots)
prefer 2
apply fastforce
  using aobjs_of_Some pts_of_Some pts_of_Some_alignedD apply blast
apply (clarsimp simp: pptr_from_pte_def)
done



lemma pt_lookup_slot_from_level_is_subject:
  "\<lbrakk> pas_refined aag s; valid_vspace_objs s; valid_asid_table s; pspace_aligned s;
     pt_lookup_slot_from_level level bot_level pt_ptr vptr (ptes_of s) = Some (level', pt);
     (\<exists>asid. vs_lookup_table level asid vptr s = Some (level, pt_ptr));
     level \<le> max_pt_level; vptr \<in> user_region; is_subject aag pt_ptr \<rbrakk>
     \<Longrightarrow> is_subject aag (table_base pt)"
apply (clarsimp simp: pt_lookup_slot_from_level_def obind_def split: option.splits)
apply (drule (4) pt_walk_is_subject)
defer
apply clarsimp+
apply (subst pt_slot_offset_id)
apply (erule pt_walk_is_aligned)
apply (erule vs_lookup_table_is_aligned)
apply clarsimp+
apply fastforce
done

thm pt_lookup_slot_def
pt_lookup_slot_from_level_def


lemma unmap_page_respects:
  "\<lbrace>integrity aag X st and pspace_aligned and valid_vspace_objs and valid_arch_state
                       and K (is_subject_asid aag asid) and pas_refined aag
                       and K (vptr \<in> user_region)\<rbrace>
   unmap_page sz asid vptr pptr
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: unmap_page_def swp_def cong: vmpage_size.case_cong)
  apply (rule hoare_pre)
   apply (wpsimp wp: store_pte_respects
                     hoare_drop_imps[where Q="\<lambda>rv. integrity aag X st"]
               simp: sfence_def  is_aligned_mask[symmetric]
          | wp (once) hoare_drop_imps
                      mapM_set''[where f="(\<lambda>a. store_pte a InvalidPTE)"
                                   and I="\<lambda>x s. is_subject aag (x && ~~ mask pt_bits)"
                                   and Q="integrity aag X st"]
          | wp (once) hoare_drop_imps[where R="\<lambda>rv s. rv"])+

apply (clarsimp simp: pt_lookup_slot_def)
apply (frule pt_lookup_slot_from_level_is_subject)
apply (fastforce intro: valid_arch_state_asid_table)+

apply (clarsimp simp: vspace_for_asid_def)
apply (fastforce simp: vs_lookup_table_def obind_def split: option.splits)
apply clarsimp
apply clarsimp
prefer 2
apply clarsimp

apply (erule (1) is_subject_asid_trans)

apply (prop_tac "\<exists>pool_ptr pool. asid_table s (asid_high_bits_of asid) = Some pool_ptr \<and>
asid_pools_of s pool_ptr = Some pool")
apply (simp add: vspace_for_asid_def obind_def pool_for_asid_def
vspace_for_pool_def
 split: option.splits)

apply (clarsimp simp: pas_refined_def)
apply (erule subsetD) back
apply (rule sata_asid_lookup)
apply simp

apply (simp add: state_vrefs_def)

apply (rule exI)
apply (rule conjI)
apply (rule exI, rule exI, rule conjI, rule refl)

apply (rule_tac x=asid_pool_level in exI)
apply (rule_tac x=asid in exI)
apply (rule_tac x=vptr in exI)
apply (rule conjI)
apply (clarsimp simp: vs_lookup_table_def obind_def split: option.splits)
apply (rule conjI)
apply (clarsimp simp: vspace_for_asid_def)
apply clarsimp
apply (rule conjI)
apply (rule refl)
apply (clarsimp simp: vspace_for_asid_def pool_for_asid_def)
apply (clarsimp simp: vspace_for_asid_def)

apply (clarsimp simp: opt_map_def split: option.splits)
apply simp

apply (clarsimp simp: vs_refs_aux_def graph_of_def)
apply (clarsimp simp: vspace_for_asid_def obind_def vspace_for_pool_def
pool_for_asid_def
opt_map_def map_set_in
split: option.splits)
apply (rule exI)
apply auto

apply (subst ucast_up_ucast[symmetric])
prefer 2
apply (subst asid_low_bits_of_mask_eq)
apply simp
  apply (simp add: is_up_def source_size_def target_size_def word_size)
  done


lemma perform_page_invocation_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and authorised_page_inv aag pgi
                       and valid_page_inv pgi and valid_vspace_objs
                       and pspace_aligned and valid_vspace_objs and valid_arch_state
                       and is_subject aag  \<circ> cur_thread\<rbrace>
   perform_page_invocation pgi
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
proof -
  (* does not work as elim rule with clarsimp, which hammers Ball in concl. *)
  have set_tl_subset_mp: "\<And>xs a. a \<in> set (tl xs) \<Longrightarrow> a \<in> set xs" by (case_tac xs; clarsimp)
(*
  have hd_valid_slots:
    "\<And>a xs s. valid_slots (Inl (a, xs)) s \<Longrightarrow> hd xs \<in> set xs"
    "\<And>a xs s. valid_slots (Inr (a, xs)) s \<Longrightarrow> hd xs \<in> set xs"
    by (simp_all add: valid_slots_def)
*)
  show ?thesis
    apply (unfold authorised_page_inv_def)
  apply (simp add: perform_page_invocation_def mapM_discarded swp_def
                   valid_page_inv_def valid_unmap_def
                   authorised_page_inv_def authorised_slots_def
perform_pg_inv_map_def perform_pg_inv_unmap_def
sfence_def
            split: page_invocation.split sum.split
                   arch_cap.split option.split,
         safe)
        apply ((wp set_cap_integrity_autarch unmap_page_respects
                  mapM_x_and_const_wp[OF store_pte_respects] store_pte_respects
               | elim conjE
               | clarsimp dest!: set_tl_subset_mp
               | wpc )+)

   apply (clarsimp simp: cte_wp_at_caps_of_state cap_rights_update_def
                         acap_rights_update_def update_map_data_def
                         valid_page_inv_def valid_cap_simps
                  dest!: cap_master_cap_eqDs)

apply (rule conjI)
prefer 2

apply (case_tac m; clarsimp)
apply (clarsimp simp: valid_arch_cap_def wellformed_mapdata_def split: if_splits)
apply (case_tac m; clarsimp)
apply (clarsimp simp: aag_cap_auth_def)

apply (prop_tac "a \<in> acap_asid' (FrameCap r R sz dev (Some (a,b)))")
apply (clarsimp)
apply (drule (1) sata_asid[where aag=aag])
apply (clarsimp simp: pas_refined_def)
apply (drule (1) subsetD)
apply (fastforce dest: aag_wellformed_Control)
apply (simp add: perform_pg_inv_get_addr_def)
    apply (wpsimp wp: set_mrs_integrity_autarch set_message_info_integrity_autarch
                simp: ipc_buffer_has_auth_def)+
  done
qed


definition authorised_asid_control_inv :: "'a PAS \<Rightarrow> asid_control_invocation \<Rightarrow> bool" where
 "authorised_asid_control_inv aag aci \<equiv>
  case aci of MakePool frame slot parent base \<Rightarrow>
    is_subject aag (fst slot) \<and> is_aligned frame pageBits \<and>
    (\<forall>asid. is_subject_asid aag asid) \<and> is_subject aag (fst parent) \<and>
            (\<forall>x \<in> {frame..frame + 2 ^ pageBits - 1}. is_subject aag x)"


lemma integrity_asid_table_entry_update':
  "\<lbrakk> integrity aag X st s; atable = riscv_asid_table (arch_state s);
     (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of asid
             \<longrightarrow> is_subject_asid aag asid') \<rbrakk>
     \<Longrightarrow> integrity aag X st (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table :=
                                                          \<lambda>a. if a = asid_high_bits_of asid
                                                              then v
                                                              else atable a\<rparr>\<rparr>)"
  by (clarsimp simp: integrity_def)


lemma asid_table_entry_update_integrity[wp]:
 "\<lbrace>integrity aag X st and (\<lambda> s. atable = riscv_asid_table (arch_state s)) and
   K (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of asid
              \<longrightarrow> is_subject_asid aag asid')\<rbrace>
  modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := atable(asid_high_bits_of asid := v)\<rparr>\<rparr>)
  \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (wp | simp)+
  apply (blast intro: integrity_asid_table_entry_update')
  done

lemma perform_asid_control_invocation_respects:
  "\<lbrace>integrity aag X st and invs and valid_aci aci and K (authorised_asid_control_inv aag aci)\<rbrace>
   perform_asid_control_invocation aci
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: perform_asid_control_invocation_def)
  apply (rule hoare_pre)
   apply (wpc, simp)
   apply_trace (wpsimp wp: set_cap_integrity_autarch cap_insert_integrity_autarch
                     retype_region_integrity[where sz=12] static_imp_wp
delete_objects_valid_vspace_objs delete_objects_valid_arch_state
)
  apply (clarsimp simp: authorised_asid_control_inv_def
                        ptr_range_def page_bits_def add.commute
                        range_cover_def obj_bits_api_def default_arch_object_def
                        pageBits_def word_bits_def)
  apply (subst is_aligned_neg_mask_eq[THEN sym], assumption)
  apply (simp add: and_mask_eq_iff_shiftr_0 mask_zero)
apply (clarsimp simp: word_size_bits_def)
  done

lemma state_vrefs_helper_thing:
"\<lbrakk>ako_at (ASIDPool Map.empty) frame s;
          asid_table s (asid_high_bits_of base) = None\<rbrakk>
         \<Longrightarrow> (state_vrefs
                  (s\<lparr>arch_state := arch_state s
                       \<lparr>riscv_asid_table :=
                          \<lambda>a. if a = asid_high_bits_of base then Some frame
                               else asid_table s a\<rparr>\<rparr>)) = state_vrefs s"
apply (rule all_ext)
apply clarsimp
apply safe
prefer 2

apply (subst (asm) state_vrefs_def)
apply clarsimp

apply (clarsimp simp: state_vrefs_def)

apply (rule exI)
apply (rule conjI)
apply (rule_tac x=lvl in exI)

apply (rule_tac x=ao in exI)
apply (rule conjI)
apply (rule refl)
apply (rule_tac x=lvl in exI)
apply (rule_tac x=asid in exI)
apply (drule vs_lookup_level)
apply (rule_tac x=vref in exI)
apply clarsimp
prefer 2
apply clarsimp

apply (clarsimp simp: vs_lookup_table_def obind_def split: option.splits if_splits)
apply (clarsimp simp: pool_for_asid_def)
apply (clarsimp simp: pool_for_asid_def)
apply (fastforce simp: vspace_for_pool_def obind_def split: option.splits)

apply (subst (asm) state_vrefs_def)
apply clarsimp

apply (case_tac "asid_high_bits_of asid = asid_high_bits_of base")
prefer 2

apply (clarsimp simp: vs_lookup_table_def)
apply (clarsimp simp: pool_for_asid_def)

apply (clarsimp split: if_splits)
apply (clarsimp simp: state_vrefs_def)
apply (fastforce simp: vs_lookup_table_def obind_def pool_for_asid_def
                split: option.splits)
apply (clarsimp simp: state_vrefs_def)

apply (intro exI conjI)
apply (rule refl)
apply (clarsimp simp: vs_lookup_table_def obind_def pool_for_asid_def
                split: option.splits)
apply (rule conjI)
apply fastforce
apply clarsimp
apply (rule conjI)
prefer 2
apply clarsimp
apply (rule conjI)
prefer 2
apply clarsimp
apply assumption
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply fastforce

apply (clarsimp simp: vs_lookup_table_def)

apply (case_tac "bot = asid_pool_level")

prefer 2

apply (clarsimp simp: vs_lookup_table_def)
apply (clarsimp simp: pool_for_asid_def)

apply (clarsimp simp: vspace_for_pool_def)
apply (clarsimp simp: asid_pools_of_ko_at obj_at_def)


apply clarsimp

apply (clarsimp simp: pool_for_asid_def)
apply (clarsimp simp: obj_at_def vs_refs_aux_def aobjs_of_Some)
apply (clarsimp simp: authorised_asid_control_inv_def graph_of_def)
done


lemma pas_refined_asid_control_helper:
 "authorised_asid_control_inv aag (MakePool frame slot parent base) \<Longrightarrow>
\<lbrace>\<lambda>s. pas_refined aag s \<and>  ko_at (ArchObj (ASIDPool Map.empty)) frame s
 \<and> asid_table s (asid_high_bits_of base) = None
\<rbrace> do
                                          asid_table <- gets (riscv_asid_table \<circ> arch_state);
                                          asid_table' <- return (asid_table(asid_high_bits_of base \<mapsto> frame));
                                          modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := asid_table'\<rparr>\<rparr>)
od \<lbrace>\<lambda>_ s. pas_refined aag s\<rbrace>"
unfolding pas_refined_def
apply wpsimp

apply (rule conjI)
apply (clarsimp simp: state_objs_to_policy_def)
apply (clarsimp simp: auth_graph_map_def)
apply (erule state_bits_to_policy.cases)

apply (fastforce dest: sbta_caps simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_untyped simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_ts simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_bounds simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_cdt simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_cdt_transferable simp: state_objs_to_policy_def)
apply (subst (asm) state_vrefs_helper_thing)
apply clarsimp
apply clarsimp
apply (erule subsetD)
apply (simp only:)
apply (drule sbta_vref)
apply fastforce

apply clarsimp
apply (erule state_asids_to_policy_aux.cases)
thm sata_asid
thm sata_asid_lookup
thm sata_asidpool
apply (fastforce dest: sata_asid)
prefer 2
apply (clarsimp split: if_splits)
apply (clarsimp simp: authorised_asid_control_inv_def)
apply (drule_tac x=frame in bspec)
apply clarsimp
  using is_aligned_no_overflow apply blast
  apply (simp add: aag_wellformed_refl)
apply (fastforce dest: sata_asidpool)

apply (subst (asm) state_vrefs_helper_thing)
apply clarsimp
apply clarsimp


apply (case_tac "asid_high_bits_of asid = asid_high_bits_of base")
prefer 2



apply (drule sata_asid_lookup[rotated])
apply clarsimp
apply assumption
apply fastforce
apply (clarsimp simp: state_vrefs_def aobjs_of_Some obj_at_def vs_refs_aux_def graph_of_def)
done

(* FIXME ryanb: move *)
lemma retype_region_invs_extras_vspace_objs:
  "\<lbrace>invs and pspace_no_overlap_range_cover ptr sz and caps_no_overlap ptr sz
     and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
     and region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
     and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
     and K (ty = CapTableObject \<longrightarrow> 0 < us)
     and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
      retype_region ptr n us ty dev \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  apply (wp hoare_strengthen_post [OF retype_region_post_retype_invs],
    auto simp: post_retype_invs_def split: if_split_asm)+
  done


lemma perform_asid_control_invocation_pas_refined [wp]:
  "\<lbrace>pas_refined aag and pas_cur_domain aag and invs and valid_aci aci and ct_active
                    and K (authorised_asid_control_inv aag aci)\<rbrace>
   perform_asid_control_invocation aci
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
apply (rule hoare_gen_asm)
  apply (simp add: perform_asid_control_invocation_def)
apply (wpc)
apply (rule hoare_seq_ext)
apply (simp only: K_bind_def)
apply (rule hoare_seq_ext)
apply (rule hoare_seq_ext)
apply (rule hoare_seq_ext)
apply (rule hoare_seq_ext)
apply (rule hoare_seq_ext)
apply (rule pas_refined_asid_control_helper)
apply assumption
   apply (wp cap_insert_pas_refined' static_imp_wp
          | strengthen
          | wpc
          | simp add: delete_objects_def2 fun_upd_def[symmetric])+
      apply (wp retype_region_pas_refined'[where sz=pageBits]
                hoare_vcg_ex_lift hoare_vcg_all_lift static_imp_wp hoare_wp_combs hoare_drop_imp
                retype_region_invs_extras(4)[where sz = pageBits]
                retype_region_invs_extras(6)[where sz = pageBits]
                retype_region_invs_extras(1)[where sz = pageBits]
retype_region_invs_extras_vspace_objs[where sz = pageBits]
             | simp add: do_machine_op_def split_def cte_wp_at_neg2)+

      apply (wp retype_region_cte_at_other'[where sz=pageBits]
                max_index_upd_invs_simple max_index_upd_caps_overlap_reserved
                hoare_vcg_ex_lift set_cap_cte_wp_at hoare_vcg_disj_lift set_free_index_valid_pspace
                set_cap_descendants_range_in set_cap_no_overlap get_cap_wp set_cap_caps_no_overlap
                hoare_vcg_all_lift static_imp_wp retype_region_invs_extras
                set_cap_pas_refined_not_transferable arch_update_cap_valid_mdb
             | simp add: do_machine_op_def split_def cte_wp_at_neg2 region_in_kernel_window_def)+
   apply (rename_tac frame slot parent base cap)
   apply (case_tac slot, rename_tac slot_ptr slot_idx)
   apply (case_tac parent, rename_tac parent_ptr parent_idx)
   apply (rule_tac Q="\<lambda>rv s.
             (\<exists>idx. cte_wp_at ((=) (UntypedCap False frame pageBits idx)) parent s) \<and>
             (\<forall>x\<in>ptr_range frame pageBits. is_subject aag x) \<and>
             pas_refined aag s \<and>
             pas_cur_domain aag s \<and>
             pspace_no_overlap_range_cover frame pageBits s \<and>
             invs s \<and> asid_table s (asid_high_bits_of base) = None \<and>
             descendants_range_in
               {frame..(frame && ~~ mask pageBits) + 2 ^ pageBits - 1} parent s \<and>
             range_cover frame pageBits
               (obj_bits_api (ArchObject ASIDPoolObj) 0) (Suc 0) \<and>
             is_subject aag slot_ptr \<and>
             is_subject aag parent_ptr \<and>
             pas_cap_cur_auth aag (ArchObjectCap (ASIDPoolCap frame base)) \<and>
             is_subject aag frame \<and>
             (\<forall>x. asid_high_bits_of x = asid_high_bits_of base \<longrightarrow>
                 is_subject_asid aag x)"
             in hoare_strengthen_post)
    apply (simp add: page_bits_def)
    apply (wp add: delete_objects_pspace_no_overlap hoare_vcg_ex_lift
                   delete_objects_descendants_range_in delete_objects_invs_ex
                   delete_objects_pas_refined
              del: Untyped_AI.delete_objects_pspace_no_overlap
           | simp add: page_bits_def)+
   apply clarsimp
   apply (rename_tac s idx)
   apply (frule untyped_cap_aligned, simp add: invs_valid_objs)
   apply (clarsimp simp: cte_wp_at_def aag_cap_auth_def ptr_range_def pas_refined_refl
                         cap_links_asid_slot_def cap_links_irq_def
                         obj_bits_api_def default_arch_object_def retype_addrs_def)
apply (clarsimp simp: conj_ac)
   apply (rule conjI, fastforce)
   apply (rule conjI, fastforce)
   apply (rule conjI, fastforce)
   apply (rule conjI, fastforce)
   apply (rule conjI, force intro: descendants_range_caps_no_overlapI
                             simp: cte_wp_at_def)
   apply (rule conjI)
apply (clarsimp simp: max_free_index_def)
apply (prop_tac "valid_cap (UntypedCap False frame pageBits idx) s")
apply (clarsimp simp: get_cap_caps_of_state)
  apply (simp add: Untyped_AI.caps_of_state_valid)
   apply (rule conjI)
apply (clarsimp simp: free_index_of_def max_free_index_def valid_cap_def)
   apply (rule conjI)
    apply (cut_tac s=s and ptr="(parent_ptr, parent_idx)" in cap_refs_in_kernel_windowD)
      apply ((fastforce simp add: caps_of_state_def cap_range_def)+)[3]
apply (clarsimp simp: valid_cap_def)
apply (prop_tac "frame \<le> frame + (2 ^ pageBits - 1)")
  using is_aligned_no_overflow' apply blast
apply (prop_tac "frame + (2 ^ pageBits - 1) \<le> frame + 2 ^ pageBits - 1")
  apply (simp add: x_power_minus_1)
apply fastforce

  apply (clarsimp simp: valid_aci_def authorised_asid_control_inv_def)
  apply (rename_tac frame slot_ptr slot_idx parent_ptr parent_idx base)
  apply (subgoal_tac "is_aligned frame pageBits")
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (rule conjI)
    apply (drule untyped_slots_not_in_untyped_range)
         apply (erule empty_descendants_range_in)
        apply (simp add: cte_wp_at_caps_of_state)
       apply simp
      apply (rule refl)
     apply (rule subset_refl)
    apply (simp add: page_bits_def)
   apply (clarsimp simp: ptr_range_def invs_psp_aligned invs_valid_objs
                         descendants_range_def2 empty_descendants_range_in page_bits_def)
   apply ((strengthen refl | simp)+)?
   apply (rule conjI, fastforce)
   apply (rule conjI, fastforce intro: empty_descendants_range_in)
   apply (rule conjI)
    apply (clarsimp simp: range_cover_def obj_bits_api_def default_arch_object_def)
    apply (subst is_aligned_neg_mask_eq[THEN sym], assumption)
    apply (simp add: and_mask_eq_iff_shiftr_0 pageBits_def mask_zero)
   apply (clarsimp simp: aag_cap_auth_def pas_refined_refl)
   apply (drule_tac x=frame in bspec)
    apply (simp add: is_aligned_no_overflow)
   apply (clarsimp simp: pas_refined_refl cap_links_asid_slot_def
                         label_owns_asid_slot_def cap_links_irq_def)
  apply (fastforce dest: cte_wp_at_valid_objs_valid_cap simp: valid_cap_def cap_aligned_def)
  done


definition authorised_asid_pool_inv :: "'a PAS \<Rightarrow> asid_pool_invocation \<Rightarrow> bool" where
 "authorised_asid_pool_inv aag api \<equiv>
  case api of Assign asid pool_ptr ct_slot \<Rightarrow>
    is_subject aag pool_ptr \<and> is_subject aag (fst ct_slot) \<and> is_subject_asid aag asid"


lemma pt_slot_offset_id':
  "is_aligned pt_ptr pt_bits \<Longrightarrow>
mask pt_bits && (xa << pte_bits) = xa << pte_bits \<Longrightarrow>
table_base (pt_ptr + (xa << pte_bits)) = pt_ptr"
  apply (simp add: pt_slot_offset_def is_aligned_mask_out_add_eq mask_eq_x_eq_0[symmetric])
apply (simp add: pt_index_def pt_bits_def table_size_def shiftl_over_and_dist mask_shiftl_decompose
                word_bool_alg.conj_ac)
done

lemma copy_global_mappings_integrity:
  "\<lbrace>integrity aag X st and K (is_aligned x pt_bits \<and> is_subject aag x)\<rbrace>
       copy_global_mappings x
       \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: copy_global_mappings_def)
  apply (wp mapM_x_wp[OF _ subset_refl] store_pte_respects)
apply (simp only: pt_index_def)
apply (subst pt_slot_offset_id')
apply simp
apply (clarsimp simp: pte_bits_def word_size_bits_def pt_bits_def table_size_def ptTranslationBits_def mask_def)
apply (word_bitwise)
apply auto[1]
apply clarsimp
   apply wpsimp+
  done


lemma perform_asid_pool_invocation_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs and valid_apinv api and K (authorised_asid_pool_inv aag api)\<rbrace>
   perform_asid_pool_invocation api
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (unfold perform_asid_pool_invocation_def store_asid_pool_entry_def)
  apply (wpsimp wp: set_asid_pool_integrity_autarch get_cap_wp set_cap_integrity_autarch
copy_global_mappings_integrity
hoare_drop_imps
)
  apply (auto iff: authorised_asid_pool_inv_def)
defer

thm valid_apinv_def
apply (clarsimp simp: valid_apinv_def)
apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)
apply (case_tac m; clarsimp)

apply (frule_tac ptr="(a,b)" in sbta_caps)
apply simp
apply (simp add: cap_auth_conferred_def arch_cap_auth_conferred_def)
apply (erule (1) is_subject_trans) back
apply (fastforce simp: pas_refined_def auth_graph_map_def state_objs_to_policy_def)


apply (clarsimp simp: valid_apinv_def)
apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)
apply (case_tac m; clarsimp)
apply (rule_tac s=s in is_aligned_pt)
apply (frule (1) caps_of_state_valid)
apply (clarsimp simp: valid_cap_def)
apply fastforce
done





thm valid_arch_inv_def
thm copy_global_mappings_invs

lemma store_pte_state_vrefs_unreachable:
  "\<lbrace>(\<lambda>s. P (state_vrefs s)) and pspace_aligned and valid_vspace_objs and valid_asid_table and (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, table_base p) s) \<rbrace>
  store_pte p pte \<lbrace>\<lambda>_. (\<lambda>s. P (state_vrefs s))\<rbrace>"
 supply fun_upd_apply[simp del]
  apply (wpsimp simp: store_pte_def set_pt_def wp: set_object_wp)
apply (erule rsubst[where P=P])
apply (rule all_ext)
apply safe
prefer 2

apply (clarsimp simp: state_vrefs_def)
apply (subst (asm) vs_lookup_table_unreachable_upd_idem)
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply fastforce

apply (prop_tac "x \<noteq> table_base p")
  using vs_lookup_level apply blast
apply (clarsimp simp: fun_upd_def)
apply (clarsimp simp: aobjs_of_Some)
apply fastforce

apply (clarsimp simp: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
apply (rule exI)
apply (rule exI)
apply (rule conjI, rule refl)
apply (rule exI)
apply (rule exI)
apply (rule_tac x=vref in exI)
apply (rule conjI)
apply (subst vs_lookup_table_unreachable_upd_idem)
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply assumption
apply (prop_tac "x \<noteq> table_base p")
  using vs_lookup_level apply blast
apply (fastforce simp: fun_upd_def aobjs_of_Some obj_at_def)
apply clarsimp
done

(* FIXME ryanb: do something with original? *)
lemma not_in_global_refs_vs_lookup:
  "(\<exists>\<rhd> (level,p)) s \<and> valid_vs_lookup s \<and> valid_global_refs s
            \<and> valid_arch_state s \<and> valid_global_objs s
            \<and> pt_at p s
        \<Longrightarrow> p \<notin> global_refs s"
  apply clarsimp
  apply (cases "level = asid_pool_level"; simp)
   apply (simp add: vs_lookup_table_def in_omonad)
   apply (drule (1) pool_for_asid_ap_at)
   apply (clarsimp simp: obj_at_def)
  apply (drule (1) vs_lookup_table_target)
  apply (drule valid_vs_lookupD; clarsimp simp: vref_for_level_user_region)
  apply (drule(1) valid_global_refsD2)
  apply (simp add: cap_range_def)
  done

(* FIXME ryanb: original has unnecessary condition *)
lemma store_pte_valid_vs_lookup_unreachable:
  "\<lbrace> valid_vs_lookup and pspace_aligned and valid_vspace_objs and valid_asid_table and
     (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, table_base p) s)  \<rbrace>
   store_pte p pte
   \<lbrace> \<lambda>_. valid_vs_lookup \<rbrace>"
  unfolding valid_vs_lookup_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' store_pte_vs_lookup_target_unreachable)
  apply (erule disjE; clarsimp)
  done

lemma copy_global_mappings_state_vrefs:
  "\<lbrace> (\<lambda>s. P (state_vrefs s)) and invs and K (is_aligned pt_ptr pt_bits) and
     (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, pt_ptr) s)  \<rbrace>
   copy_global_mappings pt_ptr
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  unfolding copy_global_mappings_def
apply clarsimp
  apply wp
      apply (rule hoare_strengthen_post)
       apply (rule_tac P="(\<lambda>s. P (state_vrefs s)) and pspace_aligned and valid_vspace_objs and valid_asid_table and
unique_table_refs and
            valid_vs_lookup and valid_objs and
 (\<lambda>s. is_aligned pt_ptr pt_bits \<and> is_aligned global_pt pt_bits \<and>

 (\<forall>level. \<not> \<exists>\<rhd> (level, table_base (pt_ptr)) s) \<and>
 (\<forall>level. \<not> \<exists>\<rhd> (level, table_base (global_pt)) s))" in mapM_x_wp')

apply (wpsimp wp: store_pte_state_vrefs_unreachable store_pte_valid_vspace_objs
hoare_vcg_all_lift hoare_vcg_imp_lift'
store_pte_vs_lookup_table_unreachable
store_pte_valid_vs_lookup_unreachable
)

apply (prop_tac "table_base (pt_ptr + (x << pte_bits)) = pt_ptr")
apply (frule_tac i=x in is_aligned_pte_offset)
      apply (metis mask_2pm1 table_base_plus)

apply (prop_tac "table_base (global_pt + (x << pte_bits)) = global_pt")
apply (frule_tac i=x in is_aligned_pte_offset)
      apply (metis mask_2pm1 table_base_plus)

apply (clarsimp simp: valid_objs_caps)
  using ptes_of_wellformed_pte apply blast
apply clarsimp

apply wpsimp
apply clarsimp
apply (intro conjI; fastforce?)
  apply (simp add: invs_valid_global_vspace_mappings)
  apply (simp add: invs_valid_global_vspace_mappings)
apply (clarsimp)
apply (prop_tac "global_pt s \<notin> global_refs s")
apply (rule_tac level=level in not_in_global_refs_vs_lookup)
  using invs_valid_global_arch_objs valid_global_arch_objs_pt_at apply fastforce
  using invs_valid_global_arch_objs riscv_global_pt_in_global_refs apply blast
done


crunches copy_global_mappings
  for tcb_domain_map_wellformed[wp]: "\<lambda>s. P (tcb_domain_map_wellformed aag s)"
  and asid_table[wp]: "\<lambda>s. P (asid_table s)"
  and cdt[wp]: "\<lambda>s. P (cdt s)"
  and thread_states[wp]: "\<lambda>s. P (thread_states s)"
  and thread_bound_ntfns[wp]: "\<lambda>s. P (thread_bound_ntfns s)"
  (wp: crunch_wps)

lemma copy_global_mappings_pas_refined:
  "\<lbrace> pas_refined aag and invs and K (is_aligned pt_ptr pt_bits) and
     (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, pt_ptr) s)
 \<rbrace>
   copy_global_mappings pt_ptr
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
apply (clarsimp simp: pas_refined_def state_objs_to_policy_def)
apply (rule hoare_pre)
apply_trace (rule hoare_vcg_conj_lift, solves wpsimp)+
apply (rule hoare_vcg_conj_lift)
prefer 2
apply (rule hoare_vcg_conj_lift)
prefer 2
apply wpsimp
apply wps
apply (rule copy_global_mappings_state_vrefs)
apply wps
apply (rule copy_global_mappings_state_vrefs)
apply clarsimp
done



lemma store_asid_pool_entry_state_vrefs:
  "\<lbrace>\<lambda>s. P (\<lambda>x. if x = pool_ptr
               then vs_refs_aux asid_pool_level (ASIDPool (\<lambda>a. if a = asid_low_bits_of asid
                                                               then Some pt_base
                                                               else (the (asid_pools_of s pool_ptr)) a))
               else if x = pt_base
               then vs_refs_aux max_pt_level (the (aobjs_of s x))
               else state_vrefs s x) \<and>
        pool_for_asid asid s = Some pool_ptr \<and>
        (\<forall>pool. ako_at (ASIDPool pool) pool_ptr s \<longrightarrow> pool (asid_low_bits_of asid) = None) \<and>
        (\<forall>level. \<not>\<exists>\<rhd> (level, pt_base) s) \<and>
        (\<exists>pt. pts_of s pt_base = Some pt \<and> kernel_mappings_only pt s) \<and>
        pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s\<rbrace>
\<comment> \<open>
         pt_cap <- get_cap ct_slot;
         pt_base <- return $ acap_obj (the_arch_cap pt_cap);
\<close>
   store_asid_pool_entry pool_ptr asid (Some pt_base)
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
apply clarsimp
unfolding store_asid_pool_entry_def set_asid_pool_def
apply (wpsimp wp: set_object_wp get_cap_wp)
apply (erule rsubst[where P=P])
apply (rule all_ext)
apply (clarsimp split del: if_split)


apply (prop_tac "is_aligned pt_base pt_bits")
apply (fastforce elim: pspace_aligned_pts_ofD dest: invs_psp_aligned)

apply safe

apply (clarsimp split: if_splits)

(* x = pool_ptr *)
apply (clarsimp simp: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
prefer 2
apply (assumption)
apply (rule exI)
apply (rule exI)
apply (rule conjI, rule refl)
apply (rule_tac x=asid_pool_level in exI)
apply (rule exI)+
apply (rule conjI)
apply (clarsimp simp: fun_upd_def)
thm asid_pool_map.vs_lookup_table[simplified fun_upd_def]
apply (subst asid_pool_map.vs_lookup_table[simplified fun_upd_def])
thm asid_pool_map_def
apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at obj_at_def valid_apinv_def asid_low_bits_of_def
pts_of_Some aobjs_of_Some)
apply fastforce
apply clarsimp
apply (fastforce simp: vs_lookup_table_def obind_def split: option.splits)
apply clarsimp
apply (clarsimp simp: ako_asid_pools_of)
(* x = acap_obj acap *)
apply (clarsimp simp: obj_at_def)

apply (clarsimp simp: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
prefer 2
apply (assumption)
apply (rule exI)
apply (rule exI)
apply (rule conjI, rule refl)
apply (rule_tac x=max_pt_level in exI)
apply (rule_tac x=asid in exI)
apply (rule_tac x=0 in exI)
apply (rule conjI)
apply (clarsimp simp: fun_upd_def)
thm asid_pool_map.vs_lookup_table[simplified fun_upd_def]
thm asid_pool_map.vs_lookup_table
apply (subst asid_pool_map.vs_lookup_table[simplified fun_upd_def])
apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at obj_at_def valid_apinv_def asid_low_bits_of_def
pts_of_Some aobjs_of_Some)
apply clarsimp
apply clarsimp
apply clarsimp
apply (clarsimp simp: pts_of_Some)

(* x is none of the above *)

apply (clarsimp simp: obj_at_def)

apply (clarsimp simp: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
prefer 2
apply (assumption)
apply (rule exI)
apply (rule exI)
apply (rule conjI, rule refl)
apply (frule vs_lookup_level)
apply (rule_tac x=lvl in exI)
apply (rule_tac x=asida in exI)
apply (rule_tac x=vref in exI)
apply (rule conjI)
apply (clarsimp simp: fun_upd_def)
thm asid_pool_map.vs_lookup_table[simplified fun_upd_def]
thm asid_pool_map.vs_lookup_table
apply (subst asid_pool_map.vs_lookup_table[simplified fun_upd_def])
apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at obj_at_def valid_apinv_def asid_low_bits_of_def
pts_of_Some aobjs_of_Some)
apply clarsimp
apply clarsimp
apply (clarsimp simp: vs_lookup_table_def obind_def vspace_for_pool_def asid_pools_of_ko_at
obj_at_def
split: if_splits option.splits)
apply clarsimp


(* second direction *)

supply if_split[split del]
apply (subst (asm) state_vrefs_def)
apply clarsimp
apply (clarsimp simp: fun_upd_def)
apply (subst (asm) asid_pool_map.vs_lookup_table[simplified fun_upd_def])
apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at obj_at_def valid_apinv_def asid_low_bits_of_def
pts_of_Some aobjs_of_Some)
apply clarsimp
apply (case_tac "x = pool_ptr")
apply clarsimp
apply (prop_tac "asid_pools_of s pool_ptr = Some pool")
apply (clarsimp simp:  asid_pools_of_ko_at obj_at_def)
apply (clarsimp simp: vs_refs_aux_def)

apply clarsimp

apply (case_tac "asida = asid \<and> bot \<le> max_pt_level")
apply clarsimp

apply clarsimp

apply (case_tac "x = pt_base")
apply clarsimp
apply (fastforce dest: vs_lookup_level)
apply clarsimp
apply (fastforce simp: state_vrefs_def)
done

crunches store_asid_pool_entry
  for irq_map_wellformed[wp]: "\<lambda>s. P (irq_map_wellformed aag s)"
  and tcb_domain_map_wellformed[wp]: "\<lambda>s. P (tcb_domain_map_wellformed aag s)"
  and state_irqs_to_policy[wp]: "\<lambda>s. P (state_irqs_to_policy aag s)"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and asid_table[wp]: "\<lambda>s. P (asid_table s)"
  and cdt[wp]: "\<lambda>s. P (cdt s)"
  and thread_states[wp]: "\<lambda>s. P (thread_states s)"
  and thread_bound_ntfns[wp]: "\<lambda>s. P (thread_bound_ntfns s)"


lemma store_asid_pool_entry_pas_refined:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and>
        pool_for_asid asid s = Some pool_ptr \<and>
        (\<forall>level. \<not>\<exists>\<rhd> (level, pt_base) s) \<and>
        (\<forall>pool. ako_at (ASIDPool pool) pool_ptr s \<longrightarrow> pool (asid_low_bits_of asid) = None) \<and>
        (\<exists>pt. pts_of s pt_base = Some pt \<and> kernel_mappings_only pt s) \<and>
        pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<and>
is_subject aag pool_ptr \<and>
is_subject aag pt_base \<and>
is_subject_asid aag asid
\<rbrace>
\<comment> \<open>
         pt_cap <- get_cap ct_slot;
         pt_base <- return $ acap_obj (the_arch_cap pt_cap);
\<close>
   store_asid_pool_entry pool_ptr asid (Some pt_base)
   \<lbrace>\<lambda>_ s. pas_refined aag s\<rbrace>"
apply (clarsimp simp: pas_refined_def state_objs_to_policy_def)
apply (rule hoare_pre)
apply wpsimp
apply (rule hoare_vcg_conj_lift)
prefer 2
apply (rule hoare_vcg_conj_lift)
prefer 2
apply wpsimp
apply wps
apply (rule store_asid_pool_entry_state_vrefs)
apply wps
apply (rule store_asid_pool_entry_state_vrefs)
apply clarsimp


apply (frule (1) pool_for_asid_validD)
apply clarsimp


apply (rule conjI)


apply (clarsimp simp: auth_graph_map_def)

apply (erule state_bits_to_policy.cases)
apply (fastforce dest: sbta_caps simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_untyped simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_ts simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_bounds simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_cdt simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_cdt_transferable simp: state_objs_to_policy_def)


apply (case_tac "ptr = pool_ptr")
apply clarsimp

apply (clarsimp simp: vs_refs_aux_def)
apply (clarsimp simp: graph_of_def)
apply (clarsimp split: if_splits)

  apply (simp add: aag_wellformed_refl)

apply (erule subsetD)
apply clarsimp
apply (rule_tac x=pool_ptr in exI)
apply clarsimp
apply (rule exI, rule conjI, rule refl)

apply (rule sbta_vref)
apply (clarsimp simp: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
apply (rule_tac x=asid_pool_level in exI)
apply (rule exI)
apply (rule conjI)
apply (rule refl)
apply (rule_tac x=asid_pool_level in exI)
apply (rule_tac x=asid in exI)
apply (rule_tac x=0 in exI)
apply (rule conjI)
apply (subst vs_lookup_table_def)
apply (clarsimp simp: obind_def aobjs_of_Some)
apply (fastforce simp: aobjs_of_Some obj_at_def asid_pools_of_ko_at)
apply (fastforce simp: vs_refs_aux_def graph_of_def)

apply (case_tac "ptr = pt_base")
apply clarsimp

apply (clarsimp simp: pts_of_Some)

apply (subgoal_tac "vs_refs_aux max_pt_level (PageTable pt) = {}", clarsimp)
apply_trace (clarsimp simp: vs_refs_aux_def)
apply (clarsimp simp: kernel_mappings_only_def)
apply (clarsimp simp: graph_of_def pte_ref2_def)

apply (simp only: if_False)
apply (drule sbta_vref)
apply fastforce


apply clarsimp

apply (erule state_asids_to_policy_aux.cases)

apply (erule subsetD) back
apply (fastforce dest: sata_asid)





apply (case_tac "poolptr = pool_ptr")
apply clarsimp

apply (clarsimp simp: vs_refs_aux_def)
apply (clarsimp simp: graph_of_def)
apply (clarsimp split: if_splits)

apply (clarsimp simp: pool_for_asid_def)

thm valid_asid_table_def
apply (clarsimp simp: asid_pools_of_ko_at obj_at_def)

apply (clarsimp simp: valid_asid_table_def)
apply (clarsimp simp: inj_on_def)
apply (drule_tac x="asid_high_bits_of asid" in bspec, clarsimp)
apply (drule_tac x="asid_high_bits_of asida" in bspec, clarsimp)
apply clarsimp

apply (prop_tac "asid_low_bits_of asida = asid_low_bits_of asid")

apply (simp add: asid_low_bits_of_mask_eq[symmetric])
apply (clarsimp simp: ucast_ucast_b is_up_def source_size_def target_size_def word_size)

apply (prop_tac "is_up UCAST(9 \<rightarrow> 64)")
apply (clarsimp simp: ucast_ucast_b is_up_def source_size_def target_size_def word_size)
apply (drule inj_ucast[OF refl])
apply (clarsimp simp: inj_def)

apply (drule asid_high_low)
apply clarsimp

  apply (metis aag_wellformed_refl)

apply (erule subsetD) back
apply (rule sata_asid_lookup)
apply fastforce
apply (clarsimp simp: state_vrefs_def)

apply (rule exI)
apply (rule conjI)
apply (rule_tac x=asid_pool_level in exI)
apply (rule exI)
apply (rule conjI)
apply (rule refl)
apply (rule_tac x=asid_pool_level in exI)
apply (rule_tac x=asid in exI)
apply (rule_tac x=0 in exI)
apply (rule conjI)
apply (subst vs_lookup_table_def)
apply (clarsimp simp: obind_def aobjs_of_Some)
apply (fastforce simp: aobjs_of_Some obj_at_def asid_pools_of_ko_at)

apply (subst vs_refs_aux_def)
apply (fastforce simp: graph_of_def)
apply clarsimp

apply (case_tac "poolptr = pt_base")
apply (clarsimp simp: vs_refs_aux_def pts_of_Some)

apply (simp only: if_False)
apply (erule subsetD) back
apply (rule sata_asid_lookup[rotated])
apply assumption
apply assumption

apply (erule subsetD) back
apply (fastforce dest: sata_asidpool)
done

crunches copy_global_mappings
  for pspace_aligned[wp]: pspace_aligned
  and valid_asid_table[wp]: valid_asid_table
  (wp: crunch_wps )




lemma copy_global_mappings_vs_lookup_table_noteq:
  "\<lbrace> (\<lambda>s. vref \<in> user_region \<and>
vs_lookup_table level asid vref s \<noteq> Some (level, pt_ptr)) and invs and K (is_aligned pt_ptr pt_bits) and
     (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, pt_ptr) s) \<rbrace>
   copy_global_mappings pt_ptr
   \<lbrace>\<lambda>_ s. vs_lookup_table level asid vref s \<noteq> Some (level, pt_ptr)\<rbrace>"
  unfolding copy_global_mappings_def
apply clarsimp
  apply wp
      apply (rule hoare_strengthen_post)
       apply (rule_tac P="(\<lambda>s. vref \<in> user_region \<and> vs_lookup_table level asid vref s \<noteq> Some (level, pt_ptr)) and pspace_aligned and valid_vspace_objs and valid_asid_table and
unique_table_refs and
            valid_vs_lookup and valid_objs and
 (\<lambda>s. is_aligned pt_ptr pt_bits \<and>

 (\<forall>level. \<not> \<exists>\<rhd> (level, table_base (pt_ptr)) s) )" in mapM_x_wp')

apply (wpsimp wp: store_pte_state_vrefs_unreachable store_pte_valid_vspace_objs
hoare_vcg_all_lift hoare_vcg_imp_lift'
store_pte_vs_lookup_table_unreachable
store_pte_valid_vs_lookup_unreachable
)

apply (prop_tac "table_base (pt_ptr + (x << pte_bits)) = pt_ptr")
apply (frule_tac i=x in is_aligned_pte_offset)
      apply (metis mask_2pm1 table_base_plus)

apply (clarsimp simp: valid_objs_caps)
  using ptes_of_wellformed_pte apply blast
apply clarsimp

apply wpsimp
apply clarsimp
apply (intro conjI; fastforce?)
done


lemma copy_global_mappings_valid_vspace_objs:
  "\<lbrace>  invs and K (is_aligned pt_ptr pt_bits) and
     (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, pt_ptr) s)
 \<rbrace>
   copy_global_mappings pt_ptr
   \<lbrace>\<lambda>_ s. valid_vspace_objs s\<rbrace>"
  unfolding copy_global_mappings_def
apply clarsimp
  apply wp
      apply (rule hoare_strengthen_post)
       apply (rule_tac P="
 pspace_aligned and valid_vspace_objs and valid_asid_table and
unique_table_refs and
            valid_vs_lookup and valid_objs and
 (\<lambda>s. is_aligned pt_ptr pt_bits \<and>

 (\<forall>level. \<not> \<exists>\<rhd> (level, table_base (pt_ptr)) s) )" in mapM_x_wp')

apply (wpsimp wp: store_pte_state_vrefs_unreachable store_pte_valid_vspace_objs
hoare_vcg_all_lift hoare_vcg_imp_lift'
store_pte_vs_lookup_table_unreachable
store_pte_valid_vs_lookup_unreachable
)

apply (prop_tac "table_base (pt_ptr + (x << pte_bits)) = pt_ptr")
apply (frule_tac i=x in is_aligned_pte_offset)
      apply (metis mask_2pm1 table_base_plus)

apply (clarsimp simp: valid_objs_caps)
  using ptes_of_wellformed_pte apply blast
apply clarsimp

apply wpsimp
apply clarsimp
apply (intro conjI; fastforce?)
done


lemma perform_asid_pool_invocation_pas_refined [wp]:
  "\<lbrace>pas_refined aag and invs and valid_apinv api and K (authorised_asid_pool_inv aag api)\<rbrace>
   perform_asid_pool_invocation api
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: perform_asid_pool_invocation_def)

apply (wpsimp)
apply (wpsimp wp: store_asid_pool_entry_pas_refined)
apply_trace (wpsimp wp: copy_global_mappings_pas_refined)
apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
apply (wpsimp wp: copy_global_mappings_vs_lookup_table_noteq)
apply wpsimp
apply (clarsimp simp: ako_asid_pools_of)
apply_trace (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' copy_global_mappings_valid_vspace_objs)
apply wpsimp
apply clarsimp
apply (strengthen invs_psp_aligned invs_valid_asid_table)
apply (clarsimp simp: conj_ac cong: conj_cong imp_cong)
apply (wpsimp wp: arch_update_cap_invs_map set_cap_pas_refined_not_transferable
hoare_vcg_all_lift hoare_vcg_imp_lift'
)
apply (wpsimp wp: get_cap_wp)+
apply (clarsimp simp: conj_ac)
apply (rule conjI, fastforce)+

apply (clarsimp simp: valid_apinv_def)

apply (clarsimp simp: cte_wp_at_caps_of_state)
apply (clarsimp simp: is_PageTableCap_def is_ArchObjectCap_def)
apply (clarsimp split: option.splits)
apply (clarsimp simp: authorised_asid_pool_inv_def)

apply (intro conjI)
  using caps_of_state_aligned_page_table apply blast
apply (fastforce dest: cap_not_in_valid_global_refs)
apply (drule (1) cap_cur_auth_caps_of_state)
apply clarsimp
apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def)
  using pas_refined_Control apply fastforce

apply (drule (1) caps_of_state_valid)
apply (clarsimp simp: update_map_data_def)
apply (clarsimp simp: valid_cap_def cap_aligned_def wellformed_mapdata_def)

apply (drule (1) cap_cur_auth_caps_of_state)
apply clarsimp
apply (clarsimp simp: update_map_data_def)
apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
cap_links_asid_slot_def label_owns_asid_slot_def cap_links_irq_def)
  using pas_refined_refl apply blast

  using invs_valid_table_caps valid_table_caps_def apply blast
  apply (simp add: asid_bits_of_defs(2))


apply (frule (1) caps_of_state_valid)
apply (clarsimp simp: valid_cap_def)
    apply (clarsimp simp: obj_at_def)
apply (rename_tac asid' pool_ptr a b acap_obj level asid vref pt)
   apply (drule (1) vs_lookup_table_valid_cap; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap, simp add: pts_of_Some aobjs_of_Some, fastforce intro: valid_objs_caps)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp)
   apply (clarsimp simp: is_cap_simps)

apply (frule (1) caps_of_state_valid)
apply (clarsimp simp: valid_cap_def)
    apply (clarsimp simp: obj_at_def)
apply (rename_tac asid' pool_ptr a b acap_obj level asid vref pt)
   apply (drule (1) vs_lookup_table_valid_cap; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap, simp add: pts_of_Some aobjs_of_Some, fastforce intro: valid_objs_caps)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp)
   apply (clarsimp simp: is_cap_simps)

apply (clarsimp simp: is_arch_update_def update_map_data_def is_cap_simps cap_master_cap_def)

done



definition authorised_arch_inv :: "'a PAS \<Rightarrow> arch_invocation \<Rightarrow> 's :: state_ext state \<Rightarrow> bool" where
 "authorised_arch_inv aag ai s \<equiv> case ai of
     InvokePageTable pti \<Rightarrow> authorised_page_table_inv aag pti
   | InvokePage pgi \<Rightarrow> authorised_page_inv aag pgi s
   | InvokeASIDControl aci \<Rightarrow> authorised_asid_control_inv aag aci
   | InvokeASIDPool api \<Rightarrow> authorised_asid_pool_inv aag api"

lemma invoke_arch_respects:
  "\<lbrace>integrity aag X st and authorised_arch_inv aag ai and
    pas_refined aag and invs and valid_arch_inv ai and is_subject aag \<circ> cur_thread\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: arch_perform_invocation_def)
  apply (wpsimp wp: perform_page_table_invocation_respects perform_page_invocation_respects
                    perform_asid_control_invocation_respects perform_asid_pool_invocation_respects)
  apply (auto simp: authorised_arch_inv_def valid_arch_inv_def)
  done


lemma invoke_arch_pas_refined:
  "\<lbrace>pas_refined aag and pas_cur_domain aag and invs and ct_active
                    and valid_arch_inv ai and authorised_arch_inv aag ai\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: arch_perform_invocation_def valid_arch_inv_def)
  apply (rule hoare_pre)
  apply (wp perform_page_table_invocation_pas_refined | wpc)+
apply (auto simp: authorised_arch_inv_def)
done


lemma decode_arch_invocation_authorised_helper:
 "pas_refined aag s \<Longrightarrow>
valid_asid_table s \<Longrightarrow>
vspace_for_asid a s = Some xaa \<Longrightarrow>
is_subject_asid aag a \<Longrightarrow>
 is_subject aag xaa"
apply (clarsimp simp: vspace_for_asid_def)
apply (frule (1) pool_for_asid_validD)
apply (clarsimp simp:
vspace_for_pool_def pool_for_asid_def
asid_pools_of_ko_at obj_at_def
)
thm sata_asid_lookup
apply (frule_tac vrefs="state_vrefs s" in sata_asid_lookup)
apply (clarsimp simp: state_vrefs_def)

apply (clarsimp simp: aobjs_of_Some)
apply (rule exI)
apply (rule conjI)
apply (rule_tac x=asid_pool_level in exI)
apply (rule exI)
apply (rule conjI)
apply (rule refl)
apply (rule_tac x=asid_pool_level in exI)
apply (rule_tac x=a in exI)
apply (rule_tac x=0 in exI)
apply (rule conjI)
prefer 2
apply fastforce
apply (clarsimp simp: vs_lookup_table_def obind_def
pool_for_asid_def vspace_for_pool_def asid_pools_of_ko_at obj_at_def split: option.splits)
apply (clarsimp simp: vs_refs_aux_def graph_of_def)

apply (clarsimp simp: image_def)
apply (rule exI)
apply (rule conjI)
apply assumption
apply (rule conjI)
prefer 2
apply (rule refl)

apply (clarsimp simp: asid_low_bits_of_def)
apply (word_eqI)
apply (fastforce simp: asid_low_bits_def)
apply (clarsimp simp: pas_refined_def)
apply (drule subsetD) back
apply assumption
  using aag_wellformed_Control by fastforce


lemma decode_page_table_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                  aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                  is_subject aag (fst slot) \<and>
                  (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)
)
and K (is_PageTableCap cap)\<rbrace> decode_page_table_invocation label msg slot cap excaps
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>, -"

  apply (rule hoare_gen_asmE)
  apply (clarsimp simp: is_PageTableCap_def)
  apply (rename_tac x xa)

  unfolding decode_page_table_invocation_def decode_pt_inv_map_def authorised_arch_inv_def

  apply (wpsimp simp: Let_def  is_final_cap_def if_fun_split )

   apply (clarsimp simp: cte_wp_at_caps_of_state)


  apply (prop_tac "\<forall>y \<in> set [x, x + 2 ^ pte_bits .e. x + 2 ^ pt_bits - 1]. table_base y = x")
   apply (drule (1) caps_of_state_aligned_page_table)
   apply (clarsimp simp only: is_aligned_neg_mask_eq' add_mask_fold)
   apply (drule subsetD[OF upto_enum_step_subset], clarsimp)
   apply (drule neg_mask_mono_le[where n=pt_bits])
   apply (drule neg_mask_mono_le[where n=pt_bits])
   apply (fastforce dest: FIXME_wordAND_wordNOT_mask_plus)


  apply safe

    prefer 3
    apply (clarsimp simp: authorised_page_table_inv_def)
    apply (drule caps_of_state_pasObjectAbs_eq)
        apply (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def)
       apply assumption
      apply clarsimp
     apply (fastforce simp: obj_refs_def)
    apply clarsimp

   prefer 2
   apply (clarsimp simp: authorised_page_table_inv_def)


  apply (clarsimp simp: authorised_page_table_inv_def)

  apply (rule conjI)

  apply (case_tac excaps; clarsimp)


   apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def)
   apply (frule_tac asid=a in pt_walk_is_subject; clarsimp?)
        apply assumption
       apply (drule vspace_for_asid_vs_lookup)
       apply (clarsimp simp: vs_lookup_table_def)
      apply clarsimp
     apply (fastforce simp: user_region_def user_vtop_canonical_user not_le_imp_less)
    apply (fastforce intro: decode_arch_invocation_authorised_helper)
   apply (fastforce dest: pt_walk_is_aligned caps_of_state_aligned_page_table)
  apply (case_tac excaps; clarsimp)
  apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                        cap_links_asid_slot_def label_owns_asid_slot_def cap_links_irq_def)
  done




lemma decode_frame_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                  aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                  is_subject aag (fst slot) \<and>
                  (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)
)
and K (is_FrameCap cap)\<rbrace> decode_frame_invocation label msg slot cap excaps
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>,-"
  apply (clarsimp simp: is_FrameCap_def)
  unfolding decode_frame_invocation_def authorised_arch_inv_def decode_fr_inv_map_def
  apply (wpsimp wp: check_vp_wpR simp: Let_def)

  apply (clarsimp simp: authorised_page_inv_def)


   apply (case_tac excaps; clarsimp)

  apply (prop_tac "pas_cap_cur_auth aag (ArchObjectCap (FrameCap x31 x32 x33 x34 (Some (a, msg ! 0)))) \<and>
               authorised_slots aag
                (make_user_pte (addrFromPPtr x31) (attribs_from_word (msg ! 2)) (mask_vm_rights x32 (data_to_rights (msg ! Suc 0))), xd)
                s")
   apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
   cap_links_asid_slot_def cap_links_irq_def)
   apply (clarsimp simp: authorised_slots_def)

   apply (prop_tac " msg ! 0 \<in> user_region")
    apply (clarsimp simp: user_region_def)
    apply (drule not_le_imp_less)
    apply (subgoal_tac "msg ! 0 \<le> msg ! 0 + mask (pageBitsForSize x33)")
  using user_vtop_canonical_user apply fastforce
    apply (clarsimp simp: vmsz_aligned_def)
    apply (erule is_aligned_no_overflow_mask)

   apply (rule conjI)
    prefer 2

    apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def)

    apply (frule_tac asid=a in pt_walk_is_subject)
            apply fastforce
           apply fastforce
          apply fastforce
         apply assumption
        apply (fastforce dest: vspace_for_asid_vs_lookup simp: vs_lookup_table_def)
       apply clarsimp
      apply clarsimp

     apply (rule decode_arch_invocation_authorised_helper)
        apply assumption
       apply fastforce
      apply fastforce
     apply clarsimp

    apply (subst pt_slot_offset_id)
     apply (erule pt_walk_is_aligned)
     apply (fastforce simp: cte_wp_at_caps_of_state dest: caps_of_state_aligned_page_table)
    apply clarsimp

   apply clarsimp

   apply (frule (1) pt_lookup_slot_vs_lookup_slotI, clarsimp)

   apply (drule (1) vs_lookup_slot_unique_level)
         apply fastforce
        apply fastforce
       apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
   apply clarsimp

   apply (clarsimp simp: make_user_pte_def split: if_splits, clarsimp simp: pte_ref2_def)

   apply (clarsimp simp: pte_ref2_def)


   apply (subst (asm) ptrFromPAddr_addr_from_ppn)
    apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply (frule (1) caps_of_state_valid)
    apply (clarsimp simp: valid_cap_def cap_aligned_def)
    apply (metis is_aligned_pageBitsForSize_table_size)

   apply (clarsimp simp: cte_wp_at_caps_of_state)

   apply (fastforce simp: vspace_cap_rights_to_auth_def mask_vm_rights_def validate_vm_rights_def
                          vm_kernel_only_def vm_read_only_def
                   split: if_splits)

  apply clarsimp
  done


lemma decode_asid_control_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (cap = ASIDControlCap \<and> (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                                           aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                           is_subject aag (fst slot) \<and>
                                           (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))\<rbrace>
   decode_asid_control_invocation label msg slot cap excaps
   \<lbrace>authorised_arch_inv aag\<rbrace>, -"
  unfolding decode_asid_control_invocation_def authorised_arch_inv_def authorised_asid_control_inv_def
  apply wpsimp
  apply (cases excaps; clarsimp)
  apply (rename_tac excaps_tail)
  apply (case_tac excaps_tail; clarsimp)
  apply (clarsimp simp: aag_cap_auth_def cte_wp_at_caps_of_state)
  apply (drule (1) caps_of_state_valid[where cap="UntypedCap _ _ _ _"])
  apply (fastforce simp: valid_cap_def cap_aligned_def is_cap_simps cap_auth_conferred_def
                   dest: pas_refined_Control)
  done

lemma decode_asid_pool_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (is_ASIDPoolCap cap \<and> (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                                         aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                         is_subject aag (fst slot) \<and>
                                         (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))\<rbrace>
   decode_asid_pool_invocation label msg slot cap excaps
   \<lbrace>authorised_arch_inv aag\<rbrace>, -"
  unfolding decode_asid_pool_invocation_def authorised_arch_inv_def Let_def
  apply wpsimp
  apply (erule swap[where P="authorised_asid_pool_inv _ _"])
  apply (cases excaps; clarsimp)
  apply (clarsimp simp: authorised_asid_pool_inv_def is_ASIDPoolCap_def)
  apply (rule conjI)
   apply (clarsimp simp: pas_refined_def state_objs_to_policy_def auth_graph_map_def)
   apply (drule subsetD)
    apply (fastforce dest!: sbta_caps
                      simp: obj_refs_def cte_wp_at_caps_of_state
                            cap_auth_conferred_def arch_cap_auth_conferred_def)
   apply (fastforce dest: aag_wellformed_Control)
  apply (erule allE, erule mp)
  apply (fastforce dest: caps_of_state_valid asid_high_bits_of_add_ucast
                   simp: cte_wp_at_caps_of_state valid_cap_def)
  done


lemma decode_arch_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                  aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                  is_subject aag (fst slot) \<and>
                  (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v))\<rbrace>
   arch_decode_invocation label msg x_slot slot cap excaps
   \<lbrace>authorised_arch_inv aag\<rbrace>, -"
  unfolding arch_decode_invocation_def
  apply (wpsimp wp: decode_page_table_invocation_authorised decode_asid_pool_invocation_authorised
                    decode_asid_control_invocation_authorised decode_frame_invocation_authorised)
  apply auto
  done


lemma authorised_arch_inv_sa_update:
  "authorised_arch_inv aag i (scheduler_action_update (\<lambda>_. act) s) =
   authorised_arch_inv aag i s"
  by (clarsimp simp: authorised_arch_inv_def authorised_page_inv_def authorised_slots_def
              split: arch_invocation.splits page_invocation.splits)

lemma set_thread_state_authorised_arch_inv[wp]:
  "set_thread_state ref ts \<lbrace>authorised_arch_inv aag i\<rbrace>"
  unfolding set_thread_state_def
  apply (wpsimp wp: dxo_wp_weak)
     apply (clarsimp simp: authorised_arch_inv_def authorised_page_inv_def authorised_slots_def
                    split: arch_invocation.splits page_invocation.splits)
    apply (wpsimp wp: set_object_wp)+
  apply (clarsimp simp: authorised_arch_inv_def authorised_page_inv_def
                        authorised_slots_def vs_lookup_slot_def obind_def
                 split: arch_invocation.splits page_invocation.splits if_splits option.splits)
  apply (subgoal_tac "vs_lookup_table level asid vref s = Some (level, b)")
   apply clarsimp
  apply (clarsimp simp: vs_lookup_table_def obind_def vspace_for_pool_def
                 split: option.splits if_splits)
  apply (subgoal_tac "(\<lambda>p. pte_of p ((pts_of s)(ref := None))) = ptes_of s")
   apply fastforce
  apply (rule all_ext)
  apply (clarsimp simp: pte_of_def obind_def pts_of_Some aobjs_of_Some get_tcb_def
                 split: option.splits)
  done

(* FIXME ryanb - move back to Finalise? *)
crunches arch_post_cap_deletion
  for pspace_aligned[wp]: pspace_aligned
  and valid_vspace_objs[wp]: valid_vspace_objs
  and valid_arch_state[wp]: valid_arch_state

end


context begin interpretation Arch .

requalify_facts
  invoke_arch_pas_refined
  invoke_arch_respects
  decode_arch_invocation_authorised
  authorised_arch_inv_sa_update
  set_thread_state_authorised_arch_inv
  arch_post_cap_deletion_pspace_aligned
  arch_post_cap_deletion_valid_vspace_objs
  arch_post_cap_deletion_valid_arch_state

requalify_consts
  authorised_arch_inv

end

declare arch_post_cap_deletion_pspace_aligned[wp]
declare arch_post_cap_deletion_valid_vspace_objs[wp]
declare arch_post_cap_deletion_valid_arch_state[wp]
declare authorised_arch_inv_sa_update[simp]
declare set_thread_state_authorised_arch_inv[wp]

end
