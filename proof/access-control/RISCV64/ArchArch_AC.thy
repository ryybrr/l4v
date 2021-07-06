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


(* FIXME ryanb: find better location *)
lemma state_vrefsD:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (lvl, p);
     aobjs_of s p = Some ao; vref \<in> user_region; x \<in> vs_refs_aux lvl ao \<rbrakk>
     \<Longrightarrow> x \<in> state_vrefs s p"
  unfolding state_vrefs_def by fastforce

lemma pool_for_asid_vs_lookupD:
  "pool_for_asid asid s = Some p \<Longrightarrow>
   vs_lookup_table asid_pool_level asid vref s = Some (asid_pool_level, p)"
  by (simp add: pool_for_asid_vs_lookup)

lemma vs_lookup_table_vref_independent:
  "\<lbrakk> vs_lookup_table level asid vref s = opt; level \<ge> max_pt_level \<rbrakk>
     \<Longrightarrow> vs_lookup_table level asid vref' s = opt"
  by (cases "level = asid_pool_level"; clarsimp simp: vs_lookup_table_def)

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
  "\<lbrace>integrity aag X st and K (is_subject aag (table_base p))\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wp get_object_wp set_object_integrity_autarch)
  apply simp
  done

lemma integrity_arch_state[iff]:
  "riscv_asid_table v = riscv_asid_table (arch_state s)
   \<Longrightarrow> integrity aag X st (s\<lparr>arch_state := v\<rparr>) = integrity aag X st s"
  unfolding integrity_def by simp

lemma integrity_riscv_global_pts[iff]:
  "integrity aag X st (s\<lparr>arch_state := ((arch_state s)\<lparr>riscv_global_pts := v\<rparr>)\<rparr>) =
   integrity aag X st s"
  unfolding integrity_def by simp

lemma integrity_riscv_kernel_vspace[iff]:
  "integrity aag X st (s\<lparr>arch_state := ((arch_state s)\<lparr>riscv_kernel_vspace := v\<rparr>)\<rparr>) =
   integrity aag X st s"
  unfolding integrity_def by simp

lemma is_subject_trans:
  "\<lbrakk> is_subject aag x; pas_refined aag s;
     (pasObjectAbs aag x, Control, pasObjectAbs aag y) \<in> pasPolicy aag \<rbrakk>
     \<Longrightarrow> is_subject aag y"
  by (subst aag_has_Control_iff_owns[symmetric]; simp)

lemma is_subject_asid_trans:
  "\<lbrakk> is_subject_asid aag x; pas_refined aag s;
     (pasASIDAbs aag x, Control, pasObjectAbs aag y) \<in> pasPolicy aag \<rbrakk>
     \<Longrightarrow> is_subject aag y"
  by (subst aag_has_Control_iff_owns[symmetric]; simp)

lemma graph_of_comp:
  "\<lbrakk> g x = y; f y = Some z \<rbrakk> \<Longrightarrow> (x,z) \<in> graph_of (f \<circ> g)"
  by (auto simp: graph_of_def)

(* FIXME ryanb: move *)
lemma rev_bexI_minus: "x \<in> A \<Longrightarrow> x \<notin> B \<Longrightarrow> P x \<Longrightarrow> \<exists>x\<in>A-B. P x"
  unfolding Bex_def by blast

lemma pt_walk_is_subject:
  "\<lbrakk> pas_refined aag s; valid_vspace_objs s; valid_asid_table s; pspace_aligned s;
     pt_walk level bot_level pt_ptr vptr (ptes_of s) = Some (level', pt);
     vs_lookup_table level asid vptr s = Some (level, pt_ptr);
     level \<le> max_pt_level; vptr \<in> user_region; is_subject aag pt_ptr \<rbrakk>
     \<Longrightarrow> is_subject aag pt"
  apply (induct level arbitrary: pt_ptr; clarsimp)
  apply (erule_tac x="pptr_from_pte (the (ptes_of s (pt_slot_offset level pt_ptr vptr)))" in meta_allE)
  apply (subst (asm) pt_walk.simps)
  apply (clarsimp simp: obind_def split: if_splits option.splits)
  apply (drule meta_mp)
   apply (erule vs_lookup_table_extend)
    apply (subst pt_walk.simps, clarsimp simp: obind_def)
   apply clarsimp
  apply (erule meta_mp)
  apply (frule vs_lookup_table_pt_at; clarsimp simp: pt_at_eq)
  apply (erule (1) is_subject_trans)
  apply (clarsimp simp: pas_refined_def auth_graph_map_def)
  apply (erule subsetD, clarsimp)
  apply (rule exI conjI refl sta_vref)+
  apply (erule state_vrefsD)
    apply (fastforce simp: pts_of_Some)
   apply clarsimp
  apply (frule_tac pt_ptr=pt_ptr in pspace_aligned_pts_ofD, simp)
  apply (clarsimp simp: ptes_of_def obind_def is_PageTablePTE_def vs_refs_aux_def split: option.splits)
  apply (drule_tac g=y and f="pte_ref2 level" in graph_of_comp)
   apply (fastforce simp: pte_ref2_def)
  apply (fastforce simp: aobjs_of_Some pts_of_Some pptr_from_pte_def
                   dest: table_index_max_level_slots
                   elim: rev_bexI rev_bexI_minus
                 intro!: pts_of_Some_alignedD)
  done

lemma pt_lookup_slot_from_level_is_subject:
  "\<lbrakk> pas_refined aag s; valid_vspace_objs s; valid_asid_table s; pspace_aligned s;
     pt_lookup_slot_from_level level bot_level pt_ptr vptr (ptes_of s) = Some (level', pt);
     (\<exists>asid. vs_lookup_table level asid vptr s = Some (level, pt_ptr));
     level \<le> max_pt_level; vptr \<in> user_region; is_subject aag pt_ptr \<rbrakk>
     \<Longrightarrow> is_subject aag (table_base pt)"
  by (fastforce dest: pt_walk_is_aligned vs_lookup_table_is_aligned pt_walk_is_subject
                simp: pt_lookup_slot_from_level_def obind_def split: option.splits)

lemma pt_lookup_from_level_is_subject:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<and>
        is_subject aag pt_ptr \<and> level \<le> max_pt_level \<and> vref \<in> user_region \<and>
        (\<exists>asid. vs_lookup_table level asid vref s = Some (level, pt_ptr))\<rbrace>
   pt_lookup_from_level level pt_ptr vref pt
   \<lbrace>\<lambda>rv _. is_subject aag (table_base rv)\<rbrace>, -"
  apply (wpsimp wp: pt_lookup_from_level_wp)
  apply (erule_tac level=level and bot_level=levela and pt_ptr=pt_ptr and vptr=vref
                in pt_lookup_slot_from_level_is_subject)
  by (auto simp: pt_lookup_slot_from_level_def obind_def)

lemma unmap_page_table_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs
                       and K (is_subject_asid aag asid \<and> vaddr \<in> user_region)\<rbrace>
   unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: unmap_page_table_def sfence_def)
  apply (wpsimp wp: pt_lookup_from_level_is_subject dmo_mol_respects hoare_vcg_conj_liftE
                    store_pte_respects pt_lookup_from_level_wrp[where Q="\<lambda>_. integrity aag X st"]
         | wp (once) hoare_drop_imps hoare_vcg_E_elim)+
  apply (intro conjI; clarsimp)
    apply fastforce
   apply (rule aag_Control_into_owns[rotated], assumption)
   apply (drule sym)
   apply (clarsimp simp: vspace_for_asid_def obj_at_def pas_refined_def)
   apply (erule_tac A="state_asids_to_policy_aux _ _ _ _" in subsetD)
   apply (rule sata_asid_lookup)
    apply (simp add: vspace_for_pool_def pool_for_asid_def)
   apply (clarsimp simp: vspace_for_pool_def)
   apply (drule pool_for_asid_vs_lookupD)
   apply (erule state_vrefsD)
     apply (fastforce simp: aobjs_of_Some asid_pools_of_ko_at obj_at_def)
    apply assumption
   apply (fastforce simp: vs_refs_aux_def graph_of_def asid_low_bits_of_mask_eq[symmetric]
                          word_size ucast_ucast_b is_up_def source_size_def target_size_def)
  apply (fastforce dest: vs_lookup_table_vref_independent[OF vspace_for_asid_vs_lookup])
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
   apply (wpsimp wp: set_cap_integrity_autarch store_pte_respects
               simp: authorised_page_table_inv_def sfence_def)
  apply (rename_tac cap fst_cslot_ptr snd_cslot_ptr)
  apply (wpsimp wp: set_cap_integrity_autarch)
     apply (rule_tac I="\<lambda>s. integrity aag X st s \<and> is_subject aag fst_cslot_ptr \<and> is_PageTableCap cap"
                  in mapM_x_inv_wp; clarsimp)
      apply (rule_tac P="\<lambda>s. integrity aag X st s \<and> is_PageTableCap cap" in hoare_vcg_conj_lift)
       apply (wpsimp wp: store_pte_respects)
       apply (clarsimp simp: authorised_page_table_inv_def)
       apply (case_tac cap; clarsimp)
      apply (wpsimp wp: unmap_page_table_respects)+
  apply (clarsimp simp: authorised_page_table_inv_def valid_pti_def valid_arch_cap_def
                        wellformed_acap_def wellformed_mapdata_def
                 split: arch_cap.splits)
  done

definition authorised_slots :: "'a PAS \<Rightarrow> pte \<times> obj_ref \<Rightarrow> 's :: state_ext state \<Rightarrow>  bool" where
 "authorised_slots aag m s \<equiv> case m of (pte, slot) \<Rightarrow>
    (\<forall>level asid vref x.
       vs_lookup_slot level asid vref s = Some (level, slot) \<longrightarrow>
       vref \<in> user_region \<longrightarrow>
       level \<le> max_pt_level \<longrightarrow>
       pte_ref2 level pte = Some x \<longrightarrow>
         (\<forall>a \<in> snd (snd x). \<forall>p \<in> ptr_range (fst x) (fst (snd x)). aag_has_auth_to aag a p)) \<and>
                                                                   is_subject aag (table_base slot)"

definition authorised_page_inv :: "'a PAS \<Rightarrow> page_invocation \<Rightarrow> 's :: state_ext state \<Rightarrow>  bool" where
  "authorised_page_inv aag pgi s \<equiv> case pgi of
     PageMap cap ptr slots \<Rightarrow> pas_cap_cur_auth aag (ArchObjectCap cap) \<and>
                              is_subject aag (fst ptr) \<and> authorised_slots aag slots s
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
  for level_of_table[wp]: "\<lambda>s. P (level_of_table p s)"
  (simp: level_of_table_def)

lemma set_cap_authorised_page_inv[wp]:
  "set_cap param_a param_b \<lbrace>\<lambda>s. P (authorised_page_inv aag (PageMap cap ct_slot entries) s)\<rbrace> "
  apply (clarsimp simp: authorised_page_inv_def authorised_slots_def)
  apply (rule hoare_pre)
   apply wps
   apply wp
  apply clarsimp
  done

lemma set_cap_same_ref[wp]:
  "set_cap param_a param_b \<lbrace>\<lambda>s. P (same_ref pte_slot cap s)\<rbrace> "
  apply (case_tac pte_slot; clarsimp)
  apply (clarsimp simp: same_ref_def)
  apply (rule hoare_pre)
   apply wps
   apply wp
  apply clarsimp
  done

lemma perform_pg_inv_map_pas_refined:
  "\<lbrace>pas_refined aag and invs and valid_page_inv (PageMap cap ct_slot (pte,slot))
                    and authorised_page_inv aag (PageMap cap ct_slot (pte,slot))\<rbrace>
   perform_pg_inv_map cap ct_slot pte slot
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pg_inv_map_def
  apply (wpsimp simp: simp: pas_refined_def state_objs_to_policy_def)
    apply (subst conj_commute, subst conj_commute)
    apply clarsimp
    apply (rule hoare_vcg_conj_lift, wpsimp)
    apply wps
    apply (rule state_vrefs_store_NonPageTablePTE_wp)
   apply (rule_tac Q="\<lambda>_. invs and pas_refined aag and K (\<not> is_PageTablePTE pte)
                               and authorised_page_inv aag (PageMap cap ct_slot (pte,slot))
                               and same_ref (pte,slot) (ArchObjectCap cap)"
                in hoare_strengthen_post[rotated])
    apply (clarsimp simp: pas_refined_def)
    apply (rule conjI)
     apply clarsimp
     apply (intro exI, rule conjI, assumption)
     apply clarsimp
     apply (rule conjI)
      apply clarsimp
      apply (erule_tac A="state_asids_to_policy_aux _ _ _ _" in subsetD)
      apply (erule state_asids_to_policy_aux.cases)
        apply (fastforce dest: sata_asid)
       apply (clarsimp simp: cte_wp_at_caps_of_state)
       apply (clarsimp simp only: split: if_splits)
        apply (clarsimp simp: vs_refs_aux_def)
       apply (erule sata_asid_lookup)
       apply assumption
      apply (fastforce dest: sata_asidpool)
     apply (clarsimp simp: auth_graph_map_def authorised_page_inv_def)
     apply (erule state_bits_to_policy.cases)
           apply (fastforce dest: sbta_caps simp: state_objs_to_policy_def)
          apply (fastforce dest: sbta_untyped simp: state_objs_to_policy_def)
         apply (fastforce dest: sbta_ts simp: state_objs_to_policy_def)
        apply (fastforce dest: sbta_bounds simp: state_objs_to_policy_def)
       apply (fastforce dest: sbta_cdt simp: state_objs_to_policy_def)
      apply (fastforce dest: sbta_cdt_transferable simp: state_objs_to_policy_def)
     apply (clarsimp split: if_split_asm)
      apply (clarsimp simp: vs_refs_aux_def graph_of_def)
      apply (erule_tac P="_ \<in> _" in swap)
      apply (case_tac "level = asid_pool_level")
       apply (fastforce dest!: vs_lookup_slot_no_asid
                         simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
      apply (clarsimp split: if_split_asm)
       apply (case_tac pte; clarsimp simp: authorised_slots_def)
      apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
      apply (erule subsetD)
      apply (clarsimp simp: state_objs_to_policy_def)
      apply (rule exI, rule conjI, rule refl)+
      apply (rule sbta_vref)
      apply (erule state_vrefsD)
        apply (fastforce simp: aobjs_of_Some obj_at_def)
       apply fastforce
      apply (fastforce simp: vs_refs_aux_def graph_of_def)
     apply (fastforce dest: sbta_vref simp: state_objs_to_policy_def)
    apply (clarsimp simp: same_ref_def)
   apply (wpsimp wp: arch_update_cap_invs_map set_cap_pas_refined_not_transferable)
  apply (clarsimp simp: valid_page_inv_def authorised_page_inv_def cte_wp_at_caps_of_state
                        is_frame_cap_def is_arch_update_def cap_master_cap_def
                 split: arch_cap.splits)
  apply (rule conjI)
   apply (fastforce dest: vs_lookup_slot_unique_level simp: same_ref_def parent_for_refs_def)
  apply (fastforce dest: vs_lookup_slot_unique_level caps_of_state_valid
                   simp: valid_arch_cap_def valid_cap_def cap_aligned_def)
  done

lemma perform_page_invocation_pas_refined:
  "\<lbrace>pas_refined aag and invs and authorised_page_inv aag pgi and valid_page_inv pgi\<rbrace>
   perform_page_invocation pgi
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: perform_page_invocation_def)
  apply (wpsimp wp: perform_pg_inv_map_pas_refined perform_pg_inv_unmap_pas_refined)
  apply auto
  done

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
          apply (fastforce simp: valid_arch_state_asid_table
                           dest: vs_lookup_table_vref_independent[OF vspace_for_asid_vs_lookup])+
   apply (erule (1) is_subject_asid_trans)
   apply (clarsimp simp: pas_refined_def vspace_for_asid_def vspace_for_pool_def)
   apply (erule subsetD[where A="state_asids_to_policy_aux _ _ _ _"])
   apply (rule sata_asid_lookup)
    apply (fastforce simp: pool_for_asid_def)
   apply (frule pool_for_asid_vs_lookupD)
   apply (erule state_vrefsD)
     apply (fastforce simp: vspace_for_pool_def opt_map_def split: option.splits)
    apply assumption
   apply (fastforce simp: vs_refs_aux_def graph_of_def asid_low_bits_of_mask_eq[symmetric] word_size
                          ucast_ucast_b ucast_up_ucast_id is_up_def source_size_def target_size_def)
  apply simp
  done

lemma perform_page_invocation_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and authorised_page_inv aag pgi
                       and valid_page_inv pgi and valid_vspace_objs
                       and pspace_aligned and valid_vspace_objs and valid_arch_state
                       and is_subject aag  \<circ> cur_thread\<rbrace>
   perform_page_invocation pgi
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
proof -
  have set_tl_subset_mp: "\<And>xs a. a \<in> set (tl xs) \<Longrightarrow> a \<in> set xs" by (case_tac xs; clarsimp)
  show ?thesis
    apply (unfold authorised_page_inv_def)
    apply (simp add: perform_page_invocation_def mapM_discarded swp_def valid_page_inv_def
                     valid_unmap_def authorised_page_inv_def authorised_slots_def
                     perform_pg_inv_map_def perform_pg_inv_unmap_def sfence_def
              split: page_invocation.split sum.split
                     arch_cap.split option.split, safe)
       apply ((wp set_cap_integrity_autarch unmap_page_respects
                  mapM_x_and_const_wp[OF store_pte_respects] store_pte_respects
              | elim conjE
              | clarsimp dest!: set_tl_subset_mp
              | wpc)+)
     apply (rule conjI)
      apply (case_tac m; clarsimp)
      apply (clarsimp simp: aag_cap_auth_def cte_wp_at_caps_of_state)
      apply (prop_tac "a \<in> acap_asid' (FrameCap r R sz dev (Some (a,b)))", clarsimp)
      apply (drule (1) sata_asid[where aag=aag])
      apply (clarsimp simp: pas_refined_def)
      apply (drule (1) subsetD)
      apply (fastforce dest: aag_wellformed_Control)
     apply (fastforce simp: valid_arch_cap_def wellformed_mapdata_def split: if_splits)
    apply (wpsimp wp: set_mrs_integrity_autarch set_message_info_integrity_autarch
                simp: ipc_buffer_has_auth_def perform_pg_inv_get_addr_def)
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
     (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of asid \<longrightarrow> is_subject_asid aag asid') \<rbrakk>
     \<Longrightarrow> integrity aag X st (s\<lparr>arch_state :=
                               arch_state s\<lparr>riscv_asid_table := \<lambda>a. if a = asid_high_bits_of asid
                                                                    then v
                                                                    else atable a\<rparr>\<rparr>)"
  by (clarsimp simp: integrity_def)

lemma asid_table_entry_update_integrity:
 "\<lbrace>integrity aag X st and (\<lambda>s. atable = riscv_asid_table (arch_state s))
                      and K (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of asid
                                     \<longrightarrow> is_subject_asid aag asid')\<rbrace>
  modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := atable(asid_high_bits_of asid := v)\<rparr>\<rparr>)
  \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by wpsimp (blast intro: integrity_asid_table_entry_update')

lemma perform_asid_control_invocation_respects:
  "\<lbrace>integrity aag X st and invs and valid_aci aci and K (authorised_asid_control_inv aag aci)\<rbrace>
   perform_asid_control_invocation aci
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: perform_asid_control_invocation_def)
  apply (wpc, simp)
   apply (wpsimp wp: set_cap_integrity_autarch cap_insert_integrity_autarch
                     asid_table_entry_update_integrity retype_region_integrity[where sz=12]
                     static_imp_wp delete_objects_valid_vspace_objs delete_objects_valid_arch_state)
  apply (clarsimp simp: authorised_asid_control_inv_def ptr_range_def add.commute range_cover_def
                        obj_bits_api_def default_arch_object_def pageBits_def word_bits_def)
  apply (subst is_aligned_neg_mask_eq[THEN sym], assumption)
  apply (clarsimp simp: and_mask_eq_iff_shiftr_0 mask_zero word_size_bits_def )
  done

lemma state_vrefs_asid_pool_map:
  "\<lbrakk> ako_at (ASIDPool Map.empty) frame s; asid_table s (asid_high_bits_of base) = None \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := \<lambda>a. if a = asid_high_bits_of base
                                                                           then Some frame
                                                                           else asid_table s a\<rparr>\<rparr>)
         = state_vrefs s"
  apply (rule all_ext)
  apply clarsimp
  apply safe
   apply (subst (asm) state_vrefs_def, clarsimp)
   apply (case_tac "asid_high_bits_of asid = asid_high_bits_of base")
    apply (clarsimp simp: vs_lookup_table_def pool_for_asid_def vspace_for_pool_def graph_of_def
                          asid_pools_of_ko_at obj_at_def vs_refs_aux_def aobjs_of_Some
                   split: if_splits)
   apply (subst (asm) asid_update.vs_lookup_table[simplified fun_upd_def])
    apply (clarsimp simp: asid_update_def asid_pools_of_ko_at)
   apply (clarsimp split: if_splits)
   apply (erule (3) state_vrefsD)
  apply (subst (asm) state_vrefs_def, clarsimp)
  apply (case_tac "asid_high_bits_of asid = asid_high_bits_of base")
   apply (clarsimp simp: vs_lookup_table_def pool_for_asid_def)
  apply (rule_tac level=bot and asid=asid and vref=vref in state_vrefsD)
     apply (subst asid_update.vs_lookup_table[simplified fun_upd_def])
      apply (clarsimp simp: asid_update_def asid_pools_of_ko_at)
     apply fastforce
    apply (fastforce simp: aobjs_of_Some)
   apply clarsimp
  apply clarsimp
  done

lemma pas_refined_asid_control_helper:
  "authorised_asid_control_inv aag (MakePool frame slot parent base) \<Longrightarrow>
  \<lbrace>\<lambda>s. pas_refined aag s \<and> ko_at (ArchObj (ASIDPool Map.empty)) frame s
                         \<and> asid_table s (asid_high_bits_of base) = None\<rbrace>
  do asid_table <- gets (riscv_asid_table \<circ> arch_state);
     asid_table' <- return (asid_table(asid_high_bits_of base \<mapsto> frame));
     modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := asid_table'\<rparr>\<rparr>)
  od
  \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding pas_refined_def
  apply wpsimp
  apply (rule conjI)
   apply (clarsimp simp: auth_graph_map_def state_objs_to_policy_def)
   apply (erule state_bits_to_policy.cases)
         apply (fastforce dest: sbta_caps)
        apply (fastforce dest: sbta_untyped)
       apply (fastforce dest: sbta_ts)
      apply (fastforce dest: sbta_bounds)
     apply (fastforce dest: sbta_cdt)
    apply (fastforce dest: sbta_cdt_transferable)
   apply (fastforce dest: sbta_vref simp: state_vrefs_asid_pool_map)
  apply clarsimp
  apply (erule state_asids_to_policy_aux.cases)
    apply (fastforce dest: sata_asid)
  apply (subst (asm) state_vrefs_asid_pool_map; clarsimp)
  apply (case_tac "asid_high_bits_of asid = asid_high_bits_of base")
  apply (clarsimp simp: state_vrefs_def aobjs_of_Some obj_at_def vs_refs_aux_def graph_of_def)
  apply (drule sata_asid_lookup[rotated]; fastforce)
  apply (clarsimp split: if_splits)
  apply (fastforce simp: authorised_asid_control_inv_def is_aligned_no_overflow aag_wellformed_refl)
  apply (fastforce dest: sata_asidpool)
  done

(* FIXME ryanb: include with retype_region_invs_extras *)
thm retype_region_invs_extras
lemma retype_region_invs_extras_vspace_objs:
  "\<lbrace>invs and pspace_no_overlap_range_cover ptr sz and caps_no_overlap ptr sz
         and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
         and region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
         and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and>
                         cap_is_device c = dev) slot s)
         and K (ty = CapTableObject \<longrightarrow> 0 < us)
         and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
   retype_region ptr n us ty dev
   \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  by (wp hoare_strengthen_post[OF retype_region_post_retype_invs], auto simp: post_retype_invs_def)

lemma perform_asid_control_invocation_pas_refined:
  "\<lbrace>pas_refined aag and pas_cur_domain aag and invs and valid_aci aci and ct_active
                    and K (authorised_asid_control_inv aag aci)\<rbrace>
   perform_asid_control_invocation aci
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: perform_asid_control_invocation_def )
  apply wpc
   apply (rule pas_refined_asid_control_helper hoare_seq_ext hoare_K_bind)+
         apply (wp cap_insert_pas_refined' static_imp_wp | simp)+
      apply ((wp retype_region_pas_refined'[where sz=pageBits]
                 hoare_vcg_ex_lift hoare_vcg_all_lift static_imp_wp hoare_wp_combs hoare_drop_imp
                 retype_region_invs_extras(4)[where sz = pageBits]
                 retype_region_invs_extras(6)[where sz = pageBits]
                 retype_region_invs_extras(1)[where sz = pageBits]
                 retype_region_invs_extras_vspace_objs[where sz = pageBits]
                 retype_region_cte_at_other'[where sz=pageBits]
                 max_index_upd_invs_simple max_index_upd_caps_overlap_reserved
                 hoare_vcg_ex_lift set_cap_cte_wp_at hoare_vcg_disj_lift set_free_index_valid_pspace
                 set_cap_descendants_range_in set_cap_no_overlap get_cap_wp set_cap_caps_no_overlap
                 hoare_vcg_all_lift static_imp_wp retype_region_invs_extras
                 set_cap_pas_refined_not_transferable arch_update_cap_valid_mdb
             | simp add: do_machine_op_def region_in_kernel_window_def cte_wp_at_neg2)+)[3]
   apply (rename_tac frame slot parent base )
   apply (case_tac slot, rename_tac slot_ptr slot_idx)
   apply (case_tac parent, rename_tac parent_ptr parent_idx)
   apply (rule_tac Q="\<lambda>rv s.
             (\<exists>idx. cte_wp_at ((=) (UntypedCap False frame pageBits idx)) parent s) \<and>
             (\<forall>x\<in>ptr_range frame pageBits. is_subject aag x) \<and>
             pas_refined aag s \<and> pas_cur_domain aag s \<and>
             pspace_no_overlap_range_cover frame pageBits s \<and>
             invs s \<and> asid_table s (asid_high_bits_of base) = None \<and>
             descendants_range_in {frame..(frame && ~~ mask pageBits) + 2 ^ pageBits - 1} parent s \<and>
             range_cover frame pageBits (obj_bits_api (ArchObject ASIDPoolObj) 0) (Suc 0) \<and>
             is_subject aag slot_ptr \<and> is_subject aag parent_ptr \<and> is_subject aag frame \<and>
             pas_cap_cur_auth aag (ArchObjectCap (ASIDPoolCap frame base)) \<and>
             (\<forall>x. asid_high_bits_of x = asid_high_bits_of base \<longrightarrow> is_subject_asid aag x)"
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
                         cap_links_asid_slot_def cap_links_irq_def obj_bits_api_def
                         default_arch_object_def retype_addrs_def conj_ac
                         invs_psp_aligned invs_valid_pspace invs_vspace_objs invs_arch_state)
   apply (rule conjI, force intro: descendants_range_caps_no_overlapI simp: cte_wp_at_def)
   apply (rule conjI, clarsimp simp: max_free_index_def)
   apply (prop_tac "valid_cap (UntypedCap False frame pageBits idx) s")
    apply (clarsimp simp: get_cap_caps_of_state)
    apply (simp add: Untyped_AI.caps_of_state_valid)
   apply (clarsimp simp: free_index_of_def max_free_index_def valid_cap_def)
   apply (rule conjI)
    apply (cut_tac s=s and ptr="(parent_ptr, parent_idx)" in cap_refs_in_kernel_windowD)
      apply ((fastforce simp: caps_of_state_def cap_range_def)+)[3]
   apply (fastforce simp: x_power_minus_1 is_aligned_no_overflow')
  apply (clarsimp simp: valid_aci_def authorised_asid_control_inv_def cte_wp_at_caps_of_state)
  apply (rule conjI)
   apply (drule untyped_slots_not_in_untyped_range)
        apply (erule empty_descendants_range_in)
       apply (simp add: cte_wp_at_caps_of_state)
      apply simp
     apply simp
    apply (rule subset_refl)
   apply (simp add: page_bits_def)
  apply (frule_tac x=x in bspec)
   apply (simp add: is_aligned_no_overflow)
  apply (clarsimp simp: ptr_range_def invs_psp_aligned invs_valid_objs aag_cap_auth_def
                        descendants_range_def2 empty_descendants_range_in page_bits_def
                        pas_refined_refl cap_links_asid_slot_def label_owns_asid_slot_def
                        cap_links_irq_def range_cover_def obj_bits_api_def pageBits_def
                        default_arch_object_def and_mask_eq_iff_shiftr_0 mask_zero)
  apply (subst is_aligned_neg_mask_eq[THEN sym], assumption)
  apply (intro conjI; fastforce intro: empty_descendants_range_in)
  done


definition authorised_asid_pool_inv :: "'a PAS \<Rightarrow> asid_pool_invocation \<Rightarrow> bool" where
 "authorised_asid_pool_inv aag api \<equiv>
  case api of Assign asid pool_ptr ct_slot \<Rightarrow>
    is_subject aag pool_ptr \<and> is_subject aag (fst ct_slot) \<and> is_subject_asid aag asid"

(* FIXME ryanb: this is more general than pt_slot_offset_id *)
thm pt_slot_offset_id
lemma pt_slot_offset_id':
  "\<lbrakk> is_aligned pt_ptr pt_bits; mask pt_bits && (xa << pte_bits) = xa << pte_bits \<rbrakk>
     \<Longrightarrow> table_base (pt_ptr + (xa << pte_bits)) = pt_ptr"
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
     apply (clarsimp simp: pte_bits_def word_size_bits_def pt_bits_def
                           table_size_def ptTranslationBits_def mask_def)
     apply (word_bitwise, fastforce)
    apply clarsimp
   apply wpsimp+
  done

lemma perform_asid_pool_invocation_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs and valid_apinv api
                       and K (authorised_asid_pool_inv aag api)\<rbrace>
   perform_asid_pool_invocation api
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (unfold perform_asid_pool_invocation_def store_asid_pool_entry_def)
  apply (wpsimp wp: set_asid_pool_integrity_autarch get_cap_wp set_cap_integrity_autarch
                    copy_global_mappings_integrity hoare_drop_imps)
  apply (clarsimp simp: authorised_asid_pool_inv_def valid_apinv_def cte_wp_at_caps_of_state is_cap_simps)
  apply (rule conjI)
   apply (rule is_aligned_pt; fastforce simp: valid_cap_def dest: caps_of_state_valid)
  apply (frule_tac ptr="(a,b)" in sbta_caps)
    apply simp
   apply (simp add: cap_auth_conferred_def arch_cap_auth_conferred_def)
  apply (erule_tac x=a in is_subject_trans, assumption)
  apply (fastforce simp: pas_refined_def auth_graph_map_def state_objs_to_policy_def)
  done

lemma store_pte_state_vrefs_unreachable:
  "\<lbrace>\<lambda>s. P (state_vrefs s) \<and> pspace_aligned s \<and> valid_vspace_objs s \<and>
        valid_asid_table s \<and> (\<forall>level. \<not> \<exists>\<rhd> (level, table_base p) s)\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  supply fun_upd_apply[simp del]
  apply (wpsimp simp: store_pte_def set_pt_def wp: set_object_wp)
  apply (erule rsubst[where P=P])
  apply (rule all_ext)
  apply safe
   apply (subst (asm) state_vrefs_def, clarsimp)
   apply (rule state_vrefsD)
      apply (subst vs_lookup_table_unreachable_upd_idem)
          apply fastforce+
    apply (drule vs_lookup_level)
    apply (prop_tac "x \<noteq> table_base p", clarsimp)
    apply (fastforce simp: fun_upd_def aobjs_of_Some opt_map_def)
   apply clarsimp
  apply (subst (asm) state_vrefs_def, clarsimp)
  apply (rule state_vrefsD)
     apply (subst (asm) vs_lookup_table_unreachable_upd_idem; fastforce)
    apply (prop_tac "x \<noteq> table_base p")
     apply (subst (asm) vs_lookup_table_unreachable_upd_idem; fastforce dest: vs_lookup_level)
    apply (fastforce simp: fun_upd_def aobjs_of_Some)
   apply clarsimp
  apply clarsimp
  done

(* FIXME ryanb: manipulate the original? *)
thm not_in_global_refs_vs_lookup
lemma not_in_global_refs_vs_lookup:
  "(\<exists>\<rhd> (level,p)) s \<and> valid_vs_lookup s \<and> valid_global_refs s
            \<and> valid_arch_state s \<and> valid_global_objs s
            \<and> pt_at p s
        \<Longrightarrow> p \<notin> global_refs s"
  using not_in_global_refs_vs_lookup by blast

(* FIXME ryanb: original has unnecessary condition *)
thm store_pte_valid_vs_lookup_unreachable
lemma store_pte_valid_vs_lookup_unreachable:
  "\<lbrace>valid_vs_lookup and pspace_aligned and valid_vspace_objs and valid_asid_table and
    (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, table_base p) s)\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  unfolding valid_vs_lookup_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' store_pte_vs_lookup_target_unreachable)
  apply (erule disjE; clarsimp)
  done

lemma copy_global_mappings_state_vrefs:
  "\<lbrace>\<lambda>s. P (state_vrefs s) \<and> invs s \<and> is_aligned pt_ptr pt_bits \<and> (\<forall>level. \<not> \<exists>\<rhd> (level, pt_ptr) s)\<rbrace>
   copy_global_mappings pt_ptr
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  unfolding copy_global_mappings_def
  apply clarsimp
  apply wp
    apply (rule_tac Q="\<lambda>_ s. P (state_vrefs s) \<and> pspace_aligned s \<and> valid_vspace_objs s \<and>
                             valid_asid_table s \<and> unique_table_refs s \<and> valid_vs_lookup s \<and>
                             valid_objs s \<and> is_aligned pt_ptr pt_bits \<and> is_aligned global_pt pt_bits \<and>
                             (\<forall>level. \<not> \<exists>\<rhd> (level, table_base (pt_ptr)) s) \<and>
                             (\<forall>level. \<not> \<exists>\<rhd> (level, table_base (global_pt)) s)"
                 in hoare_strengthen_post[rotated], clarsimp)
    apply (wpsimp wp: store_pte_state_vrefs_unreachable store_pte_valid_vs_lookup_unreachable
                      store_pte_vs_lookup_table_unreachable store_pte_valid_vspace_objs
                      hoare_vcg_all_lift hoare_vcg_imp_lift' mapM_x_wp')
    apply (prop_tac "table_base (pt_ptr + (x << pte_bits)) = pt_ptr \<and>
                     table_base (global_pt + (x << pte_bits)) = global_pt")
     apply (metis mask_2pm1 table_base_plus)
    apply (fastforce simp: valid_objs_caps ptes_of_wellformed_pte)
   apply wpsimp+
  apply (simp add: invs_valid_global_vspace_mappings)
  apply (intro conjI; clarsimp)
  apply (frule invs_valid_global_arch_objs)
  apply (frule valid_global_arch_objs_pt_at)
  using not_in_global_refs_vs_lookup apply fastforce
  done

crunches copy_global_mappings
  for tcb_domain_map_wellformed[wp]: "\<lambda>s. P (tcb_domain_map_wellformed aag s)"
  and asid_table[wp]: "\<lambda>s. P (asid_table s)"
  and cdt[wp]: "\<lambda>s. P (cdt s)"
  and thread_states[wp]: "\<lambda>s. P (thread_states s)"
  and thread_bound_ntfns[wp]: "\<lambda>s. P (thread_bound_ntfns s)"
  (wp: crunch_wps)

lemma copy_global_mappings_pas_refined:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> invs s \<and> is_aligned pt_ptr pt_bits \<and> (\<forall>level. \<not> \<exists>\<rhd> (level, pt_ptr) s)\<rbrace>
   copy_global_mappings pt_ptr
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (clarsimp simp: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wps)
   apply (wpsimp wp: copy_global_mappings_state_vrefs)+
  done

lemma store_asid_pool_entry_state_vrefs:
  "\<lbrace>\<lambda>s. P (\<lambda>x. if x = pool_ptr
               then vs_refs_aux asid_pool_level (ASIDPool (\<lambda>a. if a = asid_low_bits_of asid
                                                               then Some pt_base
                                                               else the (asid_pools_of s pool_ptr) a))
               else if x = pt_base
               then vs_refs_aux max_pt_level (the (aobjs_of s x))
               else state_vrefs s x) \<and>
        pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<and>
        pool_for_asid asid s = Some pool_ptr \<and>
        (\<forall>pool. ako_at (ASIDPool pool) pool_ptr s \<longrightarrow> pool (asid_low_bits_of asid) = None) \<and>
        (\<forall>level. \<not>\<exists>\<rhd> (level, pt_base) s) \<and>
        (\<exists>pt. pts_of s pt_base = Some pt \<and> kernel_mappings_only pt s)\<rbrace>
   store_asid_pool_entry pool_ptr asid (Some pt_base)
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
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
     apply (frule pool_for_asid_vs_lookupD)
     apply (rule_tac level=asid_pool_level in state_vrefsD)
        apply (simp only: fun_upd_def)
        apply (subst asid_pool_map.vs_lookup_table[simplified fun_upd_def])
         apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at
                                valid_apinv_def asid_low_bits_of_def aobjs_of_Some)
        apply fastforce
       apply fastforce
      apply (fastforce simp: ako_asid_pools_of)
     apply (clarsimp simp: ako_asid_pools_of)
    (* x = acap_obj acap *)
    apply (rule_tac level=max_pt_level and vref=0 in state_vrefsD)
       apply (simp only: fun_upd_def)
       apply (subst asid_pool_map.vs_lookup_table[simplified fun_upd_def])
         apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at
                                valid_apinv_def asid_low_bits_of_def aobjs_of_Some)
       apply clarsimp
      apply fastforce
     apply (fastforce simp: pts_of_Some)
    apply (fastforce simp: pts_of_Some)
   (* x is none of the above *)
   apply (clarsimp simp: obj_at_def)
   apply (subst (asm) state_vrefs_def, clarsimp)
   apply (rule_tac asid=asida in state_vrefsD)
      apply (simp only: fun_upd_def)
      apply (subst asid_pool_map.vs_lookup_table[simplified fun_upd_def])
         apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at obj_at_def
                                valid_apinv_def asid_low_bits_of_def aobjs_of_Some)
      apply fastforce
     apply (prop_tac "asid \<noteq> asida")
      apply (fastforce simp: vs_lookup_table_def vspace_for_pool_def asid_pools_of_ko_at obj_at_def
                      split: if_splits)
     apply fastforce
    apply fastforce
   apply clarsimp
  (* second direction *)
  apply (subst (asm) state_vrefs_def, clarsimp split del: if_split)
  apply (simp only: fun_upd_def)
  apply (subst (asm) asid_pool_map.vs_lookup_table[simplified fun_upd_def])
    apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at
                           valid_apinv_def asid_low_bits_of_def aobjs_of_Some)
   apply clarsimp
  apply (case_tac "x = pool_ptr")
   apply (prop_tac "asid_pools_of s pool_ptr = Some pool")
    apply (clarsimp simp: asid_pools_of_ko_at obj_at_def)
   apply (clarsimp simp: vs_refs_aux_def)
  apply (case_tac "asida = asid \<and> bot \<le> max_pt_level"; clarsimp)
  apply (case_tac "x = pt_base")
   apply (fastforce dest: vs_lookup_level)
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
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<and>
        pool_for_asid asid s = Some pool_ptr \<and> is_subject aag pool_ptr \<and>
        is_subject aag pt_base \<and> is_subject_asid aag asid \<and>
        (\<forall>level. \<not>\<exists>\<rhd> (level, pt_base) s) \<and>
        (\<forall>pool. ako_at (ASIDPool pool) pool_ptr s \<longrightarrow> pool (asid_low_bits_of asid) = None) \<and>
        (\<exists>pt. pts_of s pt_base = Some pt \<and> kernel_mappings_only pt s)\<rbrace>
   store_asid_pool_entry pool_ptr asid (Some pt_base)
   \<lbrace>\<lambda>_ s. pas_refined aag s\<rbrace>"
  apply (clarsimp simp: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply wps
   apply (wp store_asid_pool_entry_state_vrefs store_asid_pool_entry_state_vrefs)
  apply (clarsimp simp: auth_graph_map_def)
  apply (frule (1) pool_for_asid_validD)
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (erule state_bits_to_policy.cases)
         apply (fastforce simp: state_objs_to_policy_def dest: sbta_caps)
        apply (fastforce simp: state_objs_to_policy_def dest: sbta_untyped)
       apply (fastforce simp: state_objs_to_policy_def dest: sbta_ts)
      apply (fastforce simp: state_objs_to_policy_def dest: sbta_bounds)
     apply (fastforce simp: state_objs_to_policy_def dest: sbta_cdt)
    apply (fastforce simp: state_objs_to_policy_def dest: sbta_cdt_transferable)
   apply (case_tac "ptr = pool_ptr")
    apply (clarsimp simp: vs_refs_aux_def graph_of_def aag_wellformed_refl split: if_splits)
    apply (erule subsetD)
    apply clarsimp
    apply (rule_tac x=pool_ptr in exI, clarsimp)
    apply (rule exI, rule conjI, rule refl)
    apply (rule sbta_vref)
    apply (drule pool_for_asid_vs_lookupD)
    apply (erule_tac vref=0 in state_vrefsD)
      apply (simp add: asid_pools_of_ko_at aobjs_of_ako_at_Some)
     apply clarsimp
    apply (fastforce simp: vs_refs_aux_def graph_of_def)
   apply (fastforce simp: vs_refs_aux_def kernel_mappings_only_def
                          graph_of_def pts_of_Some pte_ref2_def
                    dest: sbta_vref split: if_splits)
  apply (erule state_asids_to_policy_aux.cases)
    apply (erule subsetD[where A="state_asids_to_policy_aux _ _ _ _"])
    apply (fastforce dest: sata_asid)
   apply (case_tac "poolptr = pool_ptr")
    apply (clarsimp simp: vs_refs_aux_def graph_of_def obj_at_def split: if_splits)
     apply (clarsimp simp: pool_for_asid_def asid_pools_of_ko_at valid_asid_table_def inj_on_def)
     apply (drule_tac x="asid_high_bits_of asid" in bspec, clarsimp)
     apply (drule_tac x="asid_high_bits_of asida" in bspec, clarsimp)
     apply clarsimp
     apply (drule asid_high_low)
      apply (simp add: asid_low_bits_of_mask_eq[symmetric])
      apply (prop_tac "is_up UCAST(9 \<rightarrow> 16) \<and> is_up UCAST(9 \<rightarrow> 64)")
       apply (clarsimp simp: is_up_def source_size_def target_size_def word_size)
      apply (clarsimp simp: ucast_ucast_b)
      apply (metis ucast_up_ucast_id)
     apply (fastforce simp: aag_wellformed_refl)
    apply (erule subsetD[where A="state_asids_to_policy_aux _ _ _ _"])
    apply (rule sata_asid_lookup, fastforce)
    apply (frule pool_for_asid_vs_lookupD)
    apply (erule_tac vref=0 in state_vrefsD)
      apply (simp add: asid_pools_of_ko_at aobjs_of_ako_at_Some)
     apply simp
    apply (fastforce simp: vs_refs_aux_def graph_of_def)
   apply (case_tac "poolptr = pt_base")
    apply (clarsimp simp: vs_refs_aux_def pts_of_Some)
   apply (erule subsetD[where A="state_asids_to_policy_aux _ _ _ _"])
   apply (fastforce simp: sata_asid_lookup)
  apply (erule subsetD[where A="state_asids_to_policy_aux _ _ _ _"])
  apply (fastforce simp: sata_asidpool)
  done


lemma copy_global_mappings_vs_lookup_table_noteq:
  "\<lbrace>\<lambda>s. vs_lookup_table level asid vref s \<noteq> Some (level, pt_ptr) \<and> invs s \<and>
        is_aligned pt_ptr pt_bits \<and> vref \<in> user_region \<and> (\<forall>level. \<not> \<exists>\<rhd> (level, pt_ptr) s)\<rbrace>
   copy_global_mappings pt_ptr
   \<lbrace>\<lambda>_ s. vs_lookup_table level asid vref s \<noteq> Some (level, pt_ptr)\<rbrace>"
  unfolding copy_global_mappings_def
  apply clarsimp
  apply wp
    apply (rule_tac Q="\<lambda>_. pspace_aligned and valid_vspace_objs and valid_asid_table and
                           unique_table_refs and valid_vs_lookup and valid_objs and
                           (\<lambda>s. vs_lookup_table level asid vref s \<noteq> Some (level, pt_ptr) \<and>
                                vref \<in> user_region \<and> is_aligned pt_ptr pt_bits \<and>
                                (\<forall>level. \<not> \<exists>\<rhd> (level, table_base pt_ptr) s))"
                 in hoare_strengthen_post[rotated], clarsimp)
    apply (wpsimp wp: mapM_x_wp' store_pte_valid_vspace_objs store_pte_vs_lookup_table_unreachable
                      store_pte_valid_vs_lookup_unreachable hoare_vcg_all_lift hoare_vcg_imp_lift')
    apply (metis valid_objs_caps ptes_of_wellformed_pte mask_2pm1 table_base_plus)
   apply wpsimp
  apply fastforce
  done

lemma perform_asid_pool_invocation_pas_refined [wp]:
  "\<lbrace>pas_refined aag and invs and valid_apinv api and K (authorised_asid_pool_inv aag api)\<rbrace>
   perform_asid_pool_invocation api
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: perform_asid_pool_invocation_def)
  apply (strengthen invs_psp_aligned invs_vspace_objs valid_arch_state_asid_table invs_arch_state |
         wpsimp simp: ako_asid_pools_of
                  wp: copy_global_mappings_invs copy_global_mappings_pas_refined
                      copy_global_mappings_copies copy_global_mappings_vs_lookup_table_noteq
                      store_asid_pool_entry_pas_refined set_cap_pas_refined get_cap_wp
                      arch_update_cap_invs_map hoare_vcg_all_lift hoare_vcg_imp_lift')+
  apply (clarsimp simp: cte_wp_at_caps_of_state valid_apinv_def cong: conj_cong)
  apply (clarsimp simp: is_PageTableCap_def is_ArchObjectCap_def)
  apply (clarsimp split: option.splits)
  apply (clarsimp simp: authorised_asid_pool_inv_def)
  apply (prop_tac "(\<forall>x xa xb. vs_lookup_table x xa xb s = Some (x, x41) \<longrightarrow> xb \<notin> user_region)")
   apply (frule (1) caps_of_state_valid)
   apply (clarsimp simp: valid_cap_def)
   apply (clarsimp simp: obj_at_def)
   apply (rename_tac asid' pool_ptr a b acap_obj level asid vref pt)
   apply (drule (1) vs_lookup_table_valid_cap; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap, simp add: pts_of_Some aobjs_of_Some, fastforce intro: valid_objs_caps)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp)
   apply (clarsimp simp: is_cap_simps)
  apply (clarsimp simp: is_arch_update_def update_map_data_def is_cap_simps cap_master_cap_def asid_bits_of_defs)
  apply (intro conjI)
         apply (fastforce dest: cap_cur_auth_caps_of_state pas_refined_refl
                          simp: update_map_data_def aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                               cap_links_asid_slot_def label_owns_asid_slot_def cap_links_irq_def)
        apply (fastforce dest: caps_of_state_valid
                         simp: update_map_data_def valid_cap_def cap_aligned_def wellformed_mapdata_def)
       apply (fastforce dest: caps_of_state_aligned_page_table)
      apply (fastforce dest: unique_table_capsD[rotated])
     apply (fastforce dest: cap_not_in_valid_global_refs)
    apply (fastforce dest: cap_cur_auth_caps_of_state pas_refined_Control
                     simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def)
   apply fastforce
  apply (fastforce dest: invs_valid_table_caps simp: valid_table_caps_def)
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
  apply (wpsimp wp: perform_page_table_invocation_pas_refined perform_asid_pool_invocation_pas_refined
                    perform_page_invocation_pas_refined perform_asid_control_invocation_pas_refined)+
  apply (auto simp: authorised_arch_inv_def)
  done


lemma vspace_for_asid_vs_lookup':
  "asid_table s (asid_high_bits_of asid) = Some pt \<Longrightarrow>
   vs_lookup_table asid_pool_level asid 0 s = Some (asid_pool_level, pt)"
  by (clarsimp simp: vs_lookup_table_def obind_def pool_for_asid_def
                     vspace_for_pool_def asid_pools_of_ko_at obj_at_def
              split: option.splits)

lemma decode_arch_invocation_authorised_helper:
  "\<lbrakk> pas_refined aag s; valid_asid_table s; vspace_for_asid a s = Some xaa; is_subject_asid aag a \<rbrakk>
     \<Longrightarrow> is_subject aag xaa"
  apply (frule vspace_for_asid_vs_lookup)
  apply (clarsimp simp: vspace_for_asid_def)
  apply (frule (1) pool_for_asid_validD)
  apply (clarsimp simp: vspace_for_pool_def pool_for_asid_def asid_pools_of_ko_at obj_at_def)
  apply (frule_tac vrefs="state_vrefs s" in sata_asid_lookup)
   apply (rule_tac level=asid_pool_level and asid=a and vref=0 in state_vrefsD)
  by (fastforce simp: aobjs_of_Some vspace_for_asid_vs_lookup' vs_refs_aux_def graph_of_def
                      asid_low_bits_of_mask_eq[symmetric] ucast_ucast_b is_up_def source_size_def
                      target_size_def word_size aag_wellformed_Control pas_refined_def
                dest: aag_wellformed_Control)+

(* FIXME ryanb *)
lemma pt_walk_is_subject':
  "\<lbrakk> pt_walk level bot_level pt_ptr vptr (ptes_of s) = Some (level', pt);
     vs_lookup_table level asid vptr s = Some (level, pt_ptr);
     level \<le> max_pt_level; vptr \<in> user_region; is_subject aag pt_ptr;
     pas_refined aag s; valid_vspace_objs s; valid_asid_table s; pspace_aligned s \<rbrakk>
     \<Longrightarrow> is_subject aag pt"
sorry

lemma decode_page_table_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (is_PageTableCap cap \<and> (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                                          aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                          is_subject aag (fst slot) \<and>
                                          (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))\<rbrace>
   decode_page_table_invocation label msg slot cap excaps
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>, -"
  apply (rule hoare_gen_asmE)
  apply (clarsimp simp: is_PageTableCap_def)
  apply (rename_tac x xa)
  apply (unfold decode_page_table_invocation_def decode_pt_inv_map_def authorised_arch_inv_def)
  apply (wpsimp simp: Let_def is_final_cap_def if_fun_split)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (prop_tac "\<forall>y \<in> set [x, x + 2 ^ pte_bits .e. x + 2 ^ pt_bits - 1]. table_base y = x")
   apply (drule (1) caps_of_state_aligned_page_table)
   apply (clarsimp simp only: is_aligned_neg_mask_eq' add_mask_fold)
   apply (drule subsetD[OF upto_enum_step_subset], clarsimp)
   apply (drule neg_mask_mono_le[where n=pt_bits])
   apply (drule neg_mask_mono_le[where n=pt_bits])
   apply (fastforce dest: FIXME_wordAND_wordNOT_mask_plus)
  apply (intro conjI; clarsimp)
   apply (clarsimp simp: authorised_page_table_inv_def)
   apply (case_tac excaps; clarsimp)
   apply (rule conjI)
    apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def)
    apply (subst pt_slot_offset_id)
     apply (fastforce simp: cte_wp_at_caps_of_state
                      dest: caps_of_state_aligned_page_table pt_walk_is_aligned)
    apply (frule vs_lookup_table_vref_independent[OF vspace_for_asid_vs_lookup, simplified])
    apply (erule (1) pt_walk_is_subject'; fastforce intro: decode_arch_invocation_authorised_helper
                                                     simp: user_region_def user_vtop_canonical_user)
   apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                         cap_links_asid_slot_def label_owns_asid_slot_def cap_links_irq_def)
  apply (auto simp: caps_of_state_pasObjectAbs_eq authorised_page_table_inv_def
                    cap_auth_conferred_def arch_cap_auth_conferred_def)
  done

lemma decode_frame_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (is_FrameCap cap \<and> (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                                     aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                     is_subject aag (fst slot) \<and>
                                     (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))\<rbrace>
   decode_frame_invocation label msg slot cap excaps
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>,-"
  unfolding decode_frame_invocation_def authorised_arch_inv_def decode_fr_inv_map_def
  apply (wpsimp wp: check_vp_wpR simp: Let_def authorised_page_inv_def)
  apply (rule conj_imp_strg)
  apply (cases excaps; clarsimp)
  apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                        cap_links_asid_slot_def cap_links_irq_def authorised_slots_def)
  apply (prop_tac "msg ! 0 \<in> user_region")
   apply (fastforce dest: not_le_imp_less user_vtop_canonical_user
                    elim: dual_order.trans is_aligned_no_overflow_mask
                    simp: user_region_def vmsz_aligned_def)
  apply (rule conjI)
   apply (frule (1) pt_lookup_slot_vs_lookup_slotI, clarsimp)
   apply (drule (1) vs_lookup_slot_unique_level; clarsimp)
   apply (clarsimp simp: cte_wp_at_caps_of_state make_user_pte_def pte_ref2_def split: if_splits)
   apply (subst (asm) ptrFromPAddr_addr_from_ppn[OF is_aligned_pageBitsForSize_table_size])
    apply (fastforce dest: caps_of_state_valid
                     simp: valid_cap_def cap_aligned_def pageBitsForSize_pt_bits_left)
   apply (fastforce simp: vspace_cap_rights_to_auth_def mask_vm_rights_def validate_vm_rights_def
                          vm_kernel_only_def vm_read_only_def
                   split: if_splits)
  apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def)
  apply (subst pt_slot_offset_id)
   apply (fastforce simp: cte_wp_at_caps_of_state
                    dest: caps_of_state_aligned_page_table pt_walk_is_aligned)
  apply (frule vs_lookup_table_vref_independent[OF vspace_for_asid_vs_lookup, simplified])
  apply (erule (1) pt_walk_is_subject'; fastforce intro: decode_arch_invocation_authorised_helper)
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
