(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchADT_AC
imports ADT_AC
begin

context Arch begin global_naming ARM_A

named_theorems ADT_AC_assms

lemma invs_valid_global_pd_mappings:
  "invs s \<Longrightarrow> valid_global_vspace_mappings s"
  apply (simp add: invs_def valid_state_def)
  done

lemma objs_valid_tcb_vtable:
  "\<lbrakk> valid_objs s; get_tcb t s = Some tcb \<rbrakk> \<Longrightarrow> s \<turnstile> tcb_vtable tcb"
  apply (clarsimp simp: get_tcb_def split: option.splits Structures_A.kernel_object.splits)
  apply (erule cte_wp_valid_cap[rotated])
  apply (rule cte_wp_at_tcbI[where t="(a, b)" for a b, where b3="tcb_cnode_index 1"])
    apply fastforce+
  done


(* FIXME ryanb - weaken original *)
lemma get_page_info_gpd_kmaps:
  "\<lbrakk>valid_global_vspace_mappings s; valid_arch_state s;
    get_page_info (aobjs_of s) (riscv_global_pt (arch_state s)) p = Some (b, a, attr, r)\<rbrakk>
   \<Longrightarrow> p \<in> kernel_mappings"
  apply (clarsimp simp: get_page_info_def in_omonad pt_lookup_slot_def pt_lookup_slot_from_level_def)
  apply (subst (asm) pt_walk.simps)
  apply (fastforce dest: pte_info_not_InvalidPTE global_pt_not_invalid_kernel
                   simp: valid_arch_state_def in_omonad)
  done

lemma level_of_sz_vmpage_size_of_level[simp]:
  "level \<le> max_pt_level \<Longrightarrow> level_of_sz (vmpage_size_of_level level) = level"
  by (induct level; fastforce simp: level_of_sz_def vmpage_size_of_level_def max_pt_level_def2 split: if_splits)


lemma mask_ptTranslationBits_ucast_ucast:
  "((asid::machine_word) && mask ptTranslationBits) = ucast (ucast asid :: 9 word)"
  by (word_eqI simp: ptTranslationBits_def)

lemma table_index_offset_pt_bits_left:
  "is_aligned pt_ref pt_bits \<Longrightarrow>
   table_index (pt_slot_offset lvl pt_ref vref) = ucast (vref >> pt_bits_left lvl)"
apply (clarsimp simp: pt_slot_offset_def
pt_index_def mask_ptTranslationBits_ucast_ucast is_aligned_mask
)
  using is_aligned_neg_mask_eq' mask_eq_0_eq_x table_index_plus_ucast by blast


lemma ptrFromPAddr_plus: "ptrFromPAddr (x + y) = ptrFromPAddr x + y"
  by (simp add: ptrFromPAddr_def)

lemma ptr_offset_in_ptr_range:
  "\<lbrakk> invs s; x \<notin> kernel_mappings;
     get_vspace_of_thread (kheap s) (arch_state s) tcb \<noteq> global_pt s;
     get_page_info (aobjs_of s)
                   (get_vspace_of_thread (kheap s) (arch_state s) tcb) x = Some (base, sz, attr, r) \<rbrakk>
     \<Longrightarrow> ptrFromPAddr base + (x && mask sz) \<in> ptr_range (ptrFromPAddr base) sz"
  apply (simp add: ptr_range_def mask_def)
  apply (rule conjI)
   apply (rule_tac b="2 ^ sz - 1" in word_plus_mono_right2)
    apply (frule some_get_page_info_umapsD)
          apply (fastforce dest: get_vspace_of_thread_reachable
simp: invs_vspace_objs canonical_not_kernel_is_user get_page_info_def
                                invs_psp_aligned invs_valid_asid_table invs_valid_objs)+
    apply clarsimp
    apply (drule is_aligned_ptrFromPAddr_n)
     apply (simp add: pageBitsForSize_def pageBits_def canonical_bit_def ptTranslationBits_def split: vmpage_size.splits)
    apply (clarsimp simp: is_aligned_no_overflow' word_and_le1)+
  apply (subst p_assoc_help)
  apply (rule word_plus_mono_right)
   apply (rule word_and_le1)
  apply (frule some_get_page_info_umapsD)
          apply (fastforce dest: get_vspace_of_thread_reachable
simp: invs_vspace_objs canonical_not_kernel_is_user get_page_info_def
                                invs_psp_aligned invs_valid_asid_table invs_valid_objs)+
    apply clarsimp
  apply (drule is_aligned_ptrFromPAddr_n)
     apply (simp add: pageBitsForSize_def pageBits_def canonical_bit_def ptTranslationBits_def split: vmpage_size.splits)
  apply (clarsimp simp: is_aligned_no_overflow')
  done


lemma user_op_access[ADT_AC_assms]:
  "\<lbrakk> invs s; pas_refined aag s; is_subject aag tcb; ptable_lift tcb s x = Some ptr;
     auth \<in> vspace_cap_rights_to_auth (ptable_rights tcb s x) \<rbrakk>
     \<Longrightarrow> abs_has_auth_to aag auth tcb (ptrFromPAddr ptr)"
  apply (case_tac "x \<in> kernel_mappings")
   apply (clarsimp simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings
                          ptable_lift_def ptable_rights_def vspace_cap_rights_to_auth_def
                    dest: some_get_page_info_kmapsD split: option.splits)

apply (drule some_get_page_info_kmapsD)
apply clarsimp
apply clarsimp
  using kernel_mappings_canonical apply blast
apply fastforce
apply fastforce
apply (clarsimp simp: invs_def valid_state_def valid_arch_state_def)
apply (clarsimp simp: invs_def valid_state_def valid_arch_state_def)
apply fastforce
apply fastforce
apply fastforce
apply fastforce
  using get_vspace_of_thread_asid_or_global_pt apply blast
apply fastforce

apply (clarsimp simp: ptable_lift_def split: option.splits)

apply (insert get_vspace_of_thread_asid_or_global_pt)
apply (erule_tac x=s in meta_allE)
apply (erule_tac x=tcb in meta_allE)

apply (case_tac "get_vspace_of_thread (kheap s) (arch_state s) tcb = global_pt s")
apply clarsimp

apply (drule get_page_info_gpd_kmaps[rotated 2])
apply fastforce
apply fastforce
apply fastforce

apply clarsimp

apply (frule (3) ptr_offset_in_ptr_range)

apply (frule get_vspace_of_thread_reachable)
apply fastforce
apply clarsimp


apply (clarsimp simp: ptable_rights_def)
apply (rename_tac addr sz attr rights asid asid' vref)
apply (prop_tac "asid' = asid")
apply (drule vs_lookup_table_vspace)
apply assumption
apply clarsimp
apply clarsimp
apply clarsimp

apply (clarsimp simp: get_vspace_of_thread_def split: option.splits kernel_object.splits
cap.splits arch_cap.splits if_splits)

apply (clarsimp simp: get_page_info_def)

apply (clarsimp simp: pt_lookup_slot_def)

apply (frule pt_lookup_slot_from_level_is_subject)
apply fastforce
apply fastforce
apply fastforce
apply assumption
apply (clarsimp simp: pt_lookup_slot_from_level_def)

apply (prop_tac "vs_lookup_table max_pt_level asid x s = Some (max_pt_level, x41)")
apply (clarsimp simp: vs_lookup_table_def)
apply fastforce
apply fastforce
  using canonical_not_kernel_is_user apply blast

apply (rule aag_Control_into_owns)
prefer 2
apply simp

apply (clarsimp simp: pas_refined_def)
apply (erule subsetD)
apply (clarsimp simp: auth_graph_map_def state_objs_to_policy_def)

apply (drule_tac addr="tcb_cnode_index 1" in caps_of_state_tcb)
apply (clarsimp simp: tcb_cnode_map_def)
apply (drule sbta_caps)
apply (fastforce simp: obj_refs_def)
apply (fastforce simp: cap_auth_conferred_def arch_cap_auth_conferred_def)

apply (rule_tac x=tcb in exI, rule conjI)
apply clarsimp
apply (rule exI, rule conjI, rule refl)
apply fastforce

apply (clarsimp simp: pt_lookup_slot_from_level_def)

apply (prop_tac "vs_lookup_table max_pt_level asid x s = Some (max_pt_level, x41)")
apply (clarsimp simp: vs_lookup_table_def)
apply (thin_tac P for P) back
apply (drule pt_walk_level)
apply (drule (1) vs_lookup_table_extend)
apply clarsimp

apply (case_tac "ab = asid_pool_level")
  apply (simp add: pt_walk_top)

apply (prop_tac "is_aligned bb pt_bits")
apply (drule vs_lookup_table_is_aligned)
apply clarsimp
  using canonical_not_kernel_is_user apply blast
apply fastforce
apply fastforce
apply fastforce
  using pt_walk_is_aligned apply blast


apply clarsimp

apply (clarsimp simp: pte_info_def split: pte.splits)

apply (frule vs_lookup_table_pt_at)
apply clarsimp
  using canonical_not_kernel_is_user apply blast
apply fastforce
apply fastforce
apply fastforce
apply (clarsimp simp: obj_at_def)



  apply (prop_tac "state_objs_in_policy aag s")
   apply (clarsimp simp: pas_refined_def)
  apply (erule subsetD)

  apply (clarsimp simp: auth_graph_map_def)
  apply (rule_tac x=bb in exI)
  apply clarsimp
  apply (rule exI, rule conjI, rule refl)

  apply (clarsimp simp: state_objs_to_policy_def)
  apply (rule sbta_vref)
  apply (clarsimp simp: state_vrefs_def)
  apply (rule exI)
  apply (rule conjI)
   apply (rule_tac x=ab in exI)
   apply (clarsimp simp: aobjs_of_Some)
   apply (rule exI)
   apply (rule conjI, rule refl)
   apply (rule exI)+
   apply (rule conjI)
    apply assumption
  using canonical_not_kernel_is_user apply blast
  apply (clarsimp simp: vs_refs_aux_def)


  apply (rule conjI; clarsimp)
   apply (clarsimp simp: graph_of_def pte_ref2_def)
   apply (clarsimp simp: Bex_def)
   apply (clarsimp simp: ptes_of_Some pts_of_Some aobjs_of_Some)
   apply (rule_tac x="table_index (pt_slot_offset max_pt_level bb x)" in exI)
   apply clarsimp
   apply (rule conjI)
    apply (rule table_index_max_level_slots)
  using canonical_not_kernel_is_user apply blast
    apply clarsimp

   apply (prop_tac "x && mask (pt_bits_left max_pt_level) \<le> mask (pt_bits_left max_pt_level)")
  using and_and_not and_mask_0_iff_le_mask apply blast


   apply (subst table_index_offset_max_pt_level)
    apply clarsimp

   apply (clarsimp simp: image_iff)
   apply (fastforce simp: ptrFromPAddr_plus)



   apply (clarsimp simp: graph_of_def pte_ref2_def)
   apply (clarsimp simp: ptes_of_Some pts_of_Some aobjs_of_Some)
   apply (rule_tac x="table_index (pt_slot_offset ab bb x)" in exI)
   apply clarsimp

   apply (clarsimp simp: image_iff)
   apply auto[1]

apply (simp add: ptrFromPAddr_plus)

apply (clarsimp simp: table_index_offset_pt_bits_left)
done

lemma write_in_vspace_cap_rights[ADT_AC_assms]:
  "AllowWrite \<in> ptable_rights (cur_thread s) s va
   \<Longrightarrow> Write \<in> vspace_cap_rights_to_auth (ptable_rights (cur_thread s) s va)"
  by (clarsimp simp: vspace_cap_rights_to_auth_def)

end


global_interpretation ADT_AC_1?: ADT_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact ADT_AC_assms)?)
qed

end
