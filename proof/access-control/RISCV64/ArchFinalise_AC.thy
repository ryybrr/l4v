(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchFinalise_AC
imports Finalise_AC
begin

context Arch begin global_naming ARM_A

named_theorems Finalise_AC_assms

lemma pas_refined_arch_state_update_not_asids[simp]:
 "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s)
  \<Longrightarrow> pas_refined aag (arch_state_update f s) = pas_refined aag s"
  apply (auto simp add: pas_refined_def state_objs_to_policy_def)
apply (erule subsetD)
  oops

crunches set_vm_root for pas_refined[wp]: "pas_refined aag"

(* FIXME ryanb - replace original *)
lemma state_asids_to_policy_vrefs_subseteq:
"x \<in> state_asids_to_policy_aux aag (caps_of_state s) asid_tab X
\<Longrightarrow> \<forall>x. X x \<subseteq> state_vrefs s x
\<Longrightarrow> \<forall>x y. asid_tab x = Some y \<longrightarrow> asid_table s x = Some y
\<Longrightarrow>
 x \<in> state_asids_to_policy_aux aag (caps_of_state s) (asid_table s) (state_vrefs s)"
apply (case_tac x; clarsimp)
apply (erule state_asids_to_policy_aux.cases)
apply (fastforce intro: state_asids_to_policy_aux.intros)+
done


lemma state_vrefs_clear_asid_table:
"state_vrefs
                  (s\<lparr>arch_state := arch_state s
                       \<lparr>riscv_asid_table :=
                          \<lambda>a. if a = asid_high_bits_of base then None
                               else asid_table s a\<rparr>\<rparr>) x \<subseteq> state_vrefs s x"
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
apply (drule vs_lookup_clear_asid_table[simplified fun_upd_def])
apply fastforce
done

lemma delete_asid_pool_pas_refined[wp]:
  "delete_asid_pool base ptr \<lbrace>pas_refined aag\<rbrace>"
unfolding delete_asid_pool_def
apply wpsimp
apply (clarsimp simp: pas_refined_def)
apply (rule conjI)
prefer 2
apply clarsimp
apply (erule subsetD) back
apply (erule state_asids_to_policy_vrefs_subseteq)
apply (rule allI)
apply (rule state_vrefs_clear_asid_table)
apply clarsimp
apply (clarsimp simp: state_objs_to_policy_def)
apply (erule subsetD)
apply (clarsimp simp: auth_graph_map_def)
apply (rule exI, rule conjI, rule refl)+
apply (erule state_bits_to_policy_vrefs_subseteq)
apply (rule allI)
apply (rule state_vrefs_clear_asid_table)
done

lemma thread_states_tcb_states:
  "tcb_states_of_state s' = tcb_states_of_state s \<Longrightarrow>
thread_states s' = thread_states s"
by (clarsimp simp: thread_states_def)

lemma state_vrefs_clear_asid_pool:
  "
asid_tab (asid_high_bits_of asid) = Some x2 \<Longrightarrow>
riscv_asid_table (arch_state s) = asid_tab \<Longrightarrow>
ako_at (ASIDPool pool) x2 s \<Longrightarrow>
state_vrefs
                (s\<lparr>kheap :=
                     \<lambda>a. if a = x2 then Some (ArchObj (ASIDPool (\<lambda>a. if a = asid_low_bits_of asid then None else pool a)))
                          else kheap s a\<rparr>) x
\<subseteq> state_vrefs s x"

apply (clarsimp simp: state_vrefs_def)

apply (case_tac "x = x2")
apply (subst (asm) opt_map_def)
apply clarsimp


apply (rule exI)
apply (rule conjI)
apply (rule_tac x=lvl in exI)
apply (rule_tac x="ASIDPool pool" in exI)
apply (rule conjI)
apply (rule refl)
apply (rule_tac x=lvl in exI)
apply (rule_tac x=asida in exI)
apply (drule vs_lookup_level)
apply (rule_tac x=vref in exI)
apply clarsimp
apply (case_tac "lvl=asid_pool_level")
apply (clarsimp simp: obj_at_def vs_lookup_table_def obind_def aobjs_of_Some)


apply (clarsimp simp: vs_lookup_table_def obind_def
aobjs_of_Some obj_at_def vspace_for_pool_def
 split: option.split_asm if_split_asm)

apply (prop_tac "ptes_of (s\<lparr>kheap :=
              \<lambda>a. if a = x2 then Some (ArchObj (ASIDPool (\<lambda>a. if a = asid_low_bits_of asid then None else pool a)))
                   else kheap s a\<rparr>) = ptes_of s")
apply (rule all_ext)
apply (clarsimp simp: ptes_of_def obind_def opt_map_def)
apply clarsimp
apply (thin_tac "_ = ptes_of _")
apply (clarsimp simp: opt_map_def split: option.split_asm if_split_asm)

apply (fastforce simp: vs_refs_aux_def graph_of_def image_def split: if_splits)

apply (rule exI)
apply (rule conjI)
apply (rule_tac x=lvl in exI)
apply (rule_tac x=ao in exI)
apply (rule conjI)
apply (rule refl)
prefer 2
apply clarsimp
apply (rule_tac x=lvl in exI)
apply (rule_tac x=asida in exI)
apply (drule vs_lookup_level)
apply (rule_tac x=vref in exI)
apply clarsimp

apply (subst (asm) opt_map_def)
apply clarsimp

apply (clarsimp simp: vs_lookup_table_def obind_def
aobjs_of_Some obj_at_def vspace_for_pool_def
 split: option.split_asm if_split_asm)

apply (prop_tac "ptes_of (s\<lparr>kheap :=
              \<lambda>a. if a = x2 then Some (ArchObj (ASIDPool (\<lambda>a. if a = asid_low_bits_of asid then None else pool a)))
                   else kheap s a\<rparr>) = ptes_of s")
apply (rule all_ext)
apply (clarsimp simp: ptes_of_def obind_def opt_map_def)
apply clarsimp
apply (thin_tac "_ = ptes_of _")
apply (clarsimp simp: opt_map_def split: option.split_asm if_split_asm)
done


lemma delete_asid_pas_refined[wp]:
  "delete_asid asid pt \<lbrace>pas_refined aag\<rbrace>"
unfolding delete_asid_def
apply (rule hoare_seq_ext)
apply (wpsimp simp: set_asid_pool_def wp: set_object_wp hoare_vcg_imp_lift' hoare_vcg_all_lift)

apply (rule_tac Q="\<lambda>_ s. ako_at (ASIDPool pool) x2 s
\<and> riscv_asid_table (arch_state s) = asid_table
\<and> pas_refined aag s
" in hoare_strengthen_post[rotated])
defer
apply wpsimp+

apply (clarsimp simp: pas_refined_def)

apply (rule conjI)
apply (clarsimp simp: state_objs_to_policy_def)
apply (subst (asm) caps_of_state_fun_upd[simplified fun_upd_def])
apply (clarsimp simp: obj_at_def)
apply (subst (asm) thread_states_tcb_states[where s'="kheap_update f s" and s=s for f s])
apply (rule all_ext)
apply (clarsimp simp: tcb_states_of_state_def get_tcb_def obj_at_def)

apply (prop_tac "thread_bound_ntfns
                (s\<lparr>kheap :=
                     \<lambda>a. if a = x2 then Some (ArchObj (ASIDPool (\<lambda>a. if a = asid_low_bits_of asid then None else pool a)))
                          else kheap s a\<rparr>) = thread_bound_ntfns s")
apply (rule all_ext)
apply (clarsimp simp: thread_bound_ntfns_def get_tcb_def obj_at_def)
apply clarsimp
apply (thin_tac "thread_bound_ntfns _ = _")

apply (erule subsetD)
apply (clarsimp simp: auth_graph_map_def)
apply (rule exI, rule conjI, rule refl)+
apply (erule state_bits_to_policy_vrefs_subseteq)
apply (rule allI)
apply (rule state_vrefs_clear_asid_pool)
apply assumption
apply clarsimp
apply fastforce

apply (rule conjI)
apply clarsimp
apply (subst (asm) caps_of_state_fun_upd[simplified fun_upd_def])
apply (clarsimp simp: obj_at_def)



apply (erule subsetD) back
apply (erule state_asids_to_policy_vrefs_subseteq)
apply (rule allI)
apply (rule state_vrefs_clear_asid_pool)
apply assumption
apply clarsimp
apply fastforce
apply fastforce
apply clarsimp
apply (subst (asm) caps_of_state_fun_upd[simplified fun_upd_def])
apply (clarsimp simp: obj_at_def)
apply fastforce
done


lemma unmap_page_pas_refined:
   "\<lbrace>pas_refined aag and invs and K (vptr \<in> user_region)\<rbrace>
    unmap_page pgsz asid vptr pptr
    \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding unmap_page_def
  apply (wps | clarsimp simp: conj_ac | wpsimp wp: store_pte_pas_refined set_cap_pas_refined_not_transferable get_cap_wp
  hoare_vcg_all_lift hoare_vcg_imp_lift' store_pte_valid_arch_state_unreachable
  simp: unmap_page_def)+

apply (frule (1) pt_lookup_slot_vs_lookup_slotI0)
apply (drule vs_lookup_slot_level) (* problem? *)
   apply (case_tac "x = asid_pool_level")
    apply (fastforce dest: vs_lookup_slot_no_asid)
apply (subst (asm) vs_lookup_slot_table_unfold)
apply fastforce
apply fastforce
apply fastforce
apply clarsimp
apply (rule conjI)
apply (erule reachable_page_table_not_global)
apply fastforce
apply fastforce
apply fastforce

   apply (rule conjI)
    apply (frule vs_lookup_table_pt_at; clarsimp?)
    apply (drule vs_lookup_table_valid_cap; clarsimp?)
    apply (fastforce simp: valid_cap_def valid_arch_cap_def valid_arch_cap_ref_def obj_at_def
                     dest: caps_of_state_valid split: cap.splits arch_cap.splits)
   apply (clarsimp simp: wellformed_mapdata_def)
   apply (drule (1) vs_lookup_table_vspace)
     apply fastforce
    apply fastforce
   apply clarsimp

   apply (frule user_region_slots)
   apply (clarsimp simp: pt_slot_offset_def)
   apply (metis (full_types, hide_lams) if_Some_None_eq_None invs_implies(7) pspace_aligned_pts_ofD pt_slot_offset_def pt_slot_offset_offset ptes_of_Some)
done


lemma unmap_page_table_pas_refined:
 "\<lbrace>pas_refined aag and invs and K (vaddr \<in> user_region)\<rbrace>
  unmap_page_table asid vaddr pt
  \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding unmap_page_table_def
  apply (rule hoare_gen_asm)
  apply (wpsimp wp: set_cap_pas_refined get_cap_wp)
      apply (wpsimp wp: pt_lookup_from_level_wrp  store_pte_invs_unmap store_pte_pas_refined
                        static_imp_wp hoare_vcg_imp_lift' hoare_vcg_ball_lift hoare_vcg_all_lift)+
  apply (clarsimp simp: conj_ac)
  apply (rule_tac x=asid in exI)
  apply clarsimp

(* same as above basically *)
   apply (case_tac "level = asid_pool_level")
    apply (fastforce dest: vs_lookup_slot_no_asid)
apply (subst (asm) vs_lookup_slot_table_unfold)
apply fastforce
apply fastforce
apply fastforce
apply clarsimp
apply (rule conjI)
apply (erule reachable_page_table_not_global)
apply fastforce
apply fastforce
apply fastforce

   apply (rule conjI)
    apply (frule vs_lookup_table_pt_at; clarsimp?)
    apply (drule vs_lookup_table_valid_cap; clarsimp?)
    apply (fastforce simp: valid_cap_def valid_arch_cap_def valid_arch_cap_ref_def obj_at_def
                     dest: caps_of_state_valid split: cap.splits arch_cap.splits)
   apply (clarsimp simp: wellformed_mapdata_def)
   apply (drule (1) vs_lookup_table_vspace)
     apply fastforce
    apply fastforce
   apply clarsimp

   apply (frule user_region_slots)
   apply (clarsimp simp: pt_slot_offset_def)
   apply (metis (full_types, hide_lams) if_Some_None_eq_None invs_implies(7) pspace_aligned_pts_ofD pt_slot_offset_def pt_slot_offset_offset ptes_of_Some)
done



lemma arch_finalise_cap_pas_refined[wp]:
   "\<lbrace>pas_refined aag and invs and valid_arch_cap c\<rbrace> arch_finalise_cap c x \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
unfolding arch_finalise_cap_def
apply (wpsimp wp: unmap_page_pas_refined unmap_page_table_pas_refined)
apply (auto simp: valid_arch_cap_def wellformed_mapdata_def)
done

crunch pas_refined[wp]: prepare_thread_delete "pas_refined aag"

crunch respects[Finalise_AC_assms, wp]: prepare_thread_delete "integrity aag X st"

lemma sbn_st_vrefs[Finalise_AC_assms, wp]:
  "\<lbrace>(\<lambda>s. P (state_vrefs s)) and pspace_aligned and valid_vspace_objs and valid_arch_state\<rbrace>
    set_bound_notification t st \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wpsimp wp: set_object_wp dxo_wp_weak)
  apply (subst state_vrefs_tcb_upd)
      apply (auto simp: tcb_at_def)
  done

lemma arch_finalise_cap_auth'[Finalise_AC_assms]:
   "\<lbrace>pas_refined aag\<rbrace> arch_finalise_cap x12 final \<lbrace>\<lambda>rv s. pas_cap_cur_auth aag (fst rv)\<rbrace>"
  unfolding arch_finalise_cap_def
  by (wp | wpc | simp add: comp_def hoare_post_taut[where P = \<top>] split del: if_split)+

lemma arch_finalise_cap_obj_refs[Finalise_AC_assms]:
  "\<lbrace>\<lambda>s. \<forall>x \<in> aobj_ref' acap. P x\<rbrace>
   arch_finalise_cap acap slot
   \<lbrace>\<lambda>rv s. \<forall>x \<in> obj_refs (fst rv). P x\<rbrace>"
  by (wpsimp simp: arch_finalise_cap_def)

lemma arch_finalise_cap_makes_halted[Finalise_AC_assms]:
  "\<lbrace>\<top>\<rbrace> arch_finalise_cap arch_cap ex \<lbrace>\<lambda>rv s. \<forall>t\<in>Access.obj_refs (fst rv). halted_if_tcb t s\<rbrace>"
  apply (case_tac arch_cap, simp_all add: arch_finalise_cap_def)
  by (wpsimp simp: valid_cap_def split: option.split bool.split)+

lemma arch_cap_cleanup_wf[Finalise_AC_assms]:
  "\<lbrakk> arch_cap_cleanup_opt acap \<noteq> NullCap; \<not> is_arch_cap (arch_cap_cleanup_opt acap) \<rbrakk>
     \<Longrightarrow> (\<exists>irq. arch_cap_cleanup_opt acap = IRQHandlerCap irq \<and> is_subject_irq aag irq)"
  by simp

lemma set_vm_root_integrity[wp]:
  "set_vm_root param_a \<lbrace>integrity aag X st\<rbrace> "
unfolding set_vm_root_def
by (wpsimp wp: dmo_wp mol_respects get_cap_wp simp: setVSpaceRoot_def)


lemma delete_asid_pool_respects[wp]:
  "\<lbrace>integrity aag X st and
    K (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of x
               \<longrightarrow> is_subject_asid aag asid')\<rbrace>
   delete_asid_pool x y
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding delete_asid_pool_def
  apply simp
  apply (wp mapM_wp[OF _ subset_refl] | simp)+
  done

lemma set_asid_pool_respects_clear:
  "\<lbrace>integrity aag X st and (\<lambda>s. \<forall>pool'. ko_at (ArchObj (arch_kernel_obj.ASIDPool pool')) ptr s
                                        \<longrightarrow> asid_pool_integrity {pasSubject aag} aag pool' pool)\<rbrace>
   set_asid_pool ptr pool
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: set_object_wp_strong
              simp: obj_at_def a_type_def
             split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm if_splits)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def)
  apply (rule tro_arch; fastforce simp: arch_integrity_obj_atomic.simps)
  done

lemma delete_asid_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs and K (is_subject aag pd)\<rbrace>
   delete_asid asid pd
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (wpsimp wp: set_asid_pool_respects_clear hoare_vcg_all_lift dmo_wp mol_respects
           simp: obj_at_def pas_refined_refl delete_asid_def asid_pool_integrity_def hwASIDFlush_def)

lemma arch_finalise_cap_respects[wp]:
  "\<lbrace>integrity aag X st and invs and pas_refined aag and valid_cap (ArchObjectCap cap)
                       and K (pas_cap_cur_auth aag (ArchObjectCap cap))\<rbrace>
   arch_finalise_cap cap final
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: arch_finalise_cap_def)
  apply (wpsimp wp: unmap_page_respects unmap_page_table_respects delete_asid_respects)
  apply (auto simp: cap_auth_conferred_def arch_cap_auth_conferred_def wellformed_mapdata_def
                    aag_cap_auth_def pas_refined_all_auth_is_owns valid_cap_simps
                    cap_links_asid_slot_def label_owns_asid_slot_def
             intro: pas_refined_Control_into_is_subject_asid)
  done

end


global_interpretation Finalise_AC_1?: Finalise_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Finalise_AC_assms | wp finalise_cap_replaceable))
qed


context Arch begin global_naming ARM_A

lemma cap_revoke_respects'[Finalise_AC_assms]:
  "s \<turnstile> \<lbrace>(\<lambda>s. trp \<longrightarrow> integrity aag X st s) and K (is_subject aag (fst slot))
                                           and pas_refined aag and einvs and simple_sched_action\<rbrace>
       cap_revoke slot
       \<lbrace>\<lambda>_. (\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag\<rbrace>,
       \<lbrace>\<lambda>_. (\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag\<rbrace>"
proof (induct rule: cap_revoke.induct[where ?a1.0=s])
  case (1 slot s)
  show ?case
    apply (subst cap_revoke.simps)
    apply (rule hoare_pre_spec_validE)
     apply (wp "1.hyps")
            apply ((wp preemption_point_inv' | simp add: integrity_subjects_def pas_refined_def)+)[1]
           apply (wp select_ext_weak_wp cap_delete_respects cap_delete_pas_refined
                  | simp split del: if_split | wp (once) hoare_vcg_const_imp_lift hoare_drop_imps)+
    by (auto simp: emptyable_def descendants_of_def
             dest: reply_slot_not_descendant
            intro: cca_owned)
qed

lemma finalise_cap_caps_of_state_nullinv[Finalise_AC_assms]:
  "\<lbrace>\<lambda>s. P (caps_of_state s) \<and> (\<forall>p. P (caps_of_state s(p \<mapsto> NullCap)))\<rbrace>
   finalise_cap cap final
   \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  by (cases cap;
      wpsimp wp: suspend_caps_of_state unbind_notification_caps_of_state
                 unbind_notification_cte_wp_at
                 hoare_vcg_all_lift hoare_drop_imps
                 deleting_irq_handler_caps_of_state_nullinv
           simp: fun_upd_def[symmetric] if_apply_def2 split_del: if_split)

lemma finalise_cap_fst_ret[Finalise_AC_assms]:
  "\<lbrace>\<lambda>_. P NullCap \<and> (\<forall>a b c. P (Zombie a b c))\<rbrace>
   finalise_cap cap is_final
   \<lbrace>\<lambda>rv _. P (fst rv)\<rbrace>"
  including no_pre
  apply (cases cap, simp_all add: arch_finalise_cap_def split del: if_split)
  apply (wp | simp add: comp_def split del: if_split | fastforce)+
  apply (rule hoare_pre)
  apply (wp | simp | (rule hoare_pre, wpc))+
  done

end


global_interpretation Finalise_AC_2?: Finalise_AC_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact Finalise_AC_assms)
qed

end