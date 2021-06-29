(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchCNode_AC
imports CNode_AC
begin

section\<open>Arch-specific CNode AC.\<close>

context Arch begin global_naming RISCV64

declare arch_post_modify_registers_def[simp]
declare arch_post_cap_deletion_def[simp]
declare arch_cap_cleanup_opt_def[simp]
declare arch_mask_irq_signal_def[simp]

named_theorems CNode_AC_assms

lemma sata_cdt_update[CNode_AC_assms, simp]:
  "state_asids_to_policy aag (cdt_update f s) = state_asids_to_policy aag s"
  by simp

lemma sata_is_original_cap_update[CNode_AC_assms, simp]:
  "state_asids_to_policy aag (is_original_cap_update f s) = state_asids_to_policy aag s"
  by simp

lemma sata_interrupt_states_update[CNode_AC_assms, simp]:
  "state_asids_to_policy aag (interrupt_states_update f s) = state_asids_to_policy aag s"
  by simp

lemma sata_machine_state_update[CNode_AC_assms, simp]:
  "state_asids_to_policy aag (machine_state_update f s) = state_asids_to_policy aag s"
  by simp

lemma sata_update[CNode_AC_assms]:
  "\<lbrakk> pas_wellformed aag;
     cap_links_asid_slot aag (pasObjectAbs aag (fst ptr)) cap;
     state_asids_to_policy_arch aag caps as vrefs \<subseteq> pasPolicy aag \<rbrakk>
     \<Longrightarrow> state_asids_to_policy_arch aag (caps(ptr \<mapsto> cap)) as vrefs \<subseteq> pasPolicy aag"
  by (fastforce intro: state_asids_to_policy_aux.intros
                 elim!: state_asids_to_policy_aux.cases
                 simp: cap_links_asid_slot_def label_owns_asid_slot_def
                split: if_split_asm)

lemma sata_update2[CNode_AC_assms]:
  "\<lbrakk> pas_wellformed aag;
     cap_links_asid_slot aag (pasObjectAbs aag (fst ptr)) cap;
     cap_links_asid_slot aag (pasObjectAbs aag (fst ptr')) cap';
     state_asids_to_policy_arch aag caps as vrefs \<subseteq> pasPolicy aag \<rbrakk>
     \<Longrightarrow> state_asids_to_policy_arch aag (caps(ptr \<mapsto> cap, ptr' \<mapsto> cap')) as vrefs \<subseteq> pasPolicy aag"
  by (fastforce intro: state_asids_to_policy_aux.intros
                elim!: state_asids_to_policy_aux.cases
                 simp: cap_links_asid_slot_def label_owns_asid_slot_def
                split: if_split_asm)

(* FIXME ryanb *)
lemma state_vrefs_eqI:
  "\<lbrakk> \<forall>bot_level asid vref level p.
     bot_level < level \<longrightarrow>
     vs_lookup_table level asid vref s = Some (level, p) \<longrightarrow>
     (if level \<le> max_pt_level then pts_of s' p = pts_of s p else asid_pools_of s' p = asid_pools_of s p);
     aobjs_of s' = aobjs_of s; asid_table s'  = asid_table s; pspace_aligned s; valid_vspace_objs s; valid_asid_table s\<rbrakk>
     \<Longrightarrow> state_vrefs (s' :: 'a :: state_ext state) = state_vrefs (s :: 'a :: state_ext state)"
  apply (rule ext)
  apply (simp (no_asm) add: state_vrefs_def)
  apply auto
   apply (rule exI, rule conjI[rotated], assumption)
   apply (rule exI, rule exI, rule conjI, rule refl)
   apply (rule_tac x=bot in exI)
   apply (rule_tac x=asid in exI)
   apply (rule_tac x=vref in exI)
   apply clarsimp
   apply (rule subst[OF vs_lookup_table_eqI,rotated -1])
        apply assumption
       apply fastforce
      apply simp+
  apply (rule exI, rule conjI[rotated], assumption)
  apply (rule exI, rule exI, rule conjI, rule refl)
  apply (rule_tac x=bot in exI)
  apply (rule_tac x=asid in exI)
  apply (rule_tac x=vref in exI)
  apply clarsimp
  apply (subst vs_lookup_table_eqI)
       prefer 6
       apply assumption
      apply fastforce
     apply simp+
  done

lemma set_cap_state_vrefs[CNode_AC_assms, wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and (\<lambda>s. P (state_vrefs s))\<rbrace>
   set_cap cap slot
   \<lbrace>\<lambda>_ s :: det_ext state. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_cap_def set_object_def)
  apply (wpsimp wp: get_object_wp)
  apply safe
        apply (all \<open>subst state_vrefs_eqI\<close>)
  by (fastforce simp: valid_arch_state_def obj_at_def opt_map_def
               split: option.splits kernel_object.splits)+

crunches maskInterrupt
  for underlying_memory[CNode_AC_assms, wp]: "\<lambda>s. P (underlying_memory s)"
  and device_state[CNode_AC_assms, wp]: "\<lambda>s. P (device_state s)"
  (simp: maskInterrupt_def)

crunches set_cdt
  for state_vrefs[CNode_AC_assms, wp]: "\<lambda>s. P (state_vrefs s)"
  and state_asids_to_policy[CNode_AC_assms, wp]: "\<lambda>s. P (state_asids_to_policy aag s)"

crunches prepare_thread_delete, arch_finalise_cap
  for cur_domain[CNode_AC_assms, wp]:"\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps select_wp hoare_vcg_if_lift2 simp: unless_def)

(* FIXME ryanb *)
lemma state_vrefs_tcb_upd[CNode_AC_assms]:
  "\<lbrakk> pspace_aligned s; valid_vspace_objs s; valid_arch_state s; tcb_at t s \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>kheap := kheap s(t \<mapsto> TCB tcb)\<rparr>) = state_vrefs s"
  apply (rule state_vrefs_eqI)
  by (fastforce simp: opt_map_def obj_at_def is_obj_defs valid_arch_state_def)+

(* FIXME ryanb *)
lemma state_vrefs_simple_type_upd[CNode_AC_assms]:
  "\<lbrakk> pspace_aligned s; valid_vspace_objs s; valid_arch_state s;
     ko_at ko ptr s; is_simple_type ko; a_type ko = a_type (f val) \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>kheap := kheap s(ptr \<mapsto> f val)\<rparr>) = state_vrefs s"
  apply (case_tac ko; case_tac "f val"; clarsimp)
  by (fastforce intro!: state_vrefs_eqI simp: opt_map_def obj_at_def is_obj_defs valid_arch_state_def)+

lemma a_type_arch_object_not_tcb[CNode_AC_assms, simp]:
  "a_type (ArchObj arch_kernel_obj) \<noteq> ATCB"
  by auto

lemma arch_post_cap_deletion_cur_domain[CNode_AC_assms, wp]:
  "arch_post_cap_deletion acap \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
  by wpsimp

lemma arch_post_cap_deletion_integrity[CNode_AC_assms]:
  "arch_post_cap_deletion acap \<lbrace>integrity aag X st\<rbrace>"
  by wpsimp

end


context is_extended begin interpretation Arch .

lemma list_integ_lift[CNode_AC_assms]:
  assumes li:
    "\<lbrace>list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st and Q\<rbrace>
     f
     \<lbrace>\<lambda>_. list_integ (cdt_change_allowed aag {pasSubject aag}  (cdt st) (tcb_states_of_state st)) st\<rbrace>"
  assumes ekh: "\<And>P. f \<lbrace>\<lambda>s. P (ekheap s)\<rbrace>"
  assumes rq: "\<And>P. f \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace>"
  shows "\<lbrace>integrity aag X st and Q\<rbrace> f \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_pre)
   apply (unfold integrity_def[abs_def] integrity_asids_def)
   apply (simp only: integrity_cdt_list_as_list_integ)
   apply (rule hoare_lift_Pf2[where f="ekheap"])
    apply (simp add: tcb_states_of_state_def get_tcb_def)
    apply (wp li[simplified tcb_states_of_state_def get_tcb_def] ekh rq)+
  apply (simp only: integrity_cdt_list_as_list_integ)
  apply (simp add: tcb_states_of_state_def get_tcb_def)
  done

end


global_interpretation CNode_AC_1?: CNode_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact CNode_AC_assms)
qed


context Arch begin global_naming RISCV64

lemma integrity_asids_set_cap_Nullcap[CNode_AC_assms]:
  "\<lbrace>(=) s\<rbrace> set_cap NullCap slot \<lbrace>\<lambda>_. integrity_asids aag subjects x s\<rbrace>"
  unfolding integrity_asids_def by wpsimp

crunches set_original
  for state_asids_to_policy[CNode_AC_assms, wp]: "\<lambda>s. P (state_asids_to_policy aag s)"
  and state_objs_to_policy[CNode_AC_assms, wp]: "\<lambda>s. P (state_objs_to_policy s)"
  (simp: state_objs_to_policy_def)

crunches set_cdt_list, update_cdt_list
  for state_vrefs[CNode_AC_assms, wp]: "\<lambda>s. P (state_vrefs s)"
  and state_asids_to_policy[CNode_AC_assms, wp]: "\<lambda>s. P (state_asids_to_policy aag s)"
  (simp: set_cdt_list_def)

end


global_interpretation CNode_AC_2?: CNode_AC_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact CNode_AC_assms)
qed


context Arch begin global_naming RISCV64

lemma arch_post_cap_deletion_pas_refined[CNode_AC_assms, wp]:
  "arch_post_cap_deletion irqopt \<lbrace>pas_refined aag\<rbrace>"
  by (wpsimp simp: post_cap_deletion_def)

lemma aobj_ref'_same_aobject[CNode_AC_assms]:
  "same_aobject_as ao' ao \<Longrightarrow> aobj_ref' ao = aobj_ref' ao'"
  by (cases ao; clarsimp split: arch_cap.splits)

end


context is_extended begin interpretation Arch .

lemma pas_refined_tcb_domain_map_wellformed[CNode_AC_assms, wp]:
  assumes tdmw: "f \<lbrace>tcb_domain_map_wellformed aag\<rbrace>"
  shows "f \<lbrace>pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def)
  apply (wp tdmw)
   apply (wp lift_inv)
   apply simp+
  done

end


global_interpretation CNode_AC_3?: CNode_AC_3
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact CNode_AC_assms)
qed


context Arch begin global_naming RISCV64

lemma arch_derive_cap_auth_derived[CNode_AC_assms]:
  "\<lbrace>\<lambda>s. cte_wp_at (auth_derived (ArchObjectCap cap)) src_slot s\<rbrace>
   arch_derive_cap cap
   \<lbrace>\<lambda>rv s. cte_wp_at (auth_derived rv) src_slot s\<rbrace>, -"
  apply (rule hoare_pre)
   apply (wp | wpc | simp add: arch_derive_cap_def)+
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (safe)
  apply (clarsimp simp: auth_derived_def arch_cap_auth_conferred_def cap_auth_conferred_def)
  done

lemma cap_asid'_cap_rights_update[CNode_AC_assms, simp]:
  "acap_asid' (acap_rights_update rights ao) = acap_asid' ao"
  by (cases ao; clarsimp simp: cap_rights_update_def acap_rights_update_def)

lemma untyped_range_cap_rights_update[CNode_AC_assms, simp]:
  "untyped_range (cap_rights_update rights (ArchObjectCap ao)) = untyped_range (ArchObjectCap ao)"
  by (cases ao; clarsimp simp: cap_rights_update_def)

lemma obj_refs_cap_rights_update[CNode_AC_assms, simp]:
  "aobj_ref' (acap_rights_update rights ao) = aobj_ref' ao"
  by (cases ao; clarsimp simp: cap_rights_update_def acap_rights_update_def)

lemma auth_derived_arch_update_cap_data[CNode_AC_assms]:
  "auth_derived (ArchObjectCap ao) cap' \<Longrightarrow> auth_derived (arch_update_cap_data pres w ao) cap'"
  by (simp add: update_cap_data_def is_cap_simps arch_update_cap_data_def
                  split del: if_split cong: if_cong)

lemma acap_auth_conferred_acap_rights_update[CNode_AC_assms]:
  "arch_cap_auth_conferred (acap_rights_update (acap_rights acap \<inter> R) acap)
   \<subseteq> arch_cap_auth_conferred acap"
  by (auto simp: arch_cap_auth_conferred_def vspace_cap_rights_to_auth_def acap_rights_update_def
                 validate_vm_rights_def vm_kernel_only_def vm_read_only_def
          split: arch_cap.splits)

lemma arch_derive_cap_clas[CNode_AC_assms]:
  "\<lbrace>\<lambda>s. cap_links_asid_slot aag p (ArchObjectCap acap)\<rbrace>
   arch_derive_cap acap
   \<lbrace>\<lambda>rv s. cap_links_asid_slot aag p rv\<rbrace>, -"
  apply (simp add: arch_derive_cap_def cong: cap.case_cong)
  apply (rule hoare_pre)
  apply (wp | wpc)+
  apply (auto simp: is_cap_simps cap_links_asid_slot_def)
  done

lemma arch_derive_cap_obj_refs_auth[CNode_AC_assms]:
  "\<lbrace>K (\<forall>r\<in>obj_refs (ArchObjectCap cap).
       \<forall>auth\<in>cap_auth_conferred (ArchObjectCap cap). aag_has_auth_to aag auth r)\<rbrace>
   arch_derive_cap cap
   \<lbrace>(\<lambda>x s. \<forall>r\<in>obj_refs x. \<forall>auth\<in>cap_auth_conferred x. aag_has_auth_to aag auth r)\<rbrace>, -"
  unfolding arch_derive_cap_def
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def)
  done

(* FIXME: move *)
lemma arch_derive_cap_obj_refs_subset[CNode_AC_assms]:
  "\<lbrace>\<lambda>s. (\<forall>x \<in> aobj_ref' acap. P x s)\<rbrace> arch_derive_cap acap \<lbrace>\<lambda>rv s. \<forall>x \<in> obj_refs rv. P x s\<rbrace>, -"
  by (wpsimp simp: arch_derive_cap_def) fastforce

lemma arch_derive_cap_clip[CNode_AC_assms]:
  "\<lbrace>K (cap_links_irq aag l (ArchObjectCap ac))\<rbrace>
   arch_derive_cap ac
   \<lbrace>\<lambda>x s. cap_links_irq aag l x\<rbrace>, -"
  by (wpsimp simp: arch_derive_cap_def comp_def cli_no_irqs)

(* FIXME: move *)
lemma arch_derive_cap_untyped_range_subset[CNode_AC_assms]:
  "\<lbrace>\<lambda>s. \<forall>x \<in> untyped_range (ArchObjectCap acap). P x s\<rbrace>
   arch_derive_cap acap
   \<lbrace>\<lambda>rv s. \<forall>x \<in> untyped_range rv. P x s\<rbrace>, -"
  by (wpsimp simp: arch_derive_cap_def)

lemma arch_update_cap_obj_refs_subset[CNode_AC_assms]:
  "\<lbrakk> x \<in> obj_refs (arch_update_cap_data pres data cap) \<rbrakk> \<Longrightarrow> x \<in> aobj_ref' cap"
  by (simp add: arch_update_cap_data_def)

lemma arch_update_cap_untyped_range_empty[CNode_AC_assms, simp]:
  "untyped_range (arch_update_cap_data pres data cap) = {}"
  by (simp add: arch_update_cap_data_def)

lemma arch_update_cap_irqs_controlled_empty[CNode_AC_assms, simp]:
  "cap_irqs_controlled (arch_update_cap_data pres data cap) = {}"
  by (simp add: arch_update_cap_data_def)

lemma arch_update_cap_links_asid_slot[CNode_AC_assms]:
  "cap_links_asid_slot aag p (arch_update_cap_data pres w acap) =
   cap_links_asid_slot aag p (ArchObjectCap acap)"
  by (simp add: arch_update_cap_data_def)

lemma arch_update_cap_cap_auth_conferred_subset[CNode_AC_assms]:
  "y \<in> cap_auth_conferred (arch_update_cap_data b w acap) \<Longrightarrow> y \<in> arch_cap_auth_conferred acap"
  by (simp add: arch_update_cap_data_def cap_auth_conferred_def)

end


global_interpretation CNode_AC_4?: CNode_AC_4
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact CNode_AC_assms)?)
qed


context Arch begin global_naming RISCV64

lemma pas_refined_arch_state_update_not_asids[simp]:
 "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s)
  \<Longrightarrow> pas_refined aag (arch_state_update f s) = pas_refined aag s"
  apply (auto simp add: pas_refined_def state_objs_to_policy_def)
apply (erule subsetD)
  oops

crunch cdt[wp]: store_pte "\<lambda>s. P (cdt s)"

lemma store_pte_state_refs[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def state_refs_of_def
                 elim!: rsubst[where P=P, OF _ ext])
  done

(* FIXME ryanb - remove? *)
lemma all_rsubst:
  "\<lbrakk> \<forall>v. P (f v); \<exists>v. f v = r \<rbrakk> \<Longrightarrow> P r"
  by clarsimp



lemma "\<lbrace>valid_pti pti\<rbrace> perform_page_table_invocation pti \<lbrace>Q\<rbrace>"
apply (unfold perform_page_table_invocation_def perform_pt_inv_map_def perform_pt_inv_unmap_def)
apply (case_tac pti; clarsimp simp: valid_pti_def)
apply (rename_tac acap cslot_a cslot_b pte pt_slot)
thm valid_vspace_objs_def
term wellformed_pte
term perform_page_table_invocation
term perform_pt_inv_map
term valid_pti
term invalid_pte_at
oops

lemma "\<lbrace>valid_pti pti\<rbrace> perform_page_table_invocation pti \<lbrace>Q\<rbrace>"
apply (unfold perform_page_table_invocation_def perform_pt_inv_map_def perform_pt_inv_unmap_def)
apply (case_tac pti; clarsimp simp: valid_pti_def)
subgoal sorry
apply (rename_tac acap cslot_a cslot_b)
thm valid_vspace_objs_def
term wellformed_pte
term perform_page_table_invocation
term perform_pt_inv_map
term valid_pti
term invalid_pte_at
oops



lemma vs_lookup_PageTablePTE:
  "\<lbrakk> pspace_aligned s; valid_vspace_objs s; valid_asid_table s;
     invalid_pte_at p s; ptes_of s' = ptes_of s (p \<mapsto> pte); is_PageTablePTE pte;
     asid_pools_of s' = asid_pools_of s; asid_table s' = asid_table s;
     vref \<in> user_region; vs_lookup_table level asid vref s' = Some (lvl', pt);
     pts_of s (the (pte_ref pte)) = Some empty_pt; pt \<noteq> pptr_from_pte pte \<rbrakk>
     \<Longrightarrow> \<exists>level' \<ge> level. vs_lookup_table level' asid vref s = Some (lvl', pt)"
  apply (induct level arbitrary: lvl' pt rule: bit0.from_top_full_induct[where y=max_pt_level])
   apply (fastforce simp: geq_max_pt_level vs_lookup_table_def pool_for_asid_def obind_def)
  apply (rule_tac x=lvl' in exI)
  apply (rule context_conjI)
   apply (fastforce dest: vs_lookup_min_level)
  apply (drule vs_lookup_level)
  apply (case_tac "lvl' < max_pt_level")
   apply (frule vs_lookup_table_split_last_Some; clarsimp)
   apply (erule_tac x="lvl'+1" in allE)
   apply (drule mp)
    apply (fastforce elim: le_less_trans dest: vm_level_less_plus_1_mono)
   apply (erule_tac x="lvl'+1" in allE)
   apply clarsimp
   apply (frule subst[where s="ptes_of s'" and P="\<lambda>ptes. ptes _ = _"])
    apply assumption
   apply (drule mp, fastforce simp: pte_ref_def2 ptes_of_Some split: if_splits)
   apply (cases pte; clarsimp)
   apply (drule_tac bot_level=level' in vs_lookup_level)
   apply (subst vs_lookup_split_Some)
     prefer 3
     apply (rule exI, rule conjI, assumption)
     apply (frule_tac P="\<lambda>x. x" and level1=lvl' and level'1="lvl'+1"
                   in subst[OF vs_lookup_split_Some, rotated 2])
       apply (fastforce dest: vm_level_less_le_1)
      apply (fastforce dest: vm_level_less_max_pt_level vm_level_less_plus_1_mono)
     apply clarsimp
     apply (subst (asm) pt_walk.simps)
     apply (clarsimp simp: obind_def)
     apply (subst pt_walk.simps)
     apply (clarsimp split: if_splits simp: obind_def)
    apply (fastforce dest: vm_level_less_le_1)
   apply (fastforce dest: vm_level_less_max_pt_level vm_level_less_plus_1_mono)
  apply (case_tac "lvl' = asid_pool_level")
   apply (auto simp: geq_max_pt_level vs_lookup_table_def pool_for_asid_def obind_def)
  done

lemma vs_lookup_PageTablePTE':
  "\<lbrakk> pspace_aligned s; valid_vspace_objs s; valid_asid_table s;
     invalid_pte_at p s; ptes_of s' = ptes_of s (p \<mapsto> pte); is_PageTablePTE pte;
     asid_pools_of s' = asid_pools_of s; asid_table s' = asid_table s;
     vref \<in> user_region; vs_lookup_table level asid vref s = Some (lvl', pt) \<rbrakk>
     \<Longrightarrow> \<exists>level' \<ge> level. vs_lookup_table level' asid vref s' = Some (lvl', pt)"
  apply (induct level arbitrary: lvl' pt rule: bit0.from_top_full_induct[where y=max_pt_level])
   apply (fastforce simp: geq_max_pt_level vs_lookup_table_def pool_for_asid_def obind_def)
  apply (rule_tac x=lvl' in exI)
  apply (rule context_conjI)
   apply (fastforce dest: vs_lookup_min_level)
  apply (drule vs_lookup_level)
  apply (case_tac "lvl' < max_pt_level")
   apply (frule vs_lookup_table_split_last_Some; clarsimp)
   apply (erule_tac x="lvl'+1" in allE)
   apply (drule mp)
    apply (fastforce elim: le_less_trans dest: vm_level_less_plus_1_mono)
   apply (erule_tac x="lvl'+1" in allE)
   apply clarsimp
   apply (drule_tac bot_level=level' in vs_lookup_level)
   apply (subst vs_lookup_split_Some)
     prefer 3
     apply (rule exI, rule conjI, assumption)
     apply (frule_tac P="\<lambda>x. x" and level1=lvl' and level'1="lvl'+1"
                   in subst[OF vs_lookup_split_Some, rotated 2])
       apply (fastforce dest: vm_level_less_le_1)
      apply (fastforce dest: vm_level_less_max_pt_level vm_level_less_plus_1_mono)
     apply clarsimp
     apply (subst (asm) pt_walk.simps)
     apply (clarsimp simp: obind_def split: if_splits)
     apply (subst pt_walk.simps)
     apply (clarsimp simp: obind_def split: if_splits)
     apply (cases pte; clarsimp)
     apply (frule is_aligned_pt[rotated])
      apply (erule vs_lookup_table_pt_at; fastforce)
     apply (clarsimp simp: invalid_pte_at_def ptes_of_Some pts_of_Some aobjs_of_Some)
    apply (fastforce dest: vm_level_less_le_1)
   apply (fastforce dest: vm_level_less_max_pt_level vm_level_less_plus_1_mono)
  apply (case_tac "lvl' = asid_pool_level")
   apply (auto simp: geq_max_pt_level vs_lookup_table_def pool_for_asid_def obind_def)
  done


lemma vs_lookup_slot_table_base':
  "\<lbrakk> vs_lookup_slot level asid vref s = Some (level, slot); vref \<in> user_region;
     level \<le> max_pt_level; invs s \<rbrakk> \<Longrightarrow>
   slot = pt_slot_offset level (table_base slot) vref"
  apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
  apply (drule vs_lookup_table_is_aligned; clarsimp)
  done


lemma level_of_slot_vs_lookup_slot:
  "\<lbrakk> vs_lookup_slot level asid vref s = Some (level, p);
     ptes_of s p = Some pte; level \<le> max_pt_level; vref \<in> user_region; invs s \<rbrakk>
     \<Longrightarrow> level_of_slot asid vref p s = level"
apply (subst level_of_slot_def)
apply (rule Greatest_equality)
apply clarsimp
thm vs_lookup_slot_no_asid vs_lookup_slot_unique_level
    apply (case_tac "y = asid_pool_level")
apply clarsimp
apply (drule vs_lookup_slot_no_asid)
apply simp
apply clarsimp+

apply (drule (1) vs_lookup_slot_unique_level)
apply fastforce+
done


lemma state_vrefs_store_NonPageTablePTE:
  "\<lbrakk> invs s; is_aligned p pte_bits; vs_lookup_slot level asid vref s = Some (level, p);
     vref \<in> user_region; \<not> is_PageTablePTE pte;
     kheap s (table_base p) = Some (ArchObj (PageTable pt)) \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>kheap := \<lambda>a. if a = table_base p
                                     then Some (ArchObj (PageTable (\<lambda>a. if a = table_index p then pte else pt a)))
                                     else kheap s a\<rparr>) =
         (\<lambda>x. if \<exists>level' vref'. vref' \<in> user_region \<and> vref_for_level vref' (level + 1) = vref_for_level vref (level + 1) \<and>
                                p = pt_slot_offset level (table_base p) vref' \<and>
                                pt_walk level level' (table_base p) vref' (ptes_of s) = Some (level',x)
              then (if x = table_base p
                    then vs_refs_aux level (PageTable (\<lambda>a. if a = table_index p then pte else pt a))
                    else {})
              else state_vrefs s x)"
  apply (rule all_ext)

  apply (case_tac "level = asid_pool_level")
   apply (clarsimp simp: vs_lookup_slot_def split: if_splits)
   apply (clarsimp simp: vs_lookup_table_def split: if_splits)
   apply (drule pool_for_asid_no_pte)
      apply (simp add: ptes_of_Some pts_of_Some aobjs_of_Some)
     apply fastforce
    apply fastforce
   apply fastforce

apply (prop_tac "ptes_of s p \<noteq> None")
apply (drule valid_vspace_objs_strong_slotD)
apply fastforce+

  apply (frule vs_lookup_slot_table_base')
     apply fastforce+
  apply (drule vs_lookup_slot_table_base)
     apply fastforce+

  apply safe


(* first thing *)
   apply (subst (asm) state_vrefs_def opt_map_def)+
   apply (clarsimp split: option.splits split del: if_split)
   apply (clarsimp split: if_split_asm option.splits split del: if_split)
(* x = table_base p *)
    apply (subst (asm) vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte])
           apply (clarsimp simp: ptes_of_Some pts_of_Some aobjs_of_Some)
          apply (rule all_ext)
          apply (clarsimp simp: opt_map_def pte_of_def obind_def)
          apply (fastforce dest: pte_ptr_eq)
         apply simp
        apply (fastforce simp: opt_map_def)
       apply (fastforce simp: opt_map_def)
      apply fastforce+
    (* done *)

    apply (clarsimp split: if_splits)


     apply (rule conjI)
      prefer 2
      apply clarsimp
      apply (erule_tac x=level in allE)
      apply (erule_tac x=vref in allE)
      apply clarsimp

     apply (drule vs_lookup_level) back

     apply (case_tac "lvl = asid_pool_level")
      apply clarsimp
      apply (frule vs_lookup_table_no_asid)
         apply (fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some)
        apply fastforce
       apply fastforce
      apply fastforce

     apply clarsimp
     apply (drule (1) vs_lookup_table_unique_level)
           apply fastforce+

    apply (rule conjI)
     prefer 2
     apply clarsimp
     apply (erule_tac x=level in allE) back
     apply clarsimp

     apply (drule vs_lookup_level) back

     apply (case_tac "lvl = asid_pool_level")
      apply clarsimp
      apply (frule vs_lookup_table_no_asid)
         apply (fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some)
        apply fastforce
       apply fastforce
      apply fastforce

     apply clarsimp
     apply (drule (1) vs_lookup_table_unique_level)
           apply fastforce+
(* x \<noteq> table_base p *)


   apply (subst (asm) vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte])
          apply (clarsimp simp: ptes_of_Some pts_of_Some aobjs_of_Some)
         apply (rule all_ext)
         apply (clarsimp simp: opt_map_def pte_of_def obind_def)
         apply (fastforce dest: pte_ptr_eq)
        apply simp
       apply (fastforce simp: opt_map_def)
      apply (fastforce simp: opt_map_def)
     apply fastforce+
    (* done *)

   apply (subst state_vrefs_def)
   apply (clarsimp split: if_splits)

  apply (case_tac "level' = asid_pool_level")
      apply clarsimp
      apply (frule vs_lookup_slot_no_asid)
         apply (fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some)
        apply fastforce
       apply fastforce
      apply fastforce
    apply clarsimp

    apply (prop_tac "level_of_slot asida vrefa p s = level'")
apply (erule level_of_slot_vs_lookup_slot)
apply (fastforce simp: ptes_of_Some pte_of_def obind_def pts_of_Some aobjs_of_Some split: option.splits)
apply fastforce+

    apply (subst (asm) vs_lookup_slot_table_unfold; fastforce)

   apply (rule conjI)
    prefer 2
    apply (fastforce simp: opt_map_def)
   apply clarsimp


   apply (case_tac "level' < level")
    prefer 2
    apply (subst (asm) pt_walk.simps)
    apply clarsimp


apply (prop_tac "vs_lookup_slot level asid vref s = Some (level, p)")
apply (fastforce simp: vs_lookup_slot_table_unfold)


   apply (subst (asm) vs_lookup_vref_for_level_eq1)
    apply (rule sym)
    apply assumption


   apply (frule (2) vs_lookup_table_extend)

   apply (frule vs_lookup_min_level) back
   apply (drule vs_lookup_level) back


    apply (case_tac "lvl = asid_pool_level")
     apply (drule vs_lookup_table_pt_at) back
          apply fastforce+
         apply clarsimp
         apply (frule vs_lookup_asid_pool)
          apply fastforce
         apply (clarsimp simp: asid_pools_of_ko_at obj_at_def)

         apply (drule (1) vs_lookup_table_unique_level, rule refl)
         apply fastforce+

         apply clarsimp
         apply (prop_tac "level' + 1 \<le> level")
          apply (fastforce simp: bit0.plus_one_leq)


         apply (erule_tac x=level in allE)
         apply (drule mp)

          apply (subst vs_lookup_slot_vref_for_level[symmetric])
           apply assumption
          apply (simp only:)
          apply (subst vs_lookup_slot_vref_for_level)
           apply assumption
          apply (fastforce simp: vs_lookup_slot_table_unfold)
          apply fastforce


(* second bit *)

apply (clarsimp simp: obind_def split: if_splits option.splits)

(* second thing *)

  apply (clarsimp simp: state_vrefs_def opt_map_def)

apply (intro exI conjI)
apply (rule refl)
apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte ])
apply (clarsimp simp: ptes_of_Some pts_of_Some aobjs_of_Some)
 apply (rule all_ext)
        apply (clarsimp simp: opt_map_def pte_of_def obind_def)
        apply (fastforce dest: pte_ptr_eq)
       apply simp
      apply (fastforce simp: opt_map_def)
     apply (fastforce simp: opt_map_def)
    apply fastforce
    apply fastforce
defer
apply fastforce
apply fastforce
apply fastforce
defer
apply (clarsimp split: if_splits)
apply auto[1]


apply (prop_tac "level_of_slot asid vref p s = level")
apply (subst level_of_slot_def)

apply (rule Greatest_equality)
apply (clarsimp simp: vs_lookup_slot_def obind_def)

 apply (case_tac "ya = asid_pool_level")
    (* lvla = asid_pool_level *)
    apply clarsimp
    apply (frule vs_lookup_slot_no_asid)
         apply (clarsimp simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def split: option.splits)
apply fastforce
apply fastforce
apply fastforce
apply clarsimp
apply clarsimp

apply (subst (asm) vs_lookup_slot_table_unfold) back
apply fastforce+

apply clarsimp
apply (drule (1) vs_lookup_table_unique_level)
apply fastforce+

apply (clarsimp simp: state_vrefs_def)
apply (subst opt_map_def)
apply (case_tac "x = table_base p"; clarsimp)

apply (rule exI, rule conjI)
prefer 2
apply assumption
apply (rule exI)+
apply (rule conjI, rule refl)
apply (clarsimp simp: aobjs_of_Some)
apply (erule_tac x=level in allE)
apply (erule_tac x=vref in allE)
apply clarsimp

apply (rule exI, rule conjI)
prefer 2
apply assumption
apply (rule exI)+
apply (rule conjI, rule refl)
apply (clarsimp simp: aobjs_of_Some)

apply (case_tac "lvl < level")

apply (drule vs_lookup_level) back
apply (subst (asm) vs_lookup_split_Some[where level'=level]) back
apply fastforce
apply fastforce
apply clarsimp

apply (rule_tac x=lvl in exI)
apply (rule_tac x=asida in exI)
apply (rule_tac x=vrefa in exI)


apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte ])
apply (clarsimp simp: ptes_of_Some pts_of_Some aobjs_of_Some)
 apply (rule all_ext)
        apply (clarsimp simp: opt_map_def pte_of_def obind_def)
        apply (fastforce dest: pte_ptr_eq)
       apply simp
      apply (fastforce simp: opt_map_def)
     apply (fastforce simp: opt_map_def)
    apply fastforce
    apply fastforce
  apply (clarsimp split: if_splits)
  apply (intro conjI; clarsimp)
prefer 2
  using vs_lookup_table_extend apply blast

    apply (case_tac "level' = asid_pool_level")
     apply (fastforce dest: vs_lookup_slot_no_asid
                       simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def split: option.splits)
   apply clarsimp

apply (prop_tac "level_of_slot asida vrefa p s = level'")

apply (subst level_of_slot_def)
apply (rule Greatest_equality)
apply clarsimp

    apply (case_tac "ya = asid_pool_level")
     apply (fastforce dest: vs_lookup_slot_no_asid
                       simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def split: option.splits)
   apply clarsimp

apply (drule (1) vs_lookup_slot_unique_level)
apply fastforce+

apply (simp only:)
apply (thin_tac "level_of_slot _ _ _ _ = _")

apply (subst (asm) vs_lookup_slot_table_unfold)
apply fastforce+
apply clarsimp
apply (drule (1) vs_lookup_table_unique_level) back
apply fastforce+


apply (rule_tac x=lvl in exI)
apply (rule_tac x=asida in exI)
apply (rule_tac x=vrefa in exI)
apply clarsimp


apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte ])
apply (clarsimp simp: ptes_of_Some pts_of_Some aobjs_of_Some)
 apply (rule all_ext)
        apply (clarsimp simp: opt_map_def pte_of_def obind_def)
        apply (fastforce dest: pte_ptr_eq)
       apply simp
      apply (fastforce simp: opt_map_def)
     apply (fastforce simp: opt_map_def)
    apply fastforce
    apply fastforce
apply (case_tac "\<exists>level'. vs_lookup_slot level' asida vrefa s = Some (level', p) \<and> lvl < level'"; clarsimp)

prefer 2
apply (fastforce dest: vs_lookup_level)
apply (case_tac "level' = asid_pool_level")
apply clarsimp
apply (frule vs_lookup_slot_no_asid)
         apply (clarsimp simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def split: option.splits)
apply fastforce
apply fastforce
apply fastforce
apply clarsimp
apply clarsimp

apply (prop_tac "level_of_slot asida vrefa p s = level'")
apply (erule level_of_slot_vs_lookup_slot)
apply fastforce+
apply (simp only:)
apply (thin_tac "level_of_slot _ _ _ _ = _")

apply (clarsimp simp: vs_lookup_slot_def split: if_splits)
  by (metis vs_lookup_slot_table vs_lookup_slot_unique_level)


definition level_of_table :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> vm_level"
  where
  "level_of_table p s \<equiv>
     GREATEST level. \<exists>asid vref. vref \<in> user_region \<and> vs_lookup_table level asid vref s = Some (level, p)"

lemma level_of_table_vs_lookup_table:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p);
     ptes_of s p = Some pte; level \<le> max_pt_level; vref \<in> user_region; invs s \<rbrakk>
     \<Longrightarrow> level_of_table p s = level"
apply (subst level_of_table_def)
apply (rule Greatest_equality)
apply fastforce
apply clarsimp
thm vs_lookup_slot_no_asid vs_lookup_slot_unique_level
    apply (case_tac "y = asid_pool_level")
apply clarsimp
apply (drule vs_lookup_table_no_asid)
apply simp
apply clarsimp+

apply (drule (1) vs_lookup_table_unique_level)
apply fastforce+
done


lemma state_vrefs_store_NonPageTablePTE':
  "\<lbrakk> invs s; is_aligned p pte_bits; \<forall>level asid vref. vref \<in> user_region \<longrightarrow> vs_lookup_slot level asid vref s \<noteq> Some (level, p);
     \<not> is_PageTablePTE pte;
     kheap s (table_base p) = Some (ArchObj (PageTable pt)) \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>kheap := \<lambda>a. if a = table_base p
                                     then Some (ArchObj (PageTable (\<lambda>a. if a = table_index p then pte else pt a)))
                                     else kheap s a\<rparr>) =
         (\<lambda>x. if x = table_base p \<and> (\<exists>level. \<exists>\<rhd> (level, table_base p) s)
                    then vs_refs_aux (level_of_table (table_base p) s) (PageTable (\<lambda>a. if a = table_index p then pte else pt a))
              else state_vrefs s x)"
  apply (rule all_ext)
  apply safe


(* first thing *)
   apply (subst (asm) state_vrefs_def opt_map_def)+
   apply (clarsimp split: option.splits split del: if_split)
   apply (clarsimp split: if_split_asm option.splits split del: if_split)

(* x = table_base p *)
    apply (subst (asm) vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte])
           apply (clarsimp simp: ptes_of_Some pts_of_Some aobjs_of_Some)
          apply (rule all_ext)
          apply (clarsimp simp: opt_map_def pte_of_def obind_def)
          apply (fastforce dest: pte_ptr_eq)
         apply simp
        apply (fastforce simp: opt_map_def)
       apply (fastforce simp: opt_map_def)
      apply fastforce+
    (* done *)

    apply (clarsimp split: if_splits)
apply safe

    apply (case_tac "level = asid_pool_level")
         apply (fastforce dest: vs_lookup_table_no_asid
                          simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def
                         split: option.splits)
    apply (case_tac "lvl = asid_pool_level")
      apply (drule vs_lookup_level)
      apply (fastforce dest: vs_lookup_table_no_asid
                       simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def
                      split: option.splits)


apply (prop_tac "level_of_table (table_base p) s = level")

apply (erule level_of_table_vs_lookup_table)
apply (fastforce simp: ptes_of_Some pte_of_def obind_def pts_of_Some aobjs_of_Some split: option.splits)
apply fastforce+

apply clarsimp
apply (drule vs_lookup_level)
apply (drule (1) vs_lookup_table_unique_level)
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply (fastforce dest: vs_lookup_level)


(* x = table_base p *)
    apply (subst (asm) vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte])
           apply (clarsimp simp: ptes_of_Some pts_of_Some aobjs_of_Some)
          apply (rule all_ext)
          apply (clarsimp simp: opt_map_def pte_of_def obind_def)
          apply (fastforce dest: pte_ptr_eq)
         apply simp
        apply (fastforce simp: opt_map_def)
       apply (fastforce simp: opt_map_def)
      apply fastforce+
    (* done *)
    apply (clarsimp split: if_splits)
apply (clarsimp simp: state_vrefs_def)
apply (fastforce simp: aobjs_of_Some)



apply (clarsimp split: if_splits)


    apply (case_tac "level = asid_pool_level")
         apply (fastforce dest: vs_lookup_table_no_asid
                          simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def
                         split: option.splits)

apply (prop_tac "level_of_table (table_base p) s = level")
apply (erule level_of_table_vs_lookup_table)
apply (fastforce simp: ptes_of_Some pte_of_def obind_def pts_of_Some aobjs_of_Some split: option.splits)
apply fastforce+

apply (simp only:)
apply (thin_tac "level_of_table _ _ = _")

  apply (clarsimp simp: state_vrefs_def opt_map_def)

apply (intro exI conjI)
apply (rule refl)
apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte ])
apply (clarsimp simp: ptes_of_Some pts_of_Some aobjs_of_Some)
 apply (rule all_ext)
        apply (clarsimp simp: opt_map_def pte_of_def obind_def)
        apply (fastforce dest: pte_ptr_eq)
       apply simp
      apply (fastforce simp: opt_map_def)
     apply (fastforce simp: opt_map_def)
    apply fastforce
    apply fastforce
defer
apply fastforce
apply fastforce
apply fastforce
defer
apply (clarsimp split: if_splits)
apply auto[1]

apply (case_tac "x = table_base p"; clarsimp)
apply (clarsimp simp: state_vrefs_def)
apply (fastforce dest: vs_lookup_level)

  apply (clarsimp simp: state_vrefs_def opt_map_def)

apply (intro exI conjI)
apply (rule refl)
apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte ])
apply (clarsimp simp: ptes_of_Some pts_of_Some aobjs_of_Some)
 apply (rule all_ext)
        apply (clarsimp simp: opt_map_def pte_of_def obind_def)
        apply (fastforce dest: pte_ptr_eq)
       apply simp
      apply (fastforce simp: opt_map_def)
     apply (fastforce simp: opt_map_def)
    apply fastforce
    apply fastforce
defer
apply fastforce
apply fastforce
apply fastforce
defer
apply (clarsimp split: if_splits)
apply auto[1]
done



lemma state_vrefs_store_NonPageTablePTE_wp':
"\<lbrace>\<lambda>s. invs s \<and> \<not> is_PageTablePTE pte \<and>

(\<forall>pt. ako_at (PageTable pt) (table_base p) s \<longrightarrow> is_aligned p pte_bits \<longrightarrow>
 (if \<exists>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<and> vref \<in> user_region
  then (\<exists>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<and> vref \<in> user_region \<and>
                          P (\<lambda>x. (if \<exists>level' vref'. vref' \<in> user_region \<and> vref_for_level vref' (level + 1) = vref_for_level vref (level + 1) \<and>
                                                    p = pt_slot_offset level (table_base p) vref' \<and>
                                                    pt_walk level level' (table_base p) vref' (ptes_of s) = Some (level',x)
                                  then (if x = table_base p
                                        then vs_refs_aux level (PageTable (\<lambda>a. if a = table_index p then pte else pt a))
                                        else {})
                                  else state_vrefs s x)))
else P (\<lambda>x. (if x = table_base p \<and> (\<exists>level. \<exists>\<rhd> (level, table_base p) s)
                    then vs_refs_aux (level_of_table (table_base p) s) (PageTable (\<lambda>a. if a = table_index p then pte else pt a))
              else state_vrefs s x))))
\<rbrace> store_pte p pte \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
unfolding store_pte_def set_pt_def
apply (wpsimp wp: set_object_wp)
apply (case_tac "\<exists>level asid vref.
                           vs_lookup_slot level asid vref s = Some (level, p) \<and> vref \<in> user_region")
apply (erule_tac x=pt in allE)
apply clarsimp
apply (clarsimp simp: fun_upd_def)
apply (subst state_vrefs_store_NonPageTablePTE)
apply fastforce+
apply (clarsimp simp: obj_at_def)
apply (case_tac "level = asid_pool_level")
     apply (fastforce dest: vs_lookup_slot_no_asid
                      simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                      split: option.splits)

apply (case_tac "levela = asid_pool_level")
     apply (fastforce dest: vs_lookup_slot_no_asid
                      simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                      split: option.splits)
apply (drule (1) vs_lookup_slot_unique_level)
apply fastforce+
apply clarsimp
apply (prop_tac "vref_for_level vrefa (level+1) = vref_for_level vref (level+1)")
  apply (metis (mono_tags, hide_lams) vs_lookup_slot_table_base vs_lookup_slot_vref_for_level_eq vs_lookup_table_unique_level)
apply clarsimp

apply clarsimp
apply (erule_tac x=pt in allE)
apply (clarsimp simp: fun_upd_def)
apply (subst state_vrefs_store_NonPageTablePTE')
apply fastforce+
apply (clarsimp simp: obj_at_def)
apply clarsimp
done



definition authorised_page_table_inv :: "'a PAS \<Rightarrow> page_table_invocation \<Rightarrow> bool" where
  "authorised_page_table_inv aag pti \<equiv>
   case pti of PageTableMap cap cslot_ptr pde obj_ref \<Rightarrow>
                 is_subject aag (fst cslot_ptr) \<and> is_subject aag (obj_ref && ~~ mask pt_bits) \<and>
                 pas_cap_cur_auth aag (ArchObjectCap cap)
             | PageTableUnmap cap cslot_ptr \<Rightarrow>
                 is_subject aag (fst cslot_ptr) \<and> aag_cap_auth aag (pasSubject aag) (ArchObjectCap cap)  \<and>
                 (\<forall>p asid vspace_ref. cap = PageTableCap p (Some (asid, vspace_ref))
                                      \<longrightarrow> is_subject_asid aag asid \<and>
                                          (\<forall>x \<in> set [p , p + 2 ^ pte_bits .e. p + 2 ^ pt_bits - 1].
                                                   is_subject aag (x && ~~ mask pt_bits)))"

lemma store_pte_thread_states[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (thread_states s)\<rbrace>"
unfolding store_pte_def set_pt_def
apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: get_tcb_def thread_states_def tcb_states_of_state_def obj_at_def
                 elim!: rsubst[where P=P, OF _ ext])
done

lemma store_pte_thread_bound_ntfns[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
unfolding store_pte_def set_pt_def
apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: get_tcb_def thread_bound_ntfns_def  obj_at_def
                 elim!: rsubst[where P=P, OF _ ext])
done

lemma store_pte_domains_of_state[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (domains_of_state s)\<rbrace>"
unfolding store_pte_def set_pt_def
by (wpsimp wp: set_object_wp)


lemma mapM_x_store_pte_caps_of_state[wp]:
  "mapM_x (swp store_pte InvalidPTE) slots \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  by (wpsimp wp: mapM_x_wp')

lemma state_bits_to_policy_vrefs_subseteq:
"x \<in> state_bits_to_policy (caps_of_state s) (thread_states s) (thread_bound_ntfns s) (cdt s) X
\<Longrightarrow> \<forall>x. X x \<subseteq> state_vrefs s x
\<Longrightarrow>
 x \<in> state_bits_to_policy (caps_of_state s) (thread_states s) (thread_bound_ntfns s) (cdt s) (state_vrefs s)"
apply (case_tac x; clarsimp)
apply (erule state_bits_to_policy.cases)
apply (fastforce intro: state_bits_to_policy.intros)+
done

lemma state_asids_to_policy_vrefs_subseteq:
"x \<in> state_asids_to_policy_aux aag (caps_of_state s) (asid_table s) X
\<Longrightarrow> \<forall>x. X x \<subseteq> state_vrefs s x
\<Longrightarrow>
 x \<in> state_asids_to_policy_aux aag (caps_of_state s) (asid_table s) (state_vrefs s)"
apply (case_tac x; clarsimp)
apply (erule state_asids_to_policy_aux.cases)
apply (fastforce intro: state_asids_to_policy_aux.intros)+
done


lemma store_pte_state_objs_in_policy:
  "\<lbrace>(\<lambda>s. state_objs_in_policy aag s) and invs
and (\<lambda>s. (\<exists>slot ref. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base p) ref)))
\<and>  ((\<exists>asid. vspace_for_asid asid s = Some (table_base p)) \<longrightarrow> table_index p \<notin> kernel_mapping_slots) \<and>
                table_base p \<notin> global_refs s
)\<rbrace>
 store_pte p InvalidPTE
\<lbrace>\<lambda>_ s. state_objs_in_policy aag s\<rbrace>"

  apply (rule hoare_weaken_pre)
   apply (clarsimp simp: state_objs_to_policy_def pred_conj_def)
   apply wps
   apply (rule state_vrefs_store_NonPageTablePTE_wp')
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (rule exI)+
   apply (rule conjI, assumption)
   apply clarsimp

   apply (clarsimp simp: state_objs_to_policy_def)
   apply (erule subsetD)
   apply (clarsimp simp: auth_graph_map_def)
   apply (rule exI, rule conjI, rule refl)+
   apply (erule state_bits_to_policy_vrefs_subseteq)
   apply clarsimp
   apply (clarsimp simp: state_vrefs_def)
   apply (rule exI)
   apply (rule conjI)
    apply (rule_tac x=level in exI)
    apply (rule_tac x="PageTable pt" in exI)
    apply (rule conjI, rule refl)

    apply (case_tac "level = asid_pool_level")
     apply (fastforce dest: vs_lookup_slot_no_asid
                      simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                      split: option.splits)


    apply (subst (asm) vs_lookup_slot_table_unfold)
       apply fastforce+
    apply (fastforce simp: aobjs_of_Some obj_at_def)
   apply (clarsimp simp: vs_refs_aux_def
   graph_of_def)
   apply (clarsimp split: if_splits)
    apply (clarsimp simp: pte_ref2_def)
   apply fastforce

  apply (clarsimp simp: state_objs_to_policy_def)
  apply (erule subsetD)
  apply (clarsimp simp: auth_graph_map_def)
  apply (rule exI, rule conjI, rule refl)+
  apply (erule state_bits_to_policy_vrefs_subseteq)
  apply clarsimp
  apply (clarsimp simp: state_vrefs_def)
  apply (rule exI)
  apply (rule conjI)
   apply (rule_tac x=level in exI)
   apply (rule_tac x="PageTable pt" in exI)
   apply (rule conjI, rule refl)

   apply (fastforce simp: aobjs_of_Some obj_at_def)

  apply (case_tac "level = asid_pool_level")
   apply (fastforce dest: vs_lookup_table_no_asid
                    simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                    split: option.splits)
  apply (drule level_of_table_vs_lookup_table)
      apply (fastforce dest: vs_lookup_slot_no_asid
                       simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                       split: option.splits)+
  apply (simp only:)
  apply (thin_tac "level_of_table _ _ = _")
  apply (clarsimp simp: vs_refs_aux_def
  graph_of_def)
  apply (clarsimp split: if_splits)
   apply (clarsimp simp: pte_ref2_def)
  apply fastforce

  done



(*
lemma store_pte_state_objs_in_policy:
  "\<forall>X Y. (\<forall>x. X x \<subseteq> Y x) \<longrightarrow> P Y \<longrightarrow> P X \<Longrightarrow>

\<lbrace>\<lambda>s. P (state_vrefs s) \<and> invs s \<and> \<not> is_PageTablePTE pte \<and>
(\<exists>slot ref. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base p) ref)))
\<and>  ((\<exists>asid. vspace_for_asid asid s = Some (table_base p)) \<longrightarrow> table_index p \<notin> kernel_mapping_slots) \<and>
                table_base p \<notin> global_refs s\<rbrace>
 store_pte p pte
\<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule state_vrefs_store_NonPageTablePTE_wp')
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (rule exI)+
   apply (rule conjI, assumption)
   apply clarsimp

apply (erule_tac x="(\<lambda>a. if \<exists>level' vref'.
                         vref' \<in> user_region \<and>
                         vref_for_level vref' (level + 1) = vref_for_level vref (level + 1) \<and>
                         p = pt_slot_offset level (table_base p) vref' \<and>
                         pt_walk level level' (table_base p) vref' (ptes_of s) = Some (level', a)
                   then if a = table_base p then vs_refs_aux level (PageTable (\<lambda>a. if a = table_index p then pte else pt a))
                        else {}
                   else state_vrefs s a)" in allE)
apply (erule_tac x="state_vrefs s" in allE)

apply (drule mp) back
prefer 2
apply clarsimp

apply clarsimp


   apply (clarsimp simp: state_vrefs_def)
   apply (rule exI)
   apply (rule conjI)
    apply (rule_tac x=level in exI)
    apply (rule_tac x="PageTable pt" in exI)
    apply (rule conjI, rule refl)

    apply (case_tac "level = asid_pool_level")
     apply (fastforce dest: vs_lookup_slot_no_asid
                      simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                      split: option.splits)


    apply (subst (asm) vs_lookup_slot_table_unfold)
       apply fastforce+
    apply (fastforce simp: aobjs_of_Some obj_at_def)

apply (clarsimp simp: vs_refs_aux_def graph_of_def)
apply (case_tac "ad = table_index p"; clarsimp)


apply (case_tac

   apply (clarsimp simp: vs_refs_aux_def
   graph_of_def)
   apply (clarsimp split: if_splits)
    apply (clarsimp simp: pte_ref2_def)
apply (case_tac pte; clarsimp)
   apply fastforce

apply clarsimp


apply (erule_tac x="(\<lambda>a. if a = table_base p \<and> (\<exists>level. \<exists>\<rhd> (level, table_base p) s)
                   then vs_refs_aux (level_of_table (table_base p) s)
                         (PageTable (\<lambda>a. if a = table_index p then InvalidPTE else pt a))
                   else state_vrefs s a)" in allE)
apply (erule_tac x="state_vrefs s" in allE)

apply (drule mp) back
prefer 2
apply clarsimp


  apply (clarsimp simp: state_vrefs_def)
  apply (rule exI)
  apply (rule conjI)
   apply (rule_tac x=level in exI)
   apply (rule_tac x="PageTable pt" in exI)
   apply (rule conjI, rule refl)

   apply (fastforce simp: aobjs_of_Some obj_at_def)

  apply (case_tac "level = asid_pool_level")
   apply (fastforce dest: vs_lookup_table_no_asid
                    simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                    split: option.splits)
  apply (drule level_of_table_vs_lookup_table)
      apply (fastforce dest: vs_lookup_slot_no_asid
                       simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                       split: option.splits)+
  apply (simp only:)
  apply (thin_tac "level_of_table _ _ = _")
  apply (clarsimp simp: vs_refs_aux_def
  graph_of_def)
  apply (clarsimp split: if_splits)
   apply (clarsimp simp: pte_ref2_def)
  apply fastforce
  done
*)


lemma store_pte_mapM_x_state_objs_in_policy:
 "\<lbrace>state_objs_in_policy aag and invs and
   (\<lambda>s. \<forall>x \<in> set slots. table_base x \<notin> global_refs s \<and> (\<forall>asid. vspace_for_asid asid s \<noteq> Some (table_base x))
)\<rbrace>
 mapM_x (swp store_pte InvalidPTE) slots
\<lbrace>\<lambda>_. state_objs_in_policy aag\<rbrace>"
apply (rule hoare_strengthen_post)
apply (rule mapM_x_wp[where S="set slots"])

apply (rule hoare_weaken_pre)
apply (clarsimp simp: state_objs_to_policy_def pred_conj_def)
apply (rule hoare_vcg_conj_lift)
apply wps
apply (rule state_vrefs_store_NonPageTablePTE_wp')
   apply (wp store_pte_invs hoare_vcg_const_Ball_lift hoare_vcg_ex_lift hoare_vcg_all_lift)
apply clarsimp
   apply (clarsimp simp: wellformed_pte_def)
apply (rule conjI)
apply (thin_tac P for P)
apply clarsimp
apply (rule exI)+
apply (rule conjI, assumption)
apply clarsimp

apply (clarsimp simp: state_objs_to_policy_def)
apply (erule subsetD)
apply (clarsimp simp: auth_graph_map_def)
apply (rule exI, rule conjI, rule refl)+
apply (erule state_bits_to_policy_vrefs_subseteq)
apply clarsimp
apply (clarsimp simp: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
apply (rule_tac x=level in exI)
apply (rule_tac x="PageTable pt" in exI)
apply (rule conjI, rule refl)

apply (case_tac "level = asid_pool_level")
     apply (fastforce dest: vs_lookup_slot_no_asid
                      simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                      split: option.splits)


apply (subst (asm) vs_lookup_slot_table_unfold)
apply fastforce+
apply (fastforce simp: aobjs_of_Some obj_at_def)
apply (clarsimp simp: vs_refs_aux_def
graph_of_def)
apply (clarsimp split: if_splits)
apply (clarsimp simp: pte_ref2_def)
apply fastforce

apply (clarsimp simp: state_objs_to_policy_def)
apply (erule subsetD)
apply (clarsimp simp: auth_graph_map_def)
apply (rule exI, rule conjI, rule refl)+
apply (erule state_bits_to_policy_vrefs_subseteq)
apply clarsimp
apply (clarsimp simp: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
apply (rule_tac x=level in exI)
apply (rule_tac x="PageTable pt" in exI)
apply (rule conjI, rule refl)

apply (fastforce simp: aobjs_of_Some obj_at_def)

apply (case_tac "level = asid_pool_level")
     apply (fastforce dest: vs_lookup_table_no_asid
                      simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                      split: option.splits)
apply (drule level_of_table_vs_lookup_table)
     apply (fastforce dest: vs_lookup_slot_no_asid
                      simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                      split: option.splits)+
apply (simp only:)
apply (thin_tac "level_of_table _ _ = _")
apply (clarsimp simp: vs_refs_aux_def
graph_of_def)
apply (clarsimp split: if_splits)
apply (clarsimp simp: pte_ref2_def)
apply fastforce

apply clarsimp

apply clarsimp
done

lemma store_pte_state_asids_to_policy:
  "\<lbrace>(\<lambda>s. state_asids_to_policy aag s \<subseteq> pasPolicy aag) and invs
and (\<lambda>s. (\<exists>slot ref. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base p) ref)))
\<and>  ((\<exists>asid. vspace_for_asid asid s = Some (table_base p)) \<longrightarrow> table_index p \<notin> kernel_mapping_slots) \<and>
                table_base p \<notin> global_refs s
)\<rbrace>
 store_pte p InvalidPTE
\<lbrace>\<lambda>_ s. state_asids_to_policy aag s \<subseteq> pasPolicy aag\<rbrace>"
apply (rule hoare_weaken_pre)
apply (clarsimp simp: state_objs_to_policy_def pred_conj_def)
apply wps
apply (rule state_vrefs_store_NonPageTablePTE_wp')
   apply (wpsimp wp: store_pte_invs hoare_vcg_const_Ball_lift hoare_vcg_ex_lift hoare_vcg_all_lift hoare_vcg_imp_lift')

apply (rule conjI)
apply clarsimp

apply (rule exI)+
apply (rule conjI, assumption)
apply clarsimp

apply (erule subsetD)
apply (erule state_asids_to_policy_vrefs_subseteq)
apply clarsimp
apply (clarsimp simp: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
apply (rule_tac x=level in exI)
apply (rule_tac x="PageTable pt" in exI)
apply (rule conjI, rule refl)

apply (case_tac "level = asid_pool_level")
     apply (fastforce dest: vs_lookup_slot_no_asid
                      simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                      split: option.splits)


apply (subst (asm) vs_lookup_slot_table_unfold)
apply fastforce+
apply (fastforce simp: aobjs_of_Some obj_at_def)
apply (clarsimp simp: vs_refs_aux_def
graph_of_def)
apply (clarsimp split: if_splits)
apply (clarsimp simp: pte_ref2_def)
apply fastforce

apply (clarsimp)
apply (erule subsetD)
apply (erule state_asids_to_policy_vrefs_subseteq)
apply clarsimp
apply (clarsimp simp: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
apply (rule_tac x=level in exI)
apply (rule_tac x="PageTable pt" in exI)
apply (rule conjI, rule refl)

apply (fastforce simp: aobjs_of_Some obj_at_def)

apply (case_tac "level = asid_pool_level")
     apply (fastforce dest: vs_lookup_table_no_asid
                      simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                      split: option.splits)
apply (drule level_of_table_vs_lookup_table)
     apply (fastforce dest: vs_lookup_slot_no_asid
                      simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                      split: option.splits)+
apply (simp only:)
apply (thin_tac "level_of_table _ _ = _")
apply (clarsimp simp: vs_refs_aux_def
graph_of_def)
apply (clarsimp split: if_splits)
apply (clarsimp simp: pte_ref2_def)
apply fastforce
done


lemma store_pte_mapM_x_state_asids_to_policy:
 "\<lbrace>(\<lambda>s. state_asids_to_policy aag s \<subseteq> pasPolicy aag) and invs
and (\<lambda>s. \<forall>x \<in> set slots. table_base x \<notin> global_refs s \<and> (\<forall>asid. vspace_for_asid asid s \<noteq> Some (table_base x)))\<rbrace>
 mapM_x (swp store_pte InvalidPTE) slots
\<lbrace>\<lambda>_ s. state_asids_to_policy aag s \<subseteq> pasPolicy aag\<rbrace>"
apply (rule hoare_strengthen_post)
apply (rule mapM_x_wp[where S="set slots"])

apply (rule hoare_weaken_pre)
apply (clarsimp simp: state_objs_to_policy_def pred_conj_def)
apply (rule hoare_vcg_conj_lift)
apply wps
apply (rule state_vrefs_store_NonPageTablePTE_wp')
   apply (wpsimp wp: store_pte_invs hoare_vcg_const_Ball_lift hoare_vcg_ex_lift hoare_vcg_all_lift hoare_vcg_imp_lift')
apply clarsimp
   apply (clarsimp simp: wellformed_pte_def)
apply (rule conjI)
apply (thin_tac P for P)
apply clarsimp

apply (rule exI)+
apply (rule conjI, assumption)
apply clarsimp

apply (erule subsetD)
apply (erule state_asids_to_policy_vrefs_subseteq)
apply clarsimp
apply (clarsimp simp: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
apply (rule_tac x=level in exI)
apply (rule_tac x="PageTable pt" in exI)
apply (rule conjI, rule refl)

apply (case_tac "level = asid_pool_level")
     apply (fastforce dest: vs_lookup_slot_no_asid
                      simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                      split: option.splits)


apply (subst (asm) vs_lookup_slot_table_unfold)
apply fastforce+
apply (fastforce simp: aobjs_of_Some obj_at_def)
apply (clarsimp simp: vs_refs_aux_def
graph_of_def)
apply (clarsimp split: if_splits)
apply (clarsimp simp: pte_ref2_def)
apply fastforce

apply (clarsimp)
apply (erule subsetD)
apply (erule state_asids_to_policy_vrefs_subseteq)
apply clarsimp
apply (clarsimp simp: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
apply (rule_tac x=level in exI)
apply (rule_tac x="PageTable pt" in exI)
apply (rule conjI, rule refl)

apply (fastforce simp: aobjs_of_Some obj_at_def)

apply (case_tac "level = asid_pool_level")
     apply (fastforce dest: vs_lookup_table_no_asid
                      simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                      split: option.splits)
apply (drule level_of_table_vs_lookup_table)
     apply (fastforce dest: vs_lookup_slot_no_asid
                      simp: ptes_of_Some pts_of_Some aobjs_of_Some pte_of_def obind_def obj_at_def
                      split: option.splits)+
apply (simp only:)
apply (thin_tac "level_of_table _ _ = _")
apply (clarsimp simp: vs_refs_aux_def
graph_of_def)
apply (clarsimp split: if_splits)
apply (clarsimp simp: pte_ref2_def)
apply fastforce

apply clarsimp
apply clarsimp
done


lemma mapM_x_store_pte_cdt[wp]:
  "mapM_x (swp store_pte InvalidPTE) slots \<lbrace>\<lambda>s. P (cdt s)\<rbrace>"
  by (wpsimp wp: mapM_x_wp')

lemma mapM_x_swp_store_pte_pas_refined:
 "\<lbrace>pas_refined aag and invs and
(\<lambda>s. \<forall>x \<in> set slots. table_base x \<notin> global_refs s \<and> (\<forall>asid. vspace_for_asid asid s \<noteq> Some (table_base x)))\<rbrace>
 mapM_x (swp store_pte InvalidPTE) slots
\<lbrace>\<lambda>_ s. pas_refined aag s\<rbrace>"
supply state_asids_to_policy_arch_def[simp del]
apply (simp add: pas_refined_def)
apply wpsimp
apply (rule hoare_vcg_conj_lift, (wpsimp wp: mapM_x_wp_inv ; fail))+
apply (wpsimp wp: store_pte_mapM_x_state_asids_to_policy store_pte_mapM_x_state_objs_in_policy)
apply clarsimp
done

lemma dmo_state_vrefs[wp]:
  "do_machine_op f \<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace>"
  by (wpsimp wp: dmo_wp)

lemma dmo_thread_bound_ntfns[wp]:
  "do_machine_op f \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
  by (wpsimp wp: dmo_wp)

lemma dmo_thread_states[wp]:
  "do_machine_op f \<lbrace>\<lambda>s. P (thread_states s)\<rbrace>"
  by (wpsimp wp: dmo_wp)


lemma mapM_swp_store_pte_invs_unmap:
  "\<lbrace>invs and
    (\<lambda>s.  table_base p \<notin> global_refs s \<and>
                        (\<forall>asid. vspace_for_asid asid s \<noteq> Some (table_base p))) and
    K (pte = InvalidPTE)\<rbrace>
  store_pte p pte \<lbrace>\<lambda>_. invs\<rbrace>"
   apply simp
   apply (wp store_pte_invs hoare_vcg_const_Ball_lift hoare_vcg_ex_lift hoare_vcg_all_lift)
   apply (clarsimp simp: wellformed_pte_def)
  done

(* FIXME ryanb - use for simplifying some lemmas *)
thm perform_pt_inv_unmap_invs


lemma FIXME_wordAND_wordNOT_mask_plus:
   "x && ~~mask n = x \<Longrightarrow> (x + mask n) && ~~mask n = x"
  by (metis AND_NOT_mask_plus_AND_mask_eq VSpaceEntries_AI.neg_mask_add_mask add_right_imp_eq word_bw_same(1))

lemma table_base_mask:
"p && ~~mask b = p \<Longrightarrow>
       p' && ~~mask b = 0 \<Longrightarrow>
       (p + p') && ~~mask b = p"
  by (metis Groups.add_ac(2) VSpaceEntries_AI.neg_mask_add_mask add_left_imp_eq mask_eq_x_eq_0 word_plus_and_or_coroll2)



lemma store_pte_pas_refined:
  "\<lbrace>pas_refined aag and invs
and (\<lambda>s. (\<exists>slot ref. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base p) ref)))
\<and>  ((\<exists>asid. vspace_for_asid asid s = Some (table_base p)) \<longrightarrow> table_index p \<notin> kernel_mapping_slots) \<and>
                table_base p \<notin> global_refs s
)\<rbrace>
 store_pte p InvalidPTE
\<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
supply state_asids_to_policy_arch_def[simp del]
apply (clarsimp simp: pas_refined_def)
apply (wpsimp wp: store_pte_state_objs_in_policy store_pte_state_asids_to_policy)
done

lemma perform_pt_inv_unmap_pas_refined:
 "\<lbrace>pas_refined aag and invs and valid_pti (PageTableUnmap cap ct_slot)
                            and K (authorised_page_table_inv aag (PageTableUnmap cap ct_slot))\<rbrace>
  perform_pt_inv_unmap cap ct_slot
  \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pt_inv_unmap_def unmap_page_table_def
  apply (rule hoare_gen_asm)
  apply (wpsimp wp: set_cap_pas_refined get_cap_wp)
       apply (strengthen invs_psp_aligned invs_vspace_objs invs_arch_state)
       apply wps
       apply (rule hoare_vcg_all_lift[OF hoare_vcg_imp_lift'[OF mapM_x_wp_inv]], wpsimp wp: mapM_x_wp_inv)
       apply (rule hoare_vcg_conj_lift[OF hoare_strengthen_post[OF mapM_x_swp_store_pte_pas_refined]], assumption)
       apply (rule hoare_vcg_conj_lift[OF hoare_strengthen_post[OF mapM_x_swp_store_pte_invs_unmap]], assumption)
       apply (wpsimp wp: mapM_x_wp_inv)
      apply (wpsimp wp: pt_lookup_from_level_wrp  store_pte_invs_unmap store_pte_pas_refined
                        static_imp_wp hoare_vcg_imp_lift' hoare_vcg_ball_lift hoare_vcg_all_lift)+
  apply (clarsimp simp: conj_ac)
  apply (rule conjI)
   apply (fastforce simp: is_PageTableCap_def authorised_page_table_inv_def
                          valid_pti_def update_map_data_def cte_wp_at_caps_of_state)
  apply clarsimp
  apply (case_tac "cte_wp_at ((=) x) ct_slot s"; clarsimp)
  apply (clarsimp simp: is_PageTableCap_def authorised_page_table_inv_def valid_pti_def
                        valid_arch_cap_def cte_wp_at_caps_of_state update_map_data_def
                        aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                        cap_links_asid_slot_def cap_links_irq_def is_transferable.simps)
  apply (prop_tac "\<forall>sl \<in> set [acap_obj cap, acap_obj cap + 2 ^ pte_bits .e. acap_obj cap + 2 ^ pt_bits - 1].
                   table_base sl = acap_obj cap \<and> acap_obj cap \<notin> global_refs s \<and>
                   (\<forall>asid. vspace_for_asid asid s \<noteq> Some (acap_obj cap))")
   apply clarsimp
   apply (intro context_conjI)
     apply (drule (1) caps_of_state_aligned_page_table)
     apply (simp only: is_aligned_neg_mask_eq')
     apply (clarsimp simp: add_mask_fold)
     apply (drule subsetD[OF upto_enum_step_subset], clarsimp)
     apply (drule neg_mask_mono_le[where n=pt_bits])
     apply (drule neg_mask_mono_le[where n=pt_bits])
     apply (fastforce dest: FIXME_wordAND_wordNOT_mask_plus)
    apply (fastforce simp: cte_wp_at_caps_of_state cap_range_def
                     dest: invs_valid_global_refs valid_global_refsD)
   apply clarsimp
   apply (frule vspace_for_asid_target)
   apply (drule valid_vs_lookupD; clarsimp)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp)
   apply (drule (1) cap_to_pt_is_pt_cap)
     apply (clarsimp simp: in_omonad obj_at_def)
    apply (fastforce intro: valid_objs_caps)
   apply (clarsimp simp: is_cap_simps)
  apply clarsimp
  apply (rule_tac x=a in exI, clarsimp)
  apply (case_tac "level = asid_pool_level")
   apply (fastforce dest: vs_lookup_slot_no_asid)
  apply (clarsimp simp: valid_arch_cap_def wellformed_mapdata_def)
  apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
  apply (intro conjI)
    apply (fastforce dest: reachable_page_table_not_global)
   apply (case_tac ct_slot; clarsimp)
   apply (frule vs_lookup_table_pt_at; clarsimp?)
   apply (drule vs_lookup_table_valid_cap; clarsimp?)
   apply (fastforce simp: valid_cap_def valid_arch_cap_def valid_arch_cap_ref_def obj_at_def
                    dest: caps_of_state_valid split: cap.splits arch_cap.splits)
  apply (metis AND_twice is_aligned_neg_mask_eq' table_index_max_level_slots vs_lookup_table_vspace)
  done




lemma state_vrefs_store_PageTablePTE:
  "\<lbrakk> invs s; is_aligned p pte_bits; vs_lookup_slot level asid vref s = Some (level, p);
     vref \<in> user_region; is_PageTablePTE pte;  invalid_pte_at p s;
     pts_of s (the (pte_ref pte)) = Some empty_pt; the (pte_ref pte) \<noteq> table_base p;
     kheap s (table_base p) = Some (ArchObj (PageTable pt)) \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>kheap := \<lambda>a. if a = table_base p
                                     then Some (ArchObj (PageTable (\<lambda>a. if a = table_index p then pte else pt a)))
                                     else kheap s a\<rparr>) =
         (\<lambda>x. if x = table_base p
              then vs_refs_aux level (PageTable (\<lambda>a. if a = table_index p then pte else pt a))
              else state_vrefs s x)"
  apply (rule all_ext)

  apply (case_tac "level = asid_pool_level")
     apply (clarsimp simp: vs_lookup_slot_def split: if_splits)
     apply (clarsimp simp: vs_lookup_table_def split: if_splits)
     apply (drule pool_for_asid_no_pte)
        apply (simp add: ptes_of_Some pts_of_Some aobjs_of_Some)
       apply fastforce
      apply fastforce
     apply fastforce

apply safe


(* first thing *)

   apply (clarsimp simp: state_vrefs_def opt_map_def split: option.splits)
   apply (case_tac "x = pptr_from_pte pte")
    (* x = pptr_from_pte pte *)
  apply clarsimp
    apply (clarsimp simp: pte_ref_def2)
    apply (clarsimp split: if_splits)
    apply (clarsimp simp: vs_refs_aux_def graph_of_def pte_ref2_def)
      (* x \<noteq> pptr_from_pte pte *)
   apply (drule_tac s=s and pte=pte and p=p in vs_lookup_PageTablePTE[rotated 9])
    (* discharging above *)
               apply (clarsimp simp: pts_of_Some aobjs_of_Some)
              apply fastforce+
        apply (rule all_ext)
        apply (clarsimp simp: opt_map_def pte_of_def obind_def)
        apply (fastforce dest: pte_ptr_eq)
       apply simp
      apply (fastforce simp: opt_map_def)
     apply (fastforce simp: opt_map_def)
    apply clarsimp
(* done *)
   apply clarsimp
   apply (drule vs_lookup_level)
   apply (case_tac "lvl = asid_pool_level")
    (* lvla = asid_pool_level *)
    apply clarsimp
    apply (frule vs_lookup_asid_pool)
     apply fastforce
    apply (fastforce simp: asid_pools_of_ko_at obj_at_def)
    (* lvla \<noteq> asid_pool_level *)
   apply clarsimp
   apply (frule vs_lookup_table_pt_at)
        apply fastforce+
   apply (clarsimp simp: typ_at_eq_kheap_obj)
   apply (case_tac "x = table_base p"; clarsimp)


    apply (subst (asm) vs_lookup_slot_table)
     apply clarsimp
    apply clarsimp
    apply (prop_tac "is_aligned pt_ptr pt_bits")
     apply (rule is_aligned_pt[rotated])
      apply fastforce
     apply (erule vs_lookup_table_pt_at; fastforce)
    apply clarsimp
    apply (drule (1) vs_lookup_table_unique_level; fastforce)
    (* x \<noteq> table_base p *)
   apply fastforce

(* second thing *)

  apply (clarsimp simp: state_vrefs_def opt_map_def)


   apply (frule vs_lookup_slot_table_base)
      apply clarsimp+

   apply (case_tac "x = table_base p"; clarsimp)

   apply (drule_tac pte=pte and s'="(s\<lparr>kheap :=
                                 \<lambda>a. if a = table_base p
                                      then Some (ArchObj (PageTable (\<lambda>a. if a = table_index p then pte else pt a)))
                                      else kheap s a\<rparr>)" in vs_lookup_PageTablePTE'[rotated 9])
            apply fastforce+
        apply (rule all_ext)
        apply (clarsimp simp: opt_map_def pte_of_def obind_def)
        apply (fastforce dest: pte_ptr_eq)
       apply simp
      apply (fastforce simp: opt_map_def)
     apply (fastforce simp: opt_map_def)
    apply clarsimp
   apply fastforce

  apply (drule_tac pte=pte and s'="(s\<lparr>kheap :=
                                \<lambda>a. if a = table_base p
                                     then Some (ArchObj (PageTable (\<lambda>a. if a = table_index p then pte else pt a)))
                                     else kheap s a\<rparr>)" in vs_lookup_PageTablePTE'[rotated 9]) back
           apply fastforce+
       apply (rule all_ext)
       apply (clarsimp simp: opt_map_def pte_of_def obind_def)
       apply (fastforce dest: pte_ptr_eq)
      apply simp
     apply (fastforce simp: opt_map_def)
    apply (fastforce simp: opt_map_def)
   apply clarsimp
  apply fastforce
  done


lemma state_vrefs_store_PageTablePTE_wp:
"\<lbrace>\<lambda>s. invs s \<and> is_PageTablePTE pte \<and> invalid_pte_at p s \<and>
pts_of s (the (pte_ref pte)) = Some empty_pt \<and> the (pte_ref pte) \<noteq> table_base p \<and>
(\<exists>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<and> vref \<in> user_region \<and>
(\<forall>pt. ako_at (PageTable pt) (table_base p) s \<longrightarrow>
P (\<lambda>x. if x = table_base p
                   then vs_refs_aux level (PageTable (\<lambda>a. if a = table_index p then pte else pt a))
                   else state_vrefs s x)))
\<rbrace> store_pte p pte \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
unfolding store_pte_def set_pt_def
apply (wpsimp wp: set_object_wp)
apply (clarsimp simp: fun_upd_def)
apply (subst state_vrefs_store_PageTablePTE)
apply fastforce+
apply (clarsimp simp: obj_at_def)
apply clarsimp
done




lemma perform_pt_inv_map_pas_refined[wp]:
"\<lbrace>pas_refined aag and invs and valid_pti (PageTableMap acap (a, b) pte p)
and K (authorised_page_table_inv aag (PageTableMap acap (a, b) pte p))\<rbrace>
            perform_pt_inv_map acap (a,b) pte p
            \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pt_inv_map_def
  apply (rule hoare_gen_asm)
  apply wpsimp
    apply (clarsimp simp: pas_refined_def state_objs_to_policy_def)
   apply (wps | wpsimp wp: state_vrefs_store_PageTablePTE_wp arch_update_cap_invs_map  vs_lookup_slot_lift
                     hoare_vcg_ex_lift hoare_vcg_all_lift hoare_vcg_imp_lift' set_cap_arch_obj_neg set_cap_state_vrefs)+


  apply (clarsimp simp: valid_pti_def)
  apply (clarsimp simp: conj_ac )
  apply (case_tac acap; clarsimp)
  apply (intro conjI impI)
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (clarsimp simp: is_arch_update_def is_arch_cap_def cap_master_cap_def)
     apply (prop_tac "valid_cap cap s")
      apply (rule cte_wp_valid_cap)
       apply (fastforce simp: cte_wp_at_caps_of_state)
      apply fastforce
     apply (case_tac cap; clarsimp)
     apply (case_tac x12; clarsimp)
     apply (case_tac x42; clarsimp)
     apply (clarsimp simp: valid_cap_def cap_aligned_def valid_arch_cap_def)

    apply clarsimp
    apply (clarsimp simp: vs_lookup_slot_def split: if_splits)

     apply (clarsimp simp: vs_lookup_table_def)
     apply (clarsimp simp: invalid_pte_at_def)
     apply (drule pool_for_asid_no_pte)
        apply (simp)
       apply fastforce
      apply fastforce
     apply simp

    apply clarsimp

    apply (prop_tac "is_aligned ba pt_bits")
     apply (drule (2) vs_lookup_table_is_aligned)
        apply fastforce
       apply fastforce
      apply fastforce
     apply clarsimp
    apply (rename_tac vref' ao pt')
    apply clarsimp
    apply (drule (1) vs_lookup_table_target)
    apply (drule valid_vs_lookupD, erule vref_for_level_user_region; clarsimp)
    apply (prop_tac "is_pt_cap cap")
     apply (erule_tac s=s in valid_cap_to_pt_cap[rotated])
  using pt_at_eq apply blast
     apply (rule cte_wp_valid_cap)
      apply (fastforce simp: cte_wp_at_caps_of_state)
     apply fastforce

    apply (frule (1) cap_to_pt_is_pt_cap, simp, fastforce intro: valid_objs_caps)
    apply (clarsimp simp: is_cap_simps)
    apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply (clarsimp simp: is_arch_update_def cap_master_cap_def split: cap.splits arch_cap.splits option.splits)

    apply (drule (1) unique_table_refsD[rotated])
      apply clarsimp
     apply fastforce
    apply (clarsimp simp: table_cap_ref_def)

   apply (erule cte_wp_at_weakenE)
   apply clarsimp
   apply (case_tac c; clarsimp)
   apply (clarsimp simp: vs_cap_ref_def vs_cap_ref_arch_def split: arch_cap.splits)
   apply (clarsimp simp: is_arch_update_def cap_master_cap_def)


  apply (rule_tac x=level in exI)
  apply (rename_tac asid ao)
  apply (rule_tac x=asid in exI)
  apply (rule_tac x=vref in exI)
  apply clarsimp

  apply (intro conjI impI; (fastforce | (clarsimp simp: pas_refined_def; fail))?)
       apply clarsimp
  using Invariants_AI.cte_wp_at_cte_at apply blast

      apply clarsimp
      apply (erule state_asids_to_policy_aux.cases)
  using Invariants_AI.cte_wp_at_cte_at apply blast
  using Invariants_AI.cte_wp_at_cte_at apply blast
  using Invariants_AI.cte_wp_at_cte_at apply blast
  using Invariants_AI.cte_wp_at_cte_at apply blast

    apply (clarsimp split: if_splits)
    apply (clarsimp simp: pas_refined_def)
    apply (erule state_irqs_to_policy_aux.cases)
    apply (clarsimp split: if_splits)
    apply (fastforce dest: sita_controlled)

(* state_asids_to_policy *)
   apply clarsimp
   apply (erule state_asids_to_policy_aux.cases)

     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (clarsimp split: if_splits)

      apply (clarsimp simp: authorised_page_table_inv_def)
      apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def cap_links_asid_slot_def label_owns_asid_slot_def)
     apply (clarsimp simp: pas_refined_def)
     apply (erule subsetD) back
  thm sata_asid
     apply (fastforce dest: sata_asid)
    apply clarsimp
    apply (clarsimp split: if_splits)
     prefer 2
     apply (fastforce simp: pas_refined_def dest: subsetD dest!: sata_asid_lookup)
    apply (clarsimp simp: vs_refs_aux_def)
   apply (fastforce simp: pas_refined_def dest: subsetD dest!: state_asids_to_policy_aux.intros)

  apply clarsimp
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (clarsimp simp: auth_graph_map_def)
  apply (erule state_bits_to_policy.cases)
    (* sbta_caps *)
        apply (clarsimp simp: pas_refined_def is_arch_update_def cap_master_cap_def
                              auth_graph_map_def state_objs_to_policy_def
                       split: if_splits cap.splits arch_cap.splits option.splits;
               fastforce dest: sbta_caps simp: cap_auth_conferred_def arch_cap_auth_conferred_def)
    (* sbta_untyped *)
        apply (clarsimp simp: pas_refined_def is_arch_update_def cap_master_cap_def
                              auth_graph_map_def state_objs_to_policy_def
                       split: if_splits cap.splits arch_cap.splits option.splits;
               fastforce dest: sbta_untyped simp: cap_auth_conferred_def arch_cap_auth_conferred_def)
    (* sbta_ts *)
        apply (clarsimp simp: pas_refined_def is_arch_update_def cap_master_cap_def
                              auth_graph_map_def state_objs_to_policy_def
                       split: if_splits cap.splits arch_cap.splits option.splits;
               fastforce dest: sbta_ts simp: cap_auth_conferred_def arch_cap_auth_conferred_def)
    (* sbta_bounds *)
        apply (clarsimp simp: pas_refined_def is_arch_update_def cap_master_cap_def
                              auth_graph_map_def state_objs_to_policy_def
                       split: if_splits cap.splits arch_cap.splits option.splits;
               fastforce dest: sbta_bounds simp: cap_auth_conferred_def arch_cap_auth_conferred_def)
    (* sbta_cdt *)
    apply (clarsimp simp: is_arch_update_def cap_master_cap_def split: cap.splits arch_cap.splits option.splits)
    apply (clarsimp simp: pas_refined_def)
    apply (erule subsetD)
    apply (clarsimp simp: auth_graph_map_def state_objs_to_policy_def)
    apply (clarsimp split: if_splits)
     apply (rule exI, rule conjI, rule refl)+
     apply (drule_tac caps="caps_of_state s" in sbta_cdt)
      apply simp
      apply clarsimp
      apply (fastforce elim: is_transferable.cases)
     apply fastforce
    apply (rule exI, rule conjI, rule refl)+
    apply (drule_tac caps="caps_of_state s" in sbta_cdt)
     apply simp
    apply clarsimp
    apply (fastforce elim: is_transferable.cases)
    (* sbta_cdt_transferable *)
   apply (clarsimp simp: is_arch_update_def cap_master_cap_def split: cap.splits arch_cap.splits option.splits)
   apply (clarsimp simp: pas_refined_def)
   apply (erule subsetD)
   apply (clarsimp simp: auth_graph_map_def state_objs_to_policy_def)
   apply (fastforce dest: sbta_cdt_transferable)
    (* sbta_vref *)
  apply (clarsimp split: if_splits)
   prefer 2
   apply (clarsimp simp: is_arch_update_def cap_master_cap_def split: cap.splits arch_cap.splits option.splits)
   apply (clarsimp simp: pas_refined_def)
   apply (erule subsetD)
   apply (clarsimp simp: auth_graph_map_def state_objs_to_policy_def)
   apply (fastforce dest: sbta_vref)

  apply (clarsimp simp: authorised_page_table_inv_def)

apply (simp only: vs_refs_aux_def arch_kernel_obj.case)
apply clarsimp

apply (case_tac "level \<noteq> max_pt_level \<or> aa \<notin> kernel_mapping_slots"; clarsimp simp: word_le_not_less)

apply (subgoal_tac "(pasSubject aag, baa, pasObjectAbs aag ac) \<in> pasPolicy aag")
apply clarsimp
apply (thin_tac "_ \<notin> _")

  apply (clarsimp simp: vs_refs_aux_def graph_of_def)

apply (subgoal_tac "(pasSubject aag, baa, pasObjectAbs aag ac) \<in> pasPolicy aag")
apply clarsimp

  apply (case_tac pte; clarsimp)
  apply (clarsimp simp: pte_ref2_def aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def)
  apply (case_tac "aa = table_index p"; clarsimp)


  apply (clarsimp simp: is_arch_update_def cap_master_cap_def split: cap.splits arch_cap.splits option.splits)
  apply (clarsimp simp: pas_refined_def)
  apply (erule subsetD)
  apply (clarsimp simp: auth_graph_map_def state_objs_to_policy_def)
  apply (rule_tac x="table_base p" in exI, rule conjI)
   apply simp
  apply (rule exI, rule conjI, rule refl)
  apply (rule sbta_vref)
  apply (clarsimp simp: state_vrefs_def)
  thm sbta_vref

  apply (case_tac "level = asid_pool_level")
   apply (clarsimp simp: vs_lookup_slot_def split: if_splits)

   apply (clarsimp simp: vs_lookup_table_def)
   apply (clarsimp simp: invalid_pte_at_def)
   apply (drule pool_for_asid_no_pte)
      apply (simp)
     apply fastforce
    apply fastforce
   apply simp

  apply clarsimp
  apply (drule vs_lookup_slot_table_base)
     apply clarsimp+

  apply (rule exI, rule conjI)
   apply (rule exI, rule exI)
   apply (rule conjI, rule refl)
   apply (rule exI)+
   apply (rule conjI, assumption)
   apply (simp add: obj_at_def aobjs_of_Some)
  apply (clarsimp simp: vs_refs_aux_def graph_of_def)
  apply (clarsimp simp: pte_ref2_def)
  apply fastforce
  done



(* FIXME ryanb: resume *)
lemma perform_page_table_invocation_pas_refined:
  "\<lbrace>pas_refined aag and invs and valid_pti iv
and K (authorised_page_table_inv aag iv)\<rbrace> perform_page_table_invocation iv \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
unfolding perform_page_table_invocation_def
apply wpsimp
apply (wpsimp wp: perform_pt_inv_unmap_pas_refined perform_pt_inv_map_pas_refined)+
apply (case_tac iv; clarsimp)
done



lemma auth_graph_map_def2:
  "auth_graph_map f S = (\<lambda>(x, auth, y). (f x, auth, f y)) ` S"
  by (auto simp add: auth_graph_map_def image_def intro: rev_bexI)

(* FIXME move to AInvs *)
lemma store_pte_ekheap[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (ekheap s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wp get_object_wp)
  apply simp
  done


lemma set_asid_pool_st_vrefs[wp]:
  "\<lbrace>\<lambda>s. P ((state_vrefs s) (p := (\<lambda>(r, p). (p, ucast r, AASIDPool, Control)) ` graph_of pool))\<rbrace>
   set_asid_pool p pool
   \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: state_vrefs_def fun_upd_def[symmetric] fun_upd_comp obj_at_def
                        vs_refs_aux_def
                 split: kernel_object.split_asm arch_kernel_obj.split_asm
                 elim!: rsubst[where P=P, OF _ ext])
  oops

lemma set_asid_pool_thread_states[wp]:
  "set_asid_pool p pool \<lbrace>\<lambda>s. P (thread_states s)\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: set_object_wp_strong)
  apply (clarsimp simp: thread_states_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm option.split)
  done

lemma set_asid_pool_thread_bound_ntfns[wp]:
  "set_asid_pool p pool \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: set_object_wp_strong)
  apply (clarsimp simp: thread_bound_ntfns_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm option.split)
  done

(* FIXME move to AInvs *)
lemma set_asid_pool_ekheap[wp]:
  "set_asid_pool p pool \<lbrace>\<lambda>s. P (ekheap s)\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp get_object_wp | simp)+
  done

lemma set_asid_pool_pas_refined[wp]:
  "\<lbrace>pas_refined aag and
    (\<lambda>s. \<forall>(x, y) \<in> graph_of pool.
           auth_graph_map (pasObjectAbs aag) {(p, Control, y)} \<subseteq> pasPolicy aag \<and>
           (\<forall>asid. asid_table s (asid_high_bits_of asid) = Some p \<and>
                   asid && mask asid_low_bits = ucast x
                   \<longrightarrow> (pasASIDAbs aag asid, Control, pasObjectAbs aag y) \<in> pasPolicy aag))\<rbrace>
         set_asid_pool p pool \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: auth_graph_map_def2 image_UN split_def)
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp tcb_domain_map_wellformed_lift | wps)+
(*
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp dest!: auth_graph_map_memD)
   apply (erule state_bits_to_policy.cases,
          auto intro: state_bits_to_policy.intros auth_graph_map_memI
               split: if_split_asm)[1]
  apply (auto intro: state_asids_to_policy_aux.intros
               simp: subsetD[OF _ state_asids_to_policy_aux.intros(2)]
              elim!: state_asids_to_policy_aux.cases
              split: if_split_asm)
*)
  oops
(* FIXME ryanb
  apply fastforce+
  done
*)

lemma pas_refined_clear_asid:
  "pas_refined aag s
   \<Longrightarrow> pas_refined aag (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := \<lambda>a. if a = asid then None
                                                                             else asid_table s a\<rparr>\<rparr>)"
  oops
(* FIXME ryanb
  by (fastforce simp: pas_refined_def state_objs_to_policy_def
               intro: state_asids_to_policy_aux.intros
               elim!: state_asids_to_policy_aux.cases
               split: if_split_asm)
*)

crunch integrity_autarch: set_asid_pool "integrity aag X st"
  (wp: crunch_wps)

end

end
