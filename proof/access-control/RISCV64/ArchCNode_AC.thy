(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchCNode_AC
imports CNode_AC
begin

section\<open>Arch-specific CNode AC.\<close>

context Arch begin global_naming ARM_A

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


context Arch begin global_naming ARM_A

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


context Arch begin global_naming ARM_A

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


context Arch begin global_naming ARM_A

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


context Arch begin global_naming ARM_A

lemma pas_refined_arch_state_update_not_asids[simp]:
 "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s)
  \<Longrightarrow> pas_refined aag (arch_state_update f s) = pas_refined aag s"
  apply (auto simp add: pas_refined_def state_objs_to_policy_def)
  sorry

crunch cdt[wp]: store_pte "\<lambda>s. P (cdt s)"

lemma store_pte_state_refs[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def state_refs_of_def
                 elim!: rsubst[where P=P, OF _ ext])
  done

lemma all_rsubst:
  "\<lbrakk> \<forall>v. P (f v); \<exists>v. f v = r \<rbrakk> \<Longrightarrow> P r"
  by clarsimp

lemma store_pte_st_vrefs[wp]:
  "\<lbrace>\<lambda>s. \<forall>S. P ((state_vrefs s) (p && ~~ mask pt_bits :=
                                  (state_vrefs s (p && ~~ mask pt_bits) - S) \<union>
                                  (\<Union>(p', sz, auth)\<in>set_option (pte_ref2 level pte).
                                     (\<lambda>(p'', a). (p'', (p && mask pt_bits) >> 2, APageTable, a)) `
                                                                       (ptr_range p' sz \<times> auth))))\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  sorry
(* FIXME ryanb
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: state_vrefs_def vs_refs_aux_def obj_at_def)
  apply (simp add: fun_upd_def[symmetric] fun_upd_comp)
  apply (erule all_rsubst[where P=P])
  apply (subst fun_eq_iff, clarsimp simp: split_def)
  apply (cases "pte_ref2 level pte")
   apply (auto simp: ucast_ucast_mask shiftr_over_and_dist
                     word_bw_assocs mask_def pt_bits_def pageBits_def)
  done
*)

lemma store_pte_thread_states[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (thread_states s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_states_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm option.split)
  done

lemma store_pte_thread_bound_ntfns[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_bound_ntfns_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm option.split)
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

crunch asid_table_inv [wp]: store_pte "\<lambda>s. P (asid_table s)"

lemma store_pte_pas_refined[wp]:
  "\<lbrace>pas_refined aag and
    K (\<forall>x level. pte_ref2 level pte = Some x
           \<longrightarrow> (\<forall>a \<in> snd (snd x). \<forall>p' \<in> (ptr_range (fst x) (fst (snd x))).
                auth_graph_map (pasObjectAbs aag) {(p && ~~ mask pt_bits, a, p')} \<subseteq> pasPolicy aag))\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  sorry
(* FIXME ryanb
  apply (simp add: auth_graph_map_def2)
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp tcb_domain_map_wellformed_lift | wps)+
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp dest!: auth_graph_map_memD split del: if_split)
   apply (erule state_bits_to_policy.cases,
          auto intro: state_bits_to_policy.intros auth_graph_map_memI
               split: if_split_asm)[1]
  apply (erule_tac B="state_asids_to_policy_aux _ _ _ _" in subset_trans[rotated])
  apply (auto intro: state_asids_to_policy_aux.intros
              elim!: state_asids_to_policy_aux.cases
               elim: subset_trans[rotated]
              split: if_split_asm)
  done
*)

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
  sorry

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
  sorry
(* FIXME ryanb
  apply fastforce+
  done
*)

lemma pas_refined_clear_asid:
  "pas_refined aag s
   \<Longrightarrow> pas_refined aag (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := \<lambda>a. if a = asid then None
                                                                             else asid_table s a\<rparr>\<rparr>)"
  sorry
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
