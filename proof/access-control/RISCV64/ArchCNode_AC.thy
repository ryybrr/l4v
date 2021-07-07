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

lemma state_vrefs_eqI:
  "\<lbrakk> \<forall>bot_level asid vref level p.
       bot_level < level \<and> vs_lookup_table level asid vref s = Some (level, p)
       \<longrightarrow> (if level \<le> max_pt_level
            then pts_of s' p = pts_of s p
            else asid_pools_of s' p = asid_pools_of s p);
     aobjs_of s' = aobjs_of s; asid_table s' = asid_table s;
     pspace_aligned s; valid_vspace_objs s; valid_asid_table s \<rbrakk>
     \<Longrightarrow> state_vrefs (s' :: 'a :: state_ext state) = state_vrefs (s :: 'a :: state_ext state)"
  apply (rule ext)
  apply safe
   apply (subst (asm) state_vrefs_def, clarsimp)
   apply (fastforce intro: state_vrefsD elim: subst[OF vs_lookup_table_eqI,rotated -1])
  apply (subst (asm) state_vrefs_def, clarsimp)
  apply (rule state_vrefsD)
     apply (subst vs_lookup_table_eqI; fastforce)
    apply fastforce+
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

lemma state_vrefs_tcb_upd[CNode_AC_assms]:
  "\<lbrakk> pspace_aligned s; valid_vspace_objs s; valid_arch_state s; tcb_at t s \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>kheap := kheap s(t \<mapsto> TCB tcb)\<rparr>) = state_vrefs s"
  apply (rule state_vrefs_eqI)
  by (fastforce simp: opt_map_def obj_at_def is_obj_defs valid_arch_state_def)+

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

crunches set_untyped_cap_as_full
  for valid_arch_state[CNode_AC_assms, wp]: valid_arch_state

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

lemma vs_lookup_slot_level_of_slot:
  "\<lbrakk> vs_lookup_slot level asid vref s = Some (level, p);
     ptes_of s p = Some pte; level \<le> max_pt_level; vref \<in> user_region; invs s \<rbrakk>
     \<Longrightarrow> level_of_slot asid vref p s = level"
  apply (subst level_of_slot_def)
  apply (rule Greatest_equality)
   apply clarsimp
  apply (case_tac "y = asid_pool_level")
   apply (fastforce dest: vs_lookup_slot_no_asid)
  apply (fastforce dest: vs_lookup_slot_unique_level)
  done

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

lemma state_vrefs_store_NonPageTablePTE:
  "\<lbrakk> invs s; is_aligned p pte_bits; vs_lookup_slot level asid vref s = Some (level, p);
     vref \<in> user_region; \<not> is_PageTablePTE pte;
     kheap s (table_base p) = Some (ArchObj (PageTable pt)) \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>kheap := \<lambda>a. if a = table_base p
                                     then Some (ArchObj (PageTable (\<lambda>a. if a = table_index p
                                                                        then pte
                                                                        else pt a)))
                                     else kheap s a\<rparr>) =
         (\<lambda>x. if \<exists>level' vref'. vref_for_level vref' (level + 1) = vref_for_level vref (level + 1) \<and>
                                vref' \<in> user_region \<and> p = pt_slot_offset level (table_base p) vref' \<and>
                                pt_walk level level' (table_base p) vref' (ptes_of s) = Some (level',x)
              then (if x = table_base p
                    then vs_refs_aux level (PageTable (\<lambda>a. if a = table_index p then pte else pt a))
                    else {})
              else state_vrefs s x)"
  apply (rule all_ext)
  apply (case_tac "level = asid_pool_level")
   apply (fastforce simp: vs_lookup_slot_def vs_lookup_table_def
                          ptes_of_Some pts_of_Some aobjs_of_Some
                    dest: pool_for_asid_no_pte)
  apply (prop_tac "ptes_of s p \<noteq> None")
   apply (drule valid_vspace_objs_strong_slotD; clarsimp split del: if_split)
  apply (frule vs_lookup_slot_table_base; clarsimp split del: if_split)
  apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp split del: if_split)
  apply safe
   apply (subst (asm) state_vrefs_def opt_map_def)+
   apply (clarsimp split: option.splits split del: if_split)
   apply (subst (asm) vs_lookup_non_PageTablePTE[where s=s and s'="kheap_update _ s" and p=p])
          apply (fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some
                                 opt_map_def pte_of_def obind_def
                           dest: pte_ptr_eq)+
   apply (case_tac "x = table_base p"; clarsimp)
    apply (case_tac "lvl = asid_pool_level")
     apply (fastforce dest: vs_lookup_table_no_asid[OF vs_lookup_level]
                      simp: ptes_of_Some pts_of_Some aobjs_of_Some split: if_splits)
    apply (fastforce dest: vs_lookup_table_unique_level[OF vs_lookup_level]
                     elim: allE[where x=level] split: if_splits)
   apply (clarsimp split: if_splits)
    apply (case_tac "level' = asid_pool_level")
     apply (fastforce dest: vs_lookup_slot_no_asid simp: ptes_of_Some pts_of_Some aobjs_of_Some)
    apply (frule vs_lookup_slot_level_of_slot)
        apply (fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some split: option.splits)
       apply fastforce+
    apply (subst (asm) vs_lookup_slot_table_unfold; fastforce)
   apply (rule conjI; clarsimp)
    apply (case_tac "level' < level")
     apply (subst (asm) vs_lookup_vref_for_level_eq1, rule sym, assumption)
     apply (frule (2) vs_lookup_table_extend)
     apply (case_tac "lvl = asid_pool_level")
      apply (fastforce dest: vs_lookup_table_pt_at vs_lookup_asid_pool
                       simp: asid_pools_of_ko_at obj_at_def)
     apply (frule_tac level=lvl in vs_lookup_level)
     apply (drule (1) vs_lookup_table_unique_level, rule refl)
          apply fastforce+
     apply (frule bit0.plus_one_leq)
     apply (erule_tac x=level in allE)
     apply (subst (asm) vs_lookup_slot_vref_for_level[symmetric], assumption)
     apply (frule_tac bot_level=bot in vs_lookup_min_level)
     apply (fastforce simp: vs_lookup_slot_vref_for_level vs_lookup_slot_table_unfold)
    apply (subst (asm) pt_walk.simps, clarsimp)
   apply (fastforce simp: state_vrefs_def opt_map_def)
  apply (prop_tac "level_of_slot asid vref p s = level")
   apply (fastforce simp: vs_lookup_slot_table_unfold vs_lookup_slot_level_of_slot)
  apply (clarsimp split: if_splits)
   apply (rule state_vrefsD)
      apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte])
             apply (fastforce dest: pte_ptr_eq
                              simp: ptes_of_Some pts_of_Some aobjs_of_Some
                                    opt_map_def pte_of_def obind_def)+
  apply (case_tac "x = table_base p")
   apply (fastforce elim: allE[where x=level])
  apply (subst (asm) state_vrefs_def, clarsimp)
  apply (rule_tac level=lvl and asid=asida and vref=vrefa in state_vrefsD)
     apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte])
            apply (fastforce dest: pte_ptr_eq
                             simp: ptes_of_Some pts_of_Some aobjs_of_Some
                                   opt_map_def pte_of_def obind_def)+
     apply (clarsimp split: if_splits)
     apply (intro conjI; clarsimp)
      apply (case_tac "level' = asid_pool_level")
       apply (fastforce dest: vs_lookup_slot_no_asid simp: ptes_of_Some pts_of_Some aobjs_of_Some)
      apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
      apply (case_tac "lvl < level")
       apply (drule_tac bot_level=bot in vs_lookup_level)
       apply (subst (asm) vs_lookup_split_Some, erule dual_order.strict_implies_order)
        apply fastforce
       apply (drule (1) vs_lookup_table_unique_level; fastforce)
      apply (metis vs_lookup_slot_table vs_lookup_slot_unique_level)
     apply (fastforce dest: vs_lookup_level)
    apply (fastforce simp: aobjs_of_Some opt_map_def)
   apply clarsimp
  apply clarsimp
  done

definition level_of_table :: "obj_ref \<Rightarrow> 'z :: state_ext state \<Rightarrow> vm_level"
  where
  "level_of_table p s \<equiv>
     GREATEST lvl. \<exists>asid vref. vref \<in> user_region \<and> vs_lookup_table lvl asid vref s = Some (lvl, p)"

lemma level_of_table_vs_lookup_table:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p);
     ptes_of s p = Some pte; level \<le> max_pt_level; vref \<in> user_region; invs s \<rbrakk>
     \<Longrightarrow> level_of_table p s = level"
  apply (subst level_of_table_def)
  apply (rule Greatest_equality, fastforce)
  apply (case_tac "y = asid_pool_level")
   apply (fastforce dest: vs_lookup_table_no_asid)
  apply (fastforce dest: vs_lookup_table_unique_level)
  done

lemma state_vrefs_store_NonPageTablePTE':
  "\<lbrakk> invs s; is_aligned p pte_bits; \<not> is_PageTablePTE pte;
     kheap s (table_base p) = Some (ArchObj (PageTable pt));
     \<forall>level asid vref. vref \<in> user_region \<longrightarrow> vs_lookup_slot level asid vref s \<noteq> Some (level, p) \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>kheap := \<lambda>a. if a = table_base p
                                     then Some (ArchObj (PageTable (\<lambda>a. if a = table_index p
                                                                        then pte
                                                                        else pt a)))
                                     else kheap s a\<rparr>) =
         (\<lambda>x. if x = table_base p \<and> (\<exists>level. \<exists>\<rhd> (level, table_base p) s)
              then vs_refs_aux (level_of_table (table_base p) s) (PageTable (\<lambda>a. if a = table_index p
                                                                                 then pte
                                                                                 else pt a))
              else state_vrefs s x)"
  apply (rule all_ext)
  apply safe
   apply (subst (asm) state_vrefs_def opt_map_def)+
   apply (clarsimp split: option.splits split del: if_split)
   apply (clarsimp split: if_split_asm option.splits split del: if_split)
    apply (subst (asm) vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte])
           apply (fastforce dest: pte_ptr_eq
                            simp: ptes_of_Some pts_of_Some aobjs_of_Some
                                  opt_map_def pte_of_def obind_def)+
    apply (clarsimp split: if_splits)
    apply (drule vs_lookup_level)
    apply (rule conjI; clarsimp)
    apply (case_tac "level = asid_pool_level")
     apply (fastforce dest: vs_lookup_table_no_asid simp: ptes_of_Some pts_of_Some aobjs_of_Some)
    apply (case_tac "lvl = asid_pool_level")
     apply (fastforce dest: vs_lookup_table_no_asid simp: ptes_of_Some pts_of_Some aobjs_of_Some)
    apply (subst level_of_table_vs_lookup_table; fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some)
   apply (subst (asm) vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte])
          apply (fastforce dest: pte_ptr_eq
                           simp: ptes_of_Some pts_of_Some aobjs_of_Some
                                 opt_map_def pte_of_def obind_def)+
   apply (fastforce simp: state_vrefs_def aobjs_of_Some)
  apply (clarsimp split: if_splits)
   apply (case_tac "level = asid_pool_level")
    apply (fastforce dest: vs_lookup_table_no_asid simp: ptes_of_Some pts_of_Some aobjs_of_Some)
   apply (subst (asm) level_of_table_vs_lookup_table)
        apply (fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some)+
   apply (rule state_vrefsD)
      apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte ])
             apply ((fastforce dest: pte_ptr_eq
                               simp: ptes_of_Some pts_of_Some aobjs_of_Some
                                     opt_map_def pte_of_def obind_def)+)[7]
      apply auto[1]
     apply (fastforce simp: aobjs_of_Some opt_map_def)
    apply clarsimp
   apply clarsimp
  apply (case_tac "x = table_base p")
   apply (fastforce dest: vs_lookup_level simp: state_vrefs_def)
  apply (subst (asm) state_vrefs_def, clarsimp)
  apply (rule state_vrefsD)
     apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte ])
            apply ((fastforce dest: pte_ptr_eq
                              simp: ptes_of_Some pts_of_Some aobjs_of_Some
                                    opt_map_def pte_of_def obind_def)+)[7]
     apply auto[1]
    apply (fastforce simp: aobjs_of_Some opt_map_def split: option.splits)
   apply clarsimp
  apply clarsimp
  done

(* FIXME AC: make this less ugly *)
lemma state_vrefs_store_NonPageTablePTE_wp:
  "\<lbrace>\<lambda>s. invs s \<and> \<not> is_PageTablePTE pte \<and>
        (\<forall>pt. ako_at (PageTable pt) (table_base p) s \<and> is_aligned p pte_bits \<longrightarrow>
              (if \<exists>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<and> vref \<in> user_region
               then (\<exists>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<and> vref \<in> user_region \<and>
                                       P (\<lambda>x. (if \<exists>level' vref'. vref_for_level vref' (level + 1) = vref_for_level vref (level + 1) \<and>
                                                                 vref' \<in> user_region \<and> p = pt_slot_offset level (table_base p) vref' \<and>
                                                                 pt_walk level level' (table_base p) vref' (ptes_of s) = Some (level', x)
                                               then (if x = table_base p
                                                     then vs_refs_aux level (PageTable (\<lambda>a. if a = table_index p then pte else pt a))
                                                     else {})
                                               else state_vrefs s x)))
               else P (\<lambda>x. (if x = table_base p \<and> (\<exists>level. \<exists>\<rhd> (level, table_base p) s)
                            then vs_refs_aux (level_of_table (table_base p) s) (PageTable (\<lambda>a. if a = table_index p then pte else pt a))
                            else state_vrefs s x))))\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (case_tac "\<exists>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<and>
                                     vref \<in> user_region")
   apply (erule_tac x=pt in allE)
   apply (clarsimp simp: fun_upd_def)
   apply (subst state_vrefs_store_NonPageTablePTE)
         apply fastforce+
    apply (clarsimp simp: obj_at_def)
   apply (case_tac "level = asid_pool_level")
    apply (fastforce dest: vs_lookup_slot_no_asid
                     simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
   apply (case_tac "levela = asid_pool_level")
    apply (fastforce dest: vs_lookup_slot_no_asid
                     simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
   apply (drule (1) vs_lookup_slot_unique_level)
         apply fastforce+
   apply clarsimp
   apply (frule_tac level'="level+1" in vref_for_level_eq_mono)
    apply (fastforce intro: vm_level_less_le_1)
   apply clarsimp
  apply (erule_tac x=pt in allE)
  apply (clarsimp simp: fun_upd_def)
  apply (subst state_vrefs_store_NonPageTablePTE'; fastforce simp: obj_at_def)
  done

definition authorised_page_table_inv :: "'a PAS \<Rightarrow> page_table_invocation \<Rightarrow> bool" where
  "authorised_page_table_inv aag pti \<equiv>
   case pti of PageTableMap cap cslot_ptr pde obj_ref \<Rightarrow>
                 is_subject aag (fst cslot_ptr) \<and> is_subject aag (obj_ref && ~~ mask pt_bits) \<and>
                 pas_cap_cur_auth aag (ArchObjectCap cap)
             | PageTableUnmap cap cslot_ptr \<Rightarrow>
                 is_subject aag (fst cslot_ptr) \<and>
                 aag_cap_auth aag (pasSubject aag) (ArchObjectCap cap) \<and>
                 (\<forall>p asid vspace_ref. cap = PageTableCap p (Some (asid, vspace_ref))
                                      \<longrightarrow> is_subject_asid aag asid \<and>
                                          (\<forall>x \<in> set [p, p + 2 ^ pte_bits .e. p + 2 ^ pt_bits - 1].
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
  unfolding store_pte_def set_pt_def by (wpsimp wp: set_object_wp)

lemma mapM_x_store_pte_caps_of_state[wp]:
  "mapM_x (swp store_pte InvalidPTE) slots \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  by (wpsimp wp: mapM_x_wp')

lemma state_bits_to_policy_vrefs_subseteq:
  "\<And>cdt. \<lbrakk> x \<in> state_bits_to_policy caps ts tbn cdt vrefs; caps = caps';
           ts = ts'; tbn = tbn'; cdt = cdt'; \<forall>x. vrefs x \<subseteq> state_vrefs s x \<rbrakk>
           \<Longrightarrow> x \<in> state_bits_to_policy caps'  ts' tbn' cdt' (state_vrefs s)"
  apply (cases x; clarsimp)
  apply (erule state_bits_to_policy.cases; fastforce intro: state_bits_to_policy.intros)
  done

lemma state_asids_to_policy_vrefs_subseteq:
  "\<lbrakk> x \<in> state_asids_to_policy_aux aag caps asid_tab vrefs; caps = caps';
     \<forall>x. vrefs x \<subseteq> state_vrefs s x; \<forall>x y. asid_tab x = Some y \<longrightarrow> asid_table s x = Some y \<rbrakk>
     \<Longrightarrow> x \<in> state_asids_to_policy_aux aag caps' (asid_table s) (state_vrefs s)"
  apply (cases x; clarsimp)
  apply (erule state_asids_to_policy_aux.cases; fastforce intro: state_asids_to_policy_aux.intros)
  done

lemma store_pte_state_objs_in_policy:
  "\<lbrace>\<lambda>s. state_objs_in_policy aag s \<and> invs s \<and> table_base p \<notin> global_refs s \<and>
        ((\<exists>a. vspace_for_asid a s = Some (table_base p)) \<longrightarrow> table_index p \<notin> kernel_mapping_slots)\<rbrace>
   store_pte p InvalidPTE
   \<lbrace>\<lambda>_ s. state_objs_in_policy aag s\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (clarsimp simp: state_objs_to_policy_def pred_conj_def)
   apply wps
   apply (rule state_vrefs_store_NonPageTablePTE_wp)
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (intro exI conjI)
     apply assumption
    apply clarsimp
   apply (clarsimp simp: state_objs_to_policy_def)
   apply (erule subsetD)
   apply (clarsimp simp: auth_graph_map_def)
   apply (rule exI, rule conjI, rule refl)+
   apply (erule state_bits_to_policy_vrefs_subseteq; clarsimp)
   apply (case_tac "level = asid_pool_level")
    apply (fastforce dest: vs_lookup_slot_no_asid
                     simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
   apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
   apply (erule state_vrefsD)
     apply (fastforce simp: aobjs_of_Some obj_at_def)
    apply clarsimp
   apply (fastforce simp: vs_refs_aux_def graph_of_def pte_ref2_def split: if_splits)
  apply (clarsimp simp: state_objs_to_policy_def)
  apply (erule subsetD)
  apply (clarsimp simp: auth_graph_map_def)
  apply (rule exI, rule conjI, rule refl)+
  apply (erule state_bits_to_policy_vrefs_subseteq; clarsimp)
  apply (case_tac "level = asid_pool_level")
   apply (fastforce dest: vs_lookup_table_no_asid
                    simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
  apply (frule level_of_table_vs_lookup_table)
      apply (fastforce dest: vs_lookup_slot_no_asid
                       simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)+
  apply (erule state_vrefsD)
    apply (fastforce simp: aobjs_of_Some obj_at_def)
   apply clarsimp
  apply (fastforce simp: vs_refs_aux_def graph_of_def pte_ref2_def split: if_splits)
  done

lemma store_pte_state_asids_to_policy:
  "\<lbrace>\<lambda>s. state_asids_to_policy aag s \<subseteq> pasPolicy aag \<and> invs s \<and> table_base p \<notin> global_refs s \<and>
        ((\<exists>a. vspace_for_asid a s = Some (table_base p)) \<longrightarrow> table_index p \<notin> kernel_mapping_slots)\<rbrace>
   store_pte p InvalidPTE
   \<lbrace>\<lambda>_ s. state_asids_to_policy aag s \<subseteq> pasPolicy aag\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (clarsimp simp: state_objs_to_policy_def pred_conj_def)
   apply wps
   apply (rule state_vrefs_store_NonPageTablePTE_wp)
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (intro exI conjI)
     apply assumption
    apply clarsimp
   apply clarsimp
   apply (erule subsetD)
   apply (erule state_asids_to_policy_vrefs_subseteq; clarsimp)
   apply (case_tac "level = asid_pool_level")
    apply (fastforce dest: vs_lookup_slot_no_asid
                     simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
   apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
   apply (erule state_vrefsD)
     apply (fastforce simp: aobjs_of_Some obj_at_def)
    apply clarsimp
   apply (fastforce simp: vs_refs_aux_def graph_of_def pte_ref2_def split: if_splits)
  apply (erule subsetD)
  apply (erule state_asids_to_policy_vrefs_subseteq; clarsimp)
  apply (case_tac "level = asid_pool_level")
   apply (fastforce dest: vs_lookup_table_no_asid
                    simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
  apply (frule level_of_table_vs_lookup_table)
      apply (fastforce dest: vs_lookup_slot_no_asid
                       simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)+
  apply (erule state_vrefsD)
    apply (fastforce simp: aobjs_of_Some obj_at_def)
   apply clarsimp
  apply (fastforce simp: vs_refs_aux_def graph_of_def pte_ref2_def split: if_splits)
  done

lemma mapM_x_swp_store_pte_pas_refined:
  "\<lbrace>pas_refined aag and invs and
    (\<lambda>s. \<forall>x \<in> set slots. table_base x \<notin> global_refs s \<and>
                         (\<forall>asid. vspace_for_asid asid s \<noteq> Some (table_base x)))\<rbrace>
   mapM_x (swp store_pte InvalidPTE) slots
   \<lbrace>\<lambda>_ s. pas_refined aag s\<rbrace>"
  supply state_asids_to_policy_arch_def[simp del]
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp[where S="set slots"])
    apply (simp add: pas_refined_def)
    apply (wpsimp wp: store_pte_state_objs_in_policy store_pte_state_asids_to_policy
                      store_pte_invs hoare_vcg_const_Ball_lift hoare_vcg_all_lift)
    apply (auto simp: wellformed_pte_def)
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
  "\<lbrace>\<lambda>s. invs s \<and> pte = InvalidPTE \<and> table_base p \<notin> global_refs s
               \<and> (\<forall>asid. vspace_for_asid asid s \<noteq> Some (table_base p))\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp wp: store_pte_invs simp: wellformed_pte_def)

lemma FIXME_wordAND_wordNOT_mask_plus:
   "x && ~~mask n = x \<Longrightarrow> (x + mask n) && ~~mask n = x"
  by (metis AND_NOT_mask_plus_AND_mask_eq VSpaceEntries_AI.neg_mask_add_mask add_right_imp_eq word_bw_same(1))

lemma store_pte_pas_refined:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> invs s \<and> table_base p \<notin> global_refs s \<and>
        (\<exists>slot ref. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base p) ref))) \<and>
        ((\<exists>asid. vspace_for_asid asid s = Some (table_base p)) \<longrightarrow> table_index p \<notin> kernel_mapping_slots)\<rbrace>
   store_pte p InvalidPTE
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  supply state_asids_to_policy_arch_def[simp del]
  apply (clarsimp simp: pas_refined_def)
  apply (wpsimp wp: store_pte_state_objs_in_policy store_pte_state_asids_to_policy)
  done

lemma unmap_page_table_pas_refined:
 "\<lbrace>pas_refined aag and invs and K (vaddr \<in> user_region)\<rbrace>
  unmap_page_table asid vaddr pt
  \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding unmap_page_table_def
  apply (rule hoare_gen_asm)
  apply (wpsimp wp: set_cap_pas_refined get_cap_wp pt_lookup_from_level_wrp store_pte_invs_unmap
                    store_pte_pas_refined hoare_vcg_imp_lift' hoare_vcg_ball_lift hoare_vcg_all_lift)
  apply (rule_tac x=asid in exI)
  apply clarsimp
  apply (case_tac "level = asid_pool_level")
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

crunches unmap_page_table
  for cdt[wp]: "\<lambda>s. P (cdt s)"

lemma perform_pt_inv_unmap_pas_refined:
 "\<lbrace>pas_refined aag and invs and valid_pti (PageTableUnmap cap ct_slot)
                            and K (authorised_page_table_inv aag (PageTableUnmap cap ct_slot))\<rbrace>
  perform_pt_inv_unmap cap ct_slot
  \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pt_inv_unmap_def
  apply (wpsimp wp: set_cap_pas_refined get_cap_wp)
       apply (strengthen invs_psp_aligned invs_vspace_objs invs_arch_state)
       apply wps
       apply (rule hoare_vcg_all_lift[OF hoare_vcg_imp_lift'[OF mapM_x_wp_inv]], wpsimp wp: mapM_x_wp_inv)
       apply (rule hoare_vcg_conj_lift[OF hoare_strengthen_post[OF mapM_x_swp_store_pte_pas_refined]], assumption)
       apply (rule hoare_vcg_conj_lift[OF hoare_strengthen_post[OF mapM_x_swp_store_pte_invs_unmap]], assumption)
       apply (wpsimp wp: pt_lookup_from_level_wrp store_pte_invs_unmap store_pte_pas_refined
                         mapM_x_wp_inv unmap_page_table_pas_refined
                         hoare_vcg_imp_lift' hoare_vcg_ball_lift hoare_vcg_all_lift)+
  apply (rule conjI)
   apply (fastforce simp: is_PageTableCap_def authorised_page_table_inv_def
                          valid_pti_def update_map_data_def cte_wp_at_caps_of_state)
  apply (clarsimp simp: is_PageTableCap_def authorised_page_table_inv_def valid_arch_cap_def
                        valid_pti_def cte_wp_at_caps_of_state update_map_data_def aag_cap_auth_def
                        cap_auth_conferred_def arch_cap_auth_conferred_def wellformed_mapdata_def
                        cap_links_asid_slot_def cap_links_irq_def is_transferable.simps)
  apply (prop_tac "table_base x = acap_obj cap")
   apply (drule (1) caps_of_state_aligned_page_table)
   apply (simp only: is_aligned_neg_mask_eq')
   apply (clarsimp simp: add_mask_fold)
   apply (drule subsetD[OF upto_enum_step_subset], clarsimp)
   apply (drule neg_mask_mono_le[where n=pt_bits])
   apply (drule neg_mask_mono_le[where n=pt_bits])
   apply (fastforce dest: FIXME_wordAND_wordNOT_mask_plus)
  apply (rule conjI; clarsimp)
   apply (fastforce simp: cte_wp_at_caps_of_state cap_range_def
                    dest: invs_valid_global_refs valid_global_refsD)
  apply (frule vspace_for_asid_target)
  apply (drule valid_vs_lookupD; clarsimp)
  apply (drule (1) unique_table_refsD[rotated]; clarsimp)
  apply (drule (1) cap_to_pt_is_pt_cap)
    apply (clarsimp simp: in_omonad obj_at_def)
   apply (fastforce intro: valid_objs_caps)
  apply (clarsimp simp: is_cap_simps)
  done

lemma vs_lookup_PageTablePTE:
  "\<lbrakk> vs_lookup_table level asid vref s' = Some (lvl', pt);
     pspace_aligned s; valid_vspace_objs s; valid_asid_table s;
     invalid_pte_at p s; ptes_of s' = ptes_of s (p \<mapsto> pte); is_PageTablePTE pte;
     asid_pools_of s' = asid_pools_of s; asid_table s' = asid_table s;
     vref \<in> user_region;
     pts_of s (the (pte_ref pte)) = Some empty_pt; pt \<noteq> pptr_from_pte pte \<rbrakk>
     \<Longrightarrow> \<exists>level' \<ge> level. vs_lookup_table level' asid vref s = Some (lvl', pt)"
  apply (induct level arbitrary: lvl' pt rule: bit0.from_top_full_induct[where y=max_pt_level])
   apply (fastforce simp: geq_max_pt_level vs_lookup_table_def pool_for_asid_def obind_def)
  apply (rule_tac x=lvl' in exI)
  apply (frule vs_lookup_min_level, clarsimp)
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
  "\<lbrakk> vs_lookup_table level asid vref s = Some (lvl', pt);
     pspace_aligned s; valid_vspace_objs s; valid_asid_table s;
     invalid_pte_at p s; ptes_of s' = ptes_of s (p \<mapsto> pte); is_PageTablePTE pte;
     asid_pools_of s' = asid_pools_of s; asid_table s' = asid_table s; vref \<in> user_region  \<rbrakk>
     \<Longrightarrow> \<exists>level' \<ge> level. vs_lookup_table level' asid vref s' = Some (lvl', pt)"
  apply (induct level arbitrary: lvl' pt rule: bit0.from_top_full_induct[where y=max_pt_level])
   apply (fastforce simp: geq_max_pt_level vs_lookup_table_def pool_for_asid_def obind_def)
  apply (rule_tac x=lvl' in exI)
  apply (frule vs_lookup_min_level, clarsimp)
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

lemma state_vrefs_store_PageTablePTE:
  assumes "invs s"
  and "is_aligned p pte_bits"
  and "vs_lookup_slot level asid vref s = Some (level, p)"
  and "vref \<in> user_region"
  and "is_PageTablePTE pte"
  and "invalid_pte_at p s"
  and "pts_of s (the (pte_ref pte)) = Some empty_pt"
  and "the (pte_ref pte) \<noteq> table_base p"
  and "kheap s (table_base p) = Some (ArchObj (PageTable pt))"
  shows "state_vrefs (s\<lparr>kheap := \<lambda>a. if a = table_base p
                                     then Some (ArchObj (PageTable (\<lambda>a. if a = table_index p
                                                                        then pte
                                                                        else pt a)))
                                     else kheap s a\<rparr>) =
         (\<lambda>x. if x = table_base p
              then vs_refs_aux level (PageTable (\<lambda>a. if a = table_index p then pte else pt a))
              else state_vrefs s x)"
  (is "state_vrefs ?s' = _")
  using assms
  apply -
  apply (rule all_ext)
  apply (case_tac "level = asid_pool_level")
   apply (fastforce simp: vs_lookup_slot_def vs_lookup_table_def
                          ptes_of_Some pts_of_Some aobjs_of_Some
                    dest: pool_for_asid_no_pte split: if_splits)
  apply safe
   apply (clarsimp simp: state_vrefs_def opt_map_def split: option.splits)
   apply (case_tac "x = pptr_from_pte pte")
    apply (clarsimp simp: pte_ref_def2 split: if_splits)
    apply (fastforce simp: vs_refs_aux_def graph_of_def pte_ref2_def)
   apply (drule_tac s=s and pte=pte and p=p in vs_lookup_PageTablePTE)
              apply (fastforce simp: pts_of_Some aobjs_of_Some opt_map_def pte_of_def obind_def
                               dest: pte_ptr_eq)+
   apply clarsimp
   apply (drule vs_lookup_level)
   apply (case_tac "lvl = asid_pool_level")
    apply (fastforce dest: vs_lookup_asid_pool  simp: asid_pools_of_ko_at obj_at_def)
   apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
   apply (fastforce dest: vs_lookup_table_unique_level split: if_splits)
  apply (clarsimp simp: state_vrefs_def opt_map_def)
  apply (frule vs_lookup_slot_table_base)
     apply clarsimp+
  apply (case_tac "x = table_base p"; clarsimp)
   apply (drule_tac pte=pte and s'="?s'" in vs_lookup_PageTablePTE';
          fastforce dest: pte_ptr_eq simp: pts_of_Some aobjs_of_Some opt_map_def pte_of_def obind_def)
  apply (drule_tac level=bot and pte=pte and s'="?s'" in vs_lookup_PageTablePTE';
         fastforce dest: pte_ptr_eq simp: pts_of_Some aobjs_of_Some opt_map_def pte_of_def obind_def)
  done

lemma state_vrefs_store_PageTablePTE_wp:
  "\<lbrace>\<lambda>s. invs s \<and> is_PageTablePTE pte \<and> invalid_pte_at p s \<and>
        pts_of s (the (pte_ref pte)) = Some empty_pt \<and> the (pte_ref pte) \<noteq> table_base p \<and>
        (\<exists>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<and> vref \<in> user_region \<and>
                           (\<forall>pt. ako_at (PageTable pt) (table_base p) s \<longrightarrow>
                                 P (\<lambda>x. if x = table_base p
                                        then vs_refs_aux level (PageTable (\<lambda>a. if a = table_index p
                                                                               then pte
                                                                               else pt a))
                                        else state_vrefs s x)))\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (fastforce simp: fun_upd_def obj_at_def state_vrefs_store_PageTablePTE)
  done

lemma perform_pt_inv_map_pas_refined[wp]:
  "\<lbrace>pas_refined aag and invs and valid_pti (PageTableMap acap (a, b) pte p)
                    and K (authorised_page_table_inv aag (PageTableMap acap (a, b) pte p))\<rbrace>
   perform_pt_inv_map acap (a,b) pte p
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pt_inv_map_def
  apply (rule hoare_gen_asm)
  apply (wpsimp simp: pas_refined_def state_objs_to_policy_def)
    apply (wps | wpsimp wp: state_vrefs_store_PageTablePTE_wp arch_update_cap_invs_map
                            vs_lookup_slot_lift set_cap_arch_obj_neg set_cap_state_vrefs
                            hoare_vcg_ex_lift hoare_vcg_all_lift hoare_vcg_imp_lift')+
  apply (clarsimp simp: invs_psp_aligned invs_vspace_objs invs_arch_state
                        valid_pti_def cte_wp_at_cte_at)
  apply (case_tac acap; clarsimp)
  apply (intro conjI; (solves \<open>simp add: pas_refined_def\<close>)?)
     apply (fastforce simp: cte_wp_at_caps_of_state vs_cap_ref_def
                            is_arch_update_def cap_master_cap_def
                     split: arch_cap.splits)
    apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply (fastforce dest: caps_of_state_valid
                    simp: vs_cap_ref_def is_arch_update_def cap_master_cap_def
                          valid_cap_def cap_aligned_def valid_arch_cap_def
                   split: cap.splits arch_cap.splits)
   apply (clarsimp simp: vs_lookup_slot_def split: if_splits)
    apply (fastforce dest: pool_for_asid_no_pte simp: vs_lookup_table_def invalid_pte_at_def)
   apply (frule (2) vs_lookup_table_is_aligned; clarsimp)
   apply (drule (1) vs_lookup_table_target)
   apply (drule valid_vs_lookupD, erule vref_for_level_user_region; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap, simp, fastforce intro: valid_objs_caps)
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (clarsimp simp: is_cap_simps is_arch_update_def cap_master_cap_def
                  split: cap.splits arch_cap.splits)
   apply (drule (1) unique_table_refsD[rotated]; fastforce simp: table_cap_ref_def)
  apply (intro exI conjI; (simp | clarsimp))
  apply (intro conjI)
    apply (clarsimp simp: pas_refined_def cte_wp_at_caps_of_state auth_graph_map_def)
    apply (erule state_bits_to_policy.cases)
          apply (clarsimp simp: is_arch_update_def cap_master_cap_def state_objs_to_policy_def
                         split: if_splits cap.splits arch_cap.splits option.splits;
                 fastforce dest: sbta_caps simp: cap_auth_conferred_def arch_cap_auth_conferred_def)
         apply (fastforce dest: sbta_untyped simp: state_objs_to_policy_def split: if_splits)
        apply (fastforce dest: sbta_ts simp: state_objs_to_policy_def)
       apply (fastforce dest: sbta_bounds simp: state_objs_to_policy_def)
      apply (clarsimp simp: state_objs_to_policy_def is_arch_update_def cap_master_cap_def)
      apply (drule_tac caps="caps_of_state s" in sbta_cdt; fastforce elim: is_transferable.cases
                                                                    split: if_splits)
     apply (fastforce dest: sbta_cdt_transferable simp: state_objs_to_policy_def)
    apply (clarsimp split: if_splits)
     apply (clarsimp simp: authorised_page_table_inv_def vs_refs_aux_def split: arch_kernel_obj.splits)
     apply (erule swap)
     apply (clarsimp simp: graph_of_def pte_ref2_def split: if_split_asm)
      apply (cases pte; clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def)
     apply (erule subsetD)
     apply (clarsimp simp: auth_graph_map_def state_objs_to_policy_def)
     apply (rule_tac x="table_base p" in exI, rule conjI, erule sym)
     apply (rule exI, rule conjI, rule refl)
     apply (rule sbta_vref)
     apply (case_tac "level = asid_pool_level")
      apply (fastforce dest: pool_for_asid_no_pte
                       simp: vs_lookup_slot_def vs_lookup_table_def invalid_pte_at_def)
     apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
     apply (erule state_vrefsD)
       apply (fastforce simp: aobjs_of_Some obj_at_def)
      apply clarsimp
     apply (fastforce simp: vs_refs_aux_def graph_of_def pte_ref2_def)
    apply (clarsimp simp: is_arch_update_def cap_master_cap_def
                   split: cap.splits arch_cap.splits option.splits)
    apply (fastforce dest: sbta_vref simp: pas_refined_def auth_graph_map_def state_objs_to_policy_def)
   apply (clarsimp simp: pas_refined_def)
   apply (erule state_asids_to_policy_aux.cases)
     apply (clarsimp simp: cte_wp_at_caps_of_state split: if_splits)
      apply (clarsimp simp: authorised_page_table_inv_def aag_cap_auth_def
                            cap_auth_conferred_def arch_cap_auth_conferred_def
                            cap_links_asid_slot_def label_owns_asid_slot_def)
     apply (fastforce dest: sata_asid)
    apply (clarsimp split: if_splits)
     apply (fastforce dest!: state_asids_to_policy_aux.intros simp: vs_refs_aux_def)
    apply (fastforce dest!: sata_asid_lookup)
   apply (fastforce dest!: sata_asidpool)
  apply (clarsimp simp: pas_refined_def)
  apply (erule state_irqs_to_policy_aux.cases)
  apply (clarsimp split: if_splits)
  apply (fastforce dest: sita_controlled)
  done

lemma perform_page_table_invocation_pas_refined:
  "\<lbrace>pas_refined aag and invs and valid_pti iv and K (authorised_page_table_inv aag iv)\<rbrace>
   perform_page_table_invocation iv
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
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

crunch integrity_autarch: set_asid_pool "integrity aag X st"
  (wp: crunch_wps)

end

end
