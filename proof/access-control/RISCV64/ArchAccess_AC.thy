(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchAccess_AC
imports Access_AC
begin

section\<open>Arch-specific AC proofs\<close>

context Arch begin global_naming ARM_A

named_theorems Access_AC_assms

lemma acap_class_reply[Access_AC_assms]:
  "acap_class acap \<noteq> ReplyClass t"
  by (cases acap; simp)

lemma arch_troa_tro_alt[Access_AC_assms, elim!]:
  "arch_integrity_obj_atomic aag subjects l ko ko'
   \<Longrightarrow> arch_integrity_obj_alt aag subjects l ko ko'"
  by (fastforce elim: arch_integrity_obj_atomic.cases intro: arch_integrity_obj_alt.intros)

lemma clear_asidpool_trans[elim]:
  "\<lbrakk> asid_pool_integrity subjects aag pool pool';
     asid_pool_integrity subjects aag pool' pool'' \<rbrakk>
     \<Longrightarrow> asid_pool_integrity subjects aag pool pool''"
  unfolding asid_pool_integrity_def by metis

lemma cap_asid'_member[simp]:
  "asid \<in> cap_asid' cap = (\<exists>acap. cap = ArchObjectCap acap \<and> asid \<in> acap_asid' acap)"
  by (cases cap; clarsimp)

lemma clas_caps_of_state[Access_AC_assms]:
  "\<lbrakk> caps_of_state s slot = Some cap; pas_refined aag s \<rbrakk>
     \<Longrightarrow> cap_links_asid_slot aag (pasObjectAbs aag (fst slot)) cap"
  apply (clarsimp simp: cap_links_asid_slot_def label_owns_asid_slot_def pas_refined_def)
  apply (drule state_asids_to_policy_aux.intros)
   apply assumption
  apply (blast dest: state_asids_to_policy_aux.intros)
  done

lemma arch_tro_alt_trans_spec[Access_AC_assms]:
  "\<lbrakk> arch_integrity_obj_alt aag subjects l ko ko';
     arch_integrity_obj_alt aag subjects l ko' ko'' \<rbrakk>
     \<Longrightarrow> arch_integrity_obj_alt aag subjects l ko ko''"
  by (fastforce simp: arch_integrity_obj_alt.simps)

lemma integrity_asids_update_autarch[Access_AC_assms]:
  "\<lbrakk> integrity_asids aag subjects x st s; is_subject aag ptr \<rbrakk>
     \<Longrightarrow> integrity_asids aag subjects x st (s\<lparr>kheap := kheap s(ptr \<mapsto> obj)\<rparr>)"
  by simp

(*
lemma vs_lookup_table_tcb_upd:
   "\<lbrakk> pspace_aligned s; valid_vspace_objs s; valid_asid_table s; tcb_at t s \<rbrakk>
      \<Longrightarrow> vs_lookup_table bt asid vref (s\<lparr>kheap := kheap s(t \<mapsto> TCB tcb)\<rparr>) =
           vs_lookup_table bt asid vref s"
  apply (rule vs_lookup_table_eqI)
  apply (auto simp: tcb_at_def get_tcb_def opt_map_def
             split: option.splits kernel_object.splits)
  done

(* FIXME ryanb: better name than bot *)
lemma state_vrefs_tcb_upd:
  "\<lbrakk> pspace_aligned s; valid_vspace_objs s; valid_asid_table s; kheap s t = Some (TCB tcb') \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>kheap := kheap s(t \<mapsto> TCB tcb)\<rparr>) = state_vrefs s"
  apply (rule ext)
  sorry

lemma "tcb_at t s \<Longrightarrow>
       vs_lookup_table btm asid vref (s\<lparr>kheap := kheap s(t \<mapsto> TCB tcb)\<rparr>) =
       vs_lookup_table btm asid vref s"
apply (rule vs_lookup_table_unreachable_upd_idem)
apply (clarsimp simp: vs_lookup_table_def)

lemma as_user_state_vrefs[Access_AC_assms, wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_asid_table and (\<lambda>s. P (state_vrefs s))\<rbrace>
   as_user t f
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  apply (simp add: as_user_def)
  apply (wpsimp wp: set_object_wp)
  apply (subst state_vrefs_tcb_upd)
      apply (auto simp: obj_at_def get_tcb_def split: option.splits kernel_object.splits)
  done
*)

end


global_interpretation Access_AC_1?: Access_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact Access_AC_assms)
qed


context Arch begin global_naming ARM_A

lemma auth_ipc_buffers_tro[Access_AC_assms]:
  "\<lbrakk> integrity_obj_state aag activate subjects s s';
     x \<in> auth_ipc_buffers s' p; pasObjectAbs aag p \<notin> subjects \<rbrakk>
     \<Longrightarrow> x \<in> auth_ipc_buffers s p "
  by (drule_tac x = p in spec)
     (erule integrity_objE;
      fastforce simp: tcb_states_of_state_def get_tcb_def auth_ipc_buffers_def
               split: cap.split_asm arch_cap.split_asm if_split_asm bool.splits)

lemma trasids_trans[Access_AC_assms]:
  "\<lbrakk> (\<forall>x. integrity_asids aag subjects x s s');
     (\<forall>x. integrity_asids aag subjects x  s' s'') \<rbrakk>
     \<Longrightarrow> (\<forall>x. integrity_asids aag subjects x s s'')"
  apply clarsimp
  apply (drule_tac x=x in spec)+
  apply fastforce
  done

lemma integrity_asids_refl[Access_AC_assms, simp]:
  "integrity_asids aag subjects x s s"
  by simp

end


global_interpretation Access_AC_2?: Access_AC_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact Access_AC_assms)
qed


context Arch begin global_naming ARM_A

lemma ipcframe_subset_page:
  "\<lbrakk> valid_objs s; get_tcb p s = Some tcb;
     tcb_ipcframe tcb = ArchObjectCap (FrameCap p' R vms d xx);
     x \<in> ptr_range (p' + (tcb_ipc_buffer tcb && mask (pageBitsForSize vms))) msg_align_bits \<rbrakk>
     \<Longrightarrow> x \<in> ptr_range p' (pageBitsForSize vms)"
   apply (frule (1) valid_tcb_objs)
   apply (clarsimp simp add: valid_tcb_def ran_tcb_cap_cases)
   apply (erule set_mp[rotated])
   apply (rule ptr_range_subset)
     apply (simp add: valid_cap_def cap_aligned_def)
    apply (simp add: valid_tcb_def valid_ipc_buffer_cap_def is_aligned_andI1 split:bool.splits)
   apply (rule order_trans [OF _ pbfs_atleast_pageBits])
   apply (simp add: msg_align_bits pageBits_def)
  apply (rule and_mask_less')
  apply (simp add: pbfs_less_wb' [unfolded word_bits_conv])
  done

lemma auth_ipc_buffers_member_def:
  "x \<in> auth_ipc_buffers s p =
   (\<exists>tcb p' R vms xx. get_tcb p s = Some tcb
                   \<and> tcb_ipcframe tcb = (ArchObjectCap (FrameCap p' R vms False xx))
                   \<and> caps_of_state s (p, tcb_cnode_index 4) =
                      Some (ArchObjectCap (FrameCap p' R vms False xx))
                   \<and> AllowWrite \<in> R
                   \<and> x \<in> ptr_range (p' + (tcb_ipc_buffer tcb && mask (pageBitsForSize vms)))
                                    msg_align_bits)"
  unfolding auth_ipc_buffers_def
  by (clarsimp simp: caps_of_state_tcb' split: option.splits cap.splits arch_cap.splits bool.splits)

lemma auth_ipc_buffers_member[Access_AC_assms]:
  "\<lbrakk> x \<in> auth_ipc_buffers s p; valid_objs s \<rbrakk>
     \<Longrightarrow> \<exists>tcb acap. get_tcb p s = Some tcb
                  \<and> tcb_ipcframe tcb = (ArchObjectCap acap)
                  \<and> caps_of_state s (p, tcb_cnode_index 4) = Some (ArchObjectCap acap)
                  \<and> Write \<in> arch_cap_auth_conferred acap
                  \<and> x \<in> aobj_ref' acap"
  by (fastforce simp: auth_ipc_buffers_def caps_of_state_tcb' arch_cap_auth_conferred_def
                      vspace_cap_rights_to_auth_def ipcframe_subset_page
               split: option.splits cap.splits arch_cap.splits bool.splits if_splits)

lemma asid_pool_integrity_mono[Access_AC_assms]:
  "\<lbrakk> asid_pool_integrity S aag cont cont'; S \<subseteq> T \<rbrakk> \<Longrightarrow> asid_pool_integrity T aag cont cont'"
  unfolding asid_pool_integrity_def by fastforce

lemma integrity_asids_mono[Access_AC_assms]:
    "\<lbrakk> integrity_asids aag S x s s'; S \<subseteq> T; pas_refined aag s; valid_objs s \<rbrakk>
       \<Longrightarrow> integrity_asids aag T x s s'"
  by fastforce

lemma arch_integrity_obj_atomic_mono[Access_AC_assms]:
  "\<lbrakk> arch_integrity_obj_atomic aag S l ao ao'; S \<subseteq> T; pas_refined aag s; valid_objs s \<rbrakk>
     \<Longrightarrow> arch_integrity_obj_atomic aag T l ao ao'"
  by (clarsimp simp: arch_integrity_obj_atomic.simps asid_pool_integrity_mono)

end


global_interpretation Access_AC_3?: Access_AC_3
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact Access_AC_assms)
qed


context Arch begin global_naming ARM_A

lemma pas_refined_irq_state_independent[intro!, simp]:
  "pas_refined x (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>) =
   pas_refined x s"
  by (simp add: pas_refined_def)

end

end