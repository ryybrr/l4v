(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchAccess
imports Types
begin

context Arch begin global_naming ARM_A

subsection \<open>Arch-specific transformation of caps into authorities\<close>

definition vspace_cap_rights_to_auth :: "cap_rights \<Rightarrow> auth set" where
  "vspace_cap_rights_to_auth r \<equiv>
     (if AllowWrite \<in> r then {Write} else {})
   \<union> (if AllowRead \<in> r then {Read} else {})"

definition arch_cap_auth_conferred where
  "arch_cap_auth_conferred arch_cap \<equiv>
     (if is_FrameCap arch_cap then vspace_cap_rights_to_auth (acap_rights arch_cap) else {Control})"

subsection \<open>Generating a policy from the current ASID distribution\<close>

(* FIXME AC: abbreviation for ptrFromPAddr *)
(* FIXME AC: rename *)
definition pte_ref2 where
  "pte_ref2 level pte \<equiv> case pte of
     PagePTE ppn atts rights
       \<Rightarrow> Some (ptrFromPAddr (addr_from_ppn ppn),
                pageBitsForSize (vmpage_size_of_level level),
                vspace_cap_rights_to_auth rights)
   | PageTablePTE ppn atts
       \<Rightarrow> Some (ptrFromPAddr (addr_from_ppn ppn), 0, {Control})
   | _ \<Rightarrow> None"

term kernel_mappings
definition vs_refs_aux :: "vm_level \<Rightarrow> arch_kernel_obj \<Rightarrow> (obj_ref \<times> obj_ref \<times> aa_type \<times> auth) set"
  where
  "vs_refs_aux level \<equiv> \<lambda>ko. case ko of
     ASIDPool pool \<Rightarrow> (\<lambda>(r,p). (p, ucast r, AASIDPool, Control)) ` graph_of pool
   | PageTable pt \<Rightarrow>
       \<Union>(r,(p, sz, auth)) \<in> graph_of (pte_ref2 level o pt) - {(x,y). x \<in> kernel_mapping_slots \<and> level = max_pt_level}.
         (\<lambda>(p, a). (p, ucast r, APageTable, a)) ` (ptr_range p sz \<times> auth)
   | _ \<Rightarrow> {}"

definition state_vrefs where
  "state_vrefs s \<equiv> \<lambda>p.
     \<Union>{vs_refs_aux lvl ao | lvl ao bot asid vref. vs_lookup_table bot asid vref s = Some (lvl, p)
                                                   \<and> aobjs_of s p = Some ao \<and> vref \<in> user_region}"

end

context Arch_p_arch_update_eq begin global_naming ARM_A

 interpretation Arch .

lemma state_vrefs[iff]: "state_vrefs (f s) = state_vrefs s"
  by (simp add: state_vrefs_def pspace)

end

context Arch begin global_naming ARM_A

lemmas state_vrefs_upd =
  cur_thread_update.state_vrefs
  cdt_update.state_vrefs
  irq_node_update_arch.state_vrefs
  interrupt_update.state_vrefs
  revokable_update.state_vrefs
  machine_state_update.state_vrefs
  more_update.state_vrefs

end

requalify_facts
  ARM_A.state_vrefs_upd

declare state_vrefs_upd[simp]

context Arch begin

primrec aobj_ref' where
  "aobj_ref' (ASIDPoolCap p as) = {p}"
| "aobj_ref' ASIDControlCap = {}"
| "aobj_ref' (FrameCap ref cR sz dev as) = ptr_range ref (pageBitsForSize sz)"
| "aobj_ref' (PageTableCap x as3) = {x}"

fun acap_asid' :: "arch_cap \<Rightarrow> asid set" where
  "acap_asid' (FrameCap _ _ _ _ mapping) = fst ` set_option mapping"
| "acap_asid' (PageTableCap _ mapping) = fst ` set_option mapping"
| "acap_asid' (ASIDPoolCap _ asid)
     = {x. asid_high_bits_of x = asid_high_bits_of asid \<and> x \<noteq> 0}"
| "acap_asid' ASIDControlCap = UNIV"

inductive_set state_asids_to_policy_aux for aag caps asid_tab vrefs where
  sata_asid:
    "\<lbrakk> caps ptr = Some (ArchObjectCap acap); asid \<in> acap_asid' acap \<rbrakk>
       \<Longrightarrow> (pasObjectAbs aag (fst ptr), Control, pasASIDAbs aag asid)
             \<in> state_asids_to_policy_aux aag caps asid_tab vrefs"
| sata_asid_lookup:
    "\<lbrakk> asid_tab (asid_high_bits_of asid) = Some poolptr;
       (pdptr, ucast (asid && mask asid_low_bits), AASIDPool, a) \<in> vrefs poolptr \<rbrakk>
       \<Longrightarrow> (pasASIDAbs aag asid, a, pasObjectAbs aag pdptr)
             \<in> state_asids_to_policy_aux aag caps asid_tab vrefs"
| sata_asidpool:
    "\<lbrakk> asid_tab (asid_high_bits_of asid) = Some poolptr; asid \<noteq> 0 \<rbrakk>
       \<Longrightarrow> (pasObjectAbs aag poolptr, AAuth ASIDPoolMapsASID, pasASIDAbs aag asid)
             \<in> state_asids_to_policy_aux aag caps asid_tab vrefs"

definition
  "state_asids_to_policy_arch aag caps astate vrefs \<equiv>
     state_asids_to_policy_aux aag caps (riscv_asid_table astate)
                               (vrefs :: 64 word \<Rightarrow> (64 word \<times> 64 word \<times> aa_type \<times> auth) set)"
declare state_asids_to_policy_arch_def[simp]

section \<open>Arch-specific integrity definition\<close>

subsection \<open>How ASIDs can change\<close>

abbreviation integrity_asids_aux ::
  "'a PAS \<Rightarrow> 'a set \<Rightarrow> asid \<Rightarrow> obj_ref option \<Rightarrow> obj_ref option \<Rightarrow> bool" where
  "integrity_asids_aux aag subjects asid pp_opt pp_opt' \<equiv>
     pp_opt = pp_opt' \<or> (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of asid
                                 \<longrightarrow> pasASIDAbs aag asid' \<in> subjects)"

definition integrity_asids ::
  "'a PAS \<Rightarrow> 'a set \<Rightarrow> asid \<Rightarrow> 'y::state_ext state \<Rightarrow> 'z:: state_ext state  \<Rightarrow> bool" where
  "integrity_asids aag subjects x s s' \<equiv>
   integrity_asids_aux aag subjects x (asid_table s  (asid_high_bits_of x))
                                      (asid_table s' (asid_high_bits_of x))"

declare integrity_asids_def[simp]

lemma integrity_asids_trans_state_l[simp]:
  "integrity_asids aag subjects x (trans_state f st) s =
   integrity_asids aag subjects x st s"
  by simp

lemma integrity_asids_trans_state_r[simp]:
  "integrity_asids aag subjects x st (trans_state f s) =
   integrity_asids aag subjects x st s"
  by simp

lemma integrity_asids_cur_thread_update_l[simp]:
  "integrity_asids aag subjects x (cur_thread_update f st) s =
   integrity_asids aag subjects x st s"
  by simp

lemma integrity_asids_cur_thread_update_r[simp]:
  "integrity_asids aag subjects x st (cur_thread_update f s) =
   integrity_asids aag subjects x st s"
  by simp

lemma integrity_asids_kheap_update_l[simp]:
  "integrity_asids aag subjects x (kheap_update f st) s =
   integrity_asids aag subjects x st s"
  by simp

lemma integrity_asids_kheap_update_r[simp]:
  "integrity_asids aag subjects x st (kheap_update f s) =
   integrity_asids aag subjects x st s"
  by simp

lemma integrity_asids_machine_state_update_l[simp]:
  "integrity_asids aag subjects x (machine_state_update f st) s =
   integrity_asids aag subjects x st s"
  by simp

lemma integrity_asids_machine_state_update_r[simp]:
  "integrity_asids aag subjects x st (machine_state_update f s) =
   integrity_asids aag subjects x st s"
  by simp

lemma integrity_asids_cdt_update_l[simp]:
  "integrity_asids aag subjects x (cdt_update f st) s =
   integrity_asids aag subjects x st s"
  by simp

lemma integrity_asids_cdt_update_r[simp]:
  "integrity_asids aag subjects x st (cdt_update f s) =
   integrity_asids aag subjects x st s"
  by simp

lemma integrity_asids_is_original_cap_update_l[simp]:
  "integrity_asids aag subjects x (is_original_cap_update f st) s =
   integrity_asids aag subjects x st s"
  by simp

lemma integrity_asids_is_original_cap_update_r[simp]:
  "integrity_asids aag subjects x st (is_original_cap_update f s) =
   integrity_asids aag subjects x st s"
  by simp

lemma integrity_asids_interrupt_states_update_l[simp]:
  "integrity_asids aag subjects x (interrupt_states_update f st) s =
   integrity_asids aag subjects x st s"
  by simp

lemma integrity_asids_interrupt_states_update_r[simp]:
  "integrity_asids aag subjects x st (interrupt_states_update f s) =
   integrity_asids aag subjects x st s"
  by simp

(* FIXME ryanb - is there a locale which could better handle this? *)
lemmas integrity_asids_updates =
  integrity_asids_trans_state_l
  integrity_asids_trans_state_r
  integrity_asids_cur_thread_update_l
  integrity_asids_cur_thread_update_r
  integrity_asids_kheap_update_l
  integrity_asids_kheap_update_r
  integrity_asids_machine_state_update_l
  integrity_asids_machine_state_update_r
  integrity_asids_cdt_update_l
  integrity_asids_cdt_update_r
  integrity_asids_is_original_cap_update_l
  integrity_asids_is_original_cap_update_r
  integrity_asids_interrupt_states_update_l
  integrity_asids_interrupt_states_update_r


(* FIXME ryanb *)
subsection \<open>Misc definitions\<close>

fun ctxt_IP_update where
  "ctxt_IP_update (UserContext ctxt) = UserContext (ctxt(NextIP := ctxt FaultIP))"

abbreviation arch_IP_update where
  "arch_IP_update arch \<equiv> arch_tcb_context_set (ctxt_IP_update (arch_tcb_context_get arch)) arch"

definition asid_pool_integrity ::
  "'a set \<Rightarrow> 'a PAS \<Rightarrow> (asid_low_index \<rightharpoonup> obj_ref) \<Rightarrow> (asid_low_index \<rightharpoonup> obj_ref) \<Rightarrow> bool" where
  "asid_pool_integrity subjects aag pool pool' \<equiv>
     \<forall>x. pool' x \<noteq> pool x
         \<longrightarrow> pool' x = None \<and> aag_subjects_have_auth_to subjects aag Control (the (pool x))"

inductive arch_integrity_obj_atomic ::
   "'a PAS \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> arch_kernel_obj \<Rightarrow> arch_kernel_obj \<Rightarrow> bool"
  for aag subjects l ao ao' where
  arch_troa_asidpool_clear:
    "\<lbrakk> ao = ASIDPool pool; ao' = ASIDPool pool';
       asid_pool_integrity subjects aag pool pool' \<rbrakk>
       \<Longrightarrow> arch_integrity_obj_atomic aag subjects l ao ao'"

inductive arch_integrity_obj_alt ::
   "'a PAS \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> arch_kernel_obj \<Rightarrow> arch_kernel_obj \<Rightarrow> bool"
  for aag subjects l' ao ao' where
  arch_tro_alt_asidpool_clear:
    "\<lbrakk> ao = ASIDPool pool; ao' = ASIDPool pool';
       asid_pool_integrity subjects aag pool pool'\<rbrakk>
       \<Longrightarrow> arch_integrity_obj_alt aag subjects l' ao ao'"

definition auth_ipc_buffers :: "'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> obj_ref set" where
  "auth_ipc_buffers s \<equiv> \<lambda>p. case (get_tcb p s) of
     None \<Rightarrow> {}
   | Some tcb \<Rightarrow>
     (case tcb_ipcframe tcb of
        ArchObjectCap (FrameCap p' R vms False _) \<Rightarrow>
          if AllowWrite \<in> R
          then (ptr_range (p' + (tcb_ipc_buffer tcb && mask (pageBitsForSize vms))) msg_align_bits)
          else {}
      | _ \<Rightarrow> {})"

end


context begin interpretation Arch .

requalify_consts
  aobj_ref'
  acap_asid'
  state_vrefs
  state_asids_to_policy_arch
  integrity_asids
  ctxt_IP_update
  arch_IP_update
  arch_cap_auth_conferred
  arch_integrity_obj_atomic
  arch_integrity_obj_alt
  auth_ipc_buffers

requalify_facts
  integrity_asids_updates

end

declare integrity_asids_updates[simp]

end
