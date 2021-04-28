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
     (if is_page_cap arch_cap then vspace_cap_rights_to_auth (acap_rights arch_cap) else {Control})"

subsection \<open>Generating a policy from the current ASID distribution\<close>

definition pte_ref where
  "pte_ref pte \<equiv> case pte of
     SmallPagePTE addr atts rights
       \<Rightarrow> Some (ptrFromPAddr addr, pageBitsForSize ARMSmallPage, vspace_cap_rights_to_auth rights)
   | LargePagePTE addr atts rights
       \<Rightarrow> Some (ptrFromPAddr addr, pageBitsForSize ARMLargePage, vspace_cap_rights_to_auth rights)
   | _ \<Rightarrow> None"

definition pde_ref2 where
  "pde_ref2 pde \<equiv> case pde of
     SectionPDE addr atts domain rights
       \<Rightarrow> Some (ptrFromPAddr addr, pageBitsForSize ARMSection, vspace_cap_rights_to_auth rights)
   | SuperSectionPDE addr atts rights
       \<Rightarrow> Some (ptrFromPAddr addr, pageBitsForSize ARMSuperSection, vspace_cap_rights_to_auth rights)
   | PageTablePDE addr atts domain
       \<comment> \<open>The 0 is a hack, saying that we own only addr, although 12 would also be OK\<close>
       \<Rightarrow> Some (ptrFromPAddr addr, 0, {Control})
   | _ \<Rightarrow> None"

\<comment> \<open>We exclude the global page tables from the authority graph. Alternatively, we could include them
    and add a wellformedness constraint to policies that requires that every label has the necessary
    authority to whichever label owns the global page tables, so that when a new page directory is
    created and references to the global page tables are added to it, no new authority is gained.
    Note: excluding the references to global page tables in this way brings in some ARM
          arch-specific VM knowledge here\<close>
definition vs_refs_no_global_pts :: "kernel_object \<Rightarrow> (obj_ref \<times> obj_ref \<times> aa_type \<times> auth) set"
  where
  "vs_refs_no_global_pts \<equiv> \<lambda>ko. case ko of
     ArchObj (ASIDPool pool) \<Rightarrow> (\<lambda>(r,p). (p, ucast r, AASIDPool, Control)) ` graph_of pool
   | ArchObj (PageDirectory pd) \<Rightarrow>
       \<Union>(r,(p, sz, auth)) \<in> graph_of (pde_ref2 o pd) - {(x,y). (ucast (kernel_base >> 20) \<le> x)}.
         (\<lambda>(p, a). (p, ucast r, APageDirectory, a)) ` (ptr_range p sz \<times> auth)
   | ArchObj (PageTable pt) \<Rightarrow>
       \<Union>(r,(p, sz, auth)) \<in> graph_of (pte_ref o pt).
         (\<lambda>(p, a). (p, ucast r, APageTable, a)) ` (ptr_range p sz \<times> auth)
   | _ \<Rightarrow> {}"

definition state_vrefs where
  "state_vrefs s = case_option {} vs_refs_no_global_pts o kheap s"

end


context pspace_update_eq begin interpretation Arch .

lemma state_vrefs[iff]: "state_vrefs (f s) = state_vrefs s"
  by (simp add: state_vrefs_def pspace)

end


context Arch begin

primrec aobj_ref' where
  "aobj_ref' (ASIDPoolCap p as) = {p}"
| "aobj_ref' ASIDControlCap = {}"
| "aobj_ref' (PageCap isdev x rs sz as4) = ptr_range x (pageBitsForSize sz)"
| "aobj_ref' (PageDirectoryCap x as2) = {x}"
| "aobj_ref' (PageTableCap x as3) = {x}"

fun acap_asid' :: "arch_cap \<Rightarrow> asid set" where
  "acap_asid' (PageCap _ _ _ _ mapping) = fst ` set_option mapping"
| "acap_asid' (PageTableCap _ mapping) = fst ` set_option mapping"
| "acap_asid' (PageDirectoryCap _ asid_opt) = set_option asid_opt"
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
       (pdptr, asid && mask asid_low_bits, AASIDPool, a) \<in> vrefs poolptr \<rbrakk>
       \<Longrightarrow> (pasASIDAbs aag asid, a, pasObjectAbs aag pdptr)
             \<in> state_asids_to_policy_aux aag caps asid_tab vrefs"
| sata_asidpool:
    "\<lbrakk> asid_tab (asid_high_bits_of asid) = Some poolptr; asid \<noteq> 0 \<rbrakk>
       \<Longrightarrow> (pasObjectAbs aag poolptr, AAuth ASIDPoolMapsASID, pasASIDAbs aag asid)
             \<in> state_asids_to_policy_aux aag caps asid_tab vrefs"

definition
  "state_asids_to_policy_arch aag caps astate vrefs \<equiv>
     state_asids_to_policy_aux aag caps (arm_asid_table astate) vrefs"
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

(* FIXME AC: locale? *)
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


subsection \<open>Misc definitions\<close>

definition ctxt_IP_update where
  "ctxt_IP_update ctxt \<equiv> ctxt(NextIP := ctxt FaultIP)"

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
        ArchObjectCap (PageCap False p' R vms _) \<Rightarrow>
          if AllowWrite \<in> R
          then (ptr_range (p' + (tcb_ipc_buffer tcb && mask (pageBitsForSize vms))) msg_align_bits)
          else {}
      | _ \<Rightarrow> {})"

end


context begin interpretation Arch .

requalify_consts
  vspace_cap_rights_to_auth
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
