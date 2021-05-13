(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchIpc_AC
imports Ipc_AC
begin

(*

context begin interpretation Arch .

crunches arch_post_cap_deletion
  for state_vrefs[wp]: "\<lambda>s. P (state_vrefs (s :: det_ext state))"
  (wp: crunch_wps hoare_unless_wp select_wp dxo_wp_weak simp: crunch_simps)

end

crunches deleted_irq_handler, send_signal
  for state_vrefs[wp]: "\<lambda>s. P (state_vrefs (s :: det_ext state))"
  (wp: crunch_wps hoare_unless_wp select_wp dxo_wp_weak simp: crunch_simps)

*)


global_interpretation Ipc_AC_1?: Ipc_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    sorry
qed

context is_extended begin interpretation Arch . (*FIXME: arch_split*)

lemma list_integ_lift_in_ipc:
  assumes li:
   "\<lbrace>list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st and Q\<rbrace>
    f
    \<lbrace>\<lambda>_. list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st\<rbrace>"
  assumes ekh: "\<And>P. \<lbrace>\<lambda>s. P (ekheap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
  assumes rq: "\<And>P. \<lbrace> \<lambda>s. P (ready_queues s) \<rbrace> f \<lbrace> \<lambda>rv s. P (ready_queues s) \<rbrace>"
  shows "\<lbrace>integrity_tcb_in_ipc aag X receiver epptr ctxt st and Q\<rbrace>
         f
         \<lbrace>\<lambda>_. integrity_tcb_in_ipc aag X receiver epptr ctxt st\<rbrace>"
  apply (unfold integrity_tcb_in_ipc_def integrity_def[abs_def])
  apply (simp del:split_paired_All)
  apply (rule hoare_pre)
   apply (simp only: integrity_cdt_list_as_list_integ)
   apply (rule hoare_lift_Pf2[where f="ekheap"])
    apply (simp add: tcb_states_of_state_def get_tcb_def)
    apply (wp li[simplified tcb_states_of_state_def get_tcb_def] ekh rq)+
  apply (simp only: integrity_cdt_list_as_list_integ)
  apply (simp add: tcb_states_of_state_def get_tcb_def)
  done

end


global_interpretation Ipc_AC_2?: Ipc_AC_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    sorry
qed

end
