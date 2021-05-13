(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInterrupt_AC
imports
  Interrupt_AC
begin


definition arch_authorised_irq_ctl_inv ::
  "'a PAS \<Rightarrow> Invocations_A.arch_irq_control_invocation \<Rightarrow> bool" where
  "arch_authorised_irq_ctl_inv aag cinv \<equiv> True"

global_interpretation Interrupt_AC_1?: Interrupt_AC_1 "arch_authorised_irq_ctl_inv"
proof goal_cases
  interpret Arch .
  case 1 show ?case
    sorry
qed


global_interpretation Interrupt_AC_2?: Interrupt_AC_2 "arch_authorised_irq_ctl_inv"
proof goal_cases
  interpret Arch .
  case 1 show ?case
    sorry
qed

end
