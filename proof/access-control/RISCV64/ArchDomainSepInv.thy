(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDomainSepInv
imports
  "DomainSepInv"
begin

global_interpretation DomainSepInv_1?: DomainSepInv_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    sorry
qed

global_interpretation DomainSepInv_2?: DomainSepInv_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    sorry
qed

end
