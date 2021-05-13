(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchSyscall_AC
imports
  Syscall_AC
begin

global_interpretation Syscall_AC_1?: Syscall_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    sorry
qed

end
