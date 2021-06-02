(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchArch_AC
imports Arch_AC
begin

text\<open>

Arch-specific access control.

\<close>

context Arch begin global_naming ARM_A

named_theorems Arch_AC_assms

lemma set_mrs_state_vrefs[Arch_AC_assms, wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and (\<lambda>s. P (state_vrefs s))\<rbrace>
   set_mrs thread buf msgs
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_mrs_def split_def set_object_def get_object_def split del: if_split)
  apply (wpsimp wp: gets_the_wp get_wp put_wp mapM_x_wp'
              simp: zipWithM_x_mapM_x split_def store_word_offs_def
         split_del: if_split)
  apply (subst state_vrefs_eqI)
        prefer 7
        apply assumption
       apply (clarsimp simp: opt_map_def)
      apply (fastforce simp: opt_map_def aobj_of_def)
     apply clarsimp
    apply (auto simp: valid_arch_state_def)
  done

lemma mul_add_word_size_lt_msg_align_bits_ofnat[Arch_AC_assms]:
  "\<lbrakk> p < 2 ^ (msg_align_bits - word_size_bits); k < 4 \<rbrakk>
     \<Longrightarrow> of_nat p * of_nat word_size + k < (2 :: obj_ref) ^ msg_align_bits"
  apply (rule is_aligned_add_less_t2n[where n=word_size_bits])
     apply (simp_all add: msg_align_bits' word_size_word_size_bits is_aligned_mult_triv2)
   apply (simp_all add: word_size_word_size_bits word_size_bits_def)
   apply (word_bitwise, simp)
  apply (erule word_less_power_trans_ofnat[where k=3 and m=10, simplified], simp)
  done

end


global_interpretation Arch_AC_1?: Arch_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact Arch_AC_assms)
qed


context Arch begin global_naming ARM_A

lemma store_pte_respects:
  "\<lbrace>integrity aag X st and K (is_subject aag (p && ~~ mask pt_bits))\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wp get_object_wp set_object_integrity_autarch)
  apply simp
  done

lemma integrity_arch_state [iff]:
  "riscv_asid_table v = riscv_asid_table (arch_state s)
   \<Longrightarrow> integrity aag X st (s\<lparr>arch_state := v\<rparr>) = integrity aag X st s"
  unfolding integrity_def by simp

lemma integrity_arm_asid_map[iff]:
  "integrity aag X st (s\<lparr>arch_state := ((arch_state s)\<lparr>riscv_global_pts := v\<rparr>)\<rparr>) =
   integrity aag X st s"
  unfolding integrity_def by simp

lemma integrity_arm_hwasid_table[iff]:
  "integrity aag X st (s\<lparr>arch_state := ((arch_state s)\<lparr>riscv_kernel_vspace := v\<rparr>)\<rparr>) =
   integrity aag X st s"
  unfolding integrity_def by simp

(*
crunch respects[wp]: arm_context_switch "integrity X aag st"
  (simp: dmo_bind_valid dsb_def isb_def writeTTBR0_def invalidateLocalTLB_ASID_def
         setHardwareASID_def set_current_pd_def ignore: do_machine_op)

crunch respects[wp]: set_vm_root "integrity X aag st"
  (simp: set_current_pd_def isb_def dsb_def writeTTBR0_def dmo_bind_valid crunch_simps
     wp: crunch_wps ignore: do_machine_op)

crunch respects[wp]: set_vm_root_for_flush "integrity X aag st"
  (wp: crunch_wps simp: set_current_pd_def crunch_simps ignore: do_machine_op)

crunch respects[wp]: flush_table "integrity X aag st"
  (wp: crunch_wps simp: invalidateLocalTLB_ASID_def crunch_simps ignore: do_machine_op)

crunch respects[wp]: page_table_mapped "integrity X aag st"
*)


(*
lemma kheap_eq_state_vrefs_pas_refinedD:
  "\<lbrakk> kheap s p = Some (ArchObj ko); (p', r, t, a) \<in> vs_refs_aux lvl ko; pas_refined aag s \<rbrakk>
     \<Longrightarrow> abs_has_auth_to aag a p p'"
  apply (drule kheap_eq_state_vrefsD)
  apply (erule pas_refined_mem[OF sta_vref, rotated])
  apply simp
  done
*)

(*
lemma find_pd_for_asid_authority2:
  "\<lbrace>\<lambda>s. \<forall>pd. (\<forall>aag. pas_refined aag s
                    \<longrightarrow> (pasASIDAbs aag asid, Control, pasObjectAbs aag pd) \<in> pasPolicy aag) \<and>
             (pspace_aligned s \<and> valid_vspace_objs s \<longrightarrow> is_aligned pd pd_bits) \<and>
             (\<exists>\<rhd> pd) s
             \<longrightarrow> Q pd s\<rbrace>
   find_pd_for_asid asid
   \<lbrace>Q\<rbrace>, -" (is "\<lbrace>?P\<rbrace> ?f \<lbrace>Q\<rbrace>,-")
  apply (clarsimp simp: validE_R_def validE_def valid_def imp_conjL[symmetric])
  apply (frule in_inv_by_hoareD[OF find_pd_for_asid_inv], clarsimp)
  apply (drule spec, erule mp)
  apply (simp add: use_validE_R[OF _ find_pd_for_asid_authority1]
                   use_validE_R[OF _ find_pd_for_asid_aligned_pd_bits]
                   use_validE_R[OF _ find_pd_for_asid_lookup])
  done
*)

lemma ptes_of_idx:
  "\<lbrakk> ptes_of s (pt_slot_offset level pt_ptr p) = Some pte;
     pts_of s pt_ptr = Some pt; pspace_aligned s \<rbrakk> \<Longrightarrow>
    pt (table_index (pt_slot_offset level pt_ptr p)) = pte"
  apply (drule_tac pt_ptr=pt_ptr in pspace_aligned_pts_ofD, simp)
  apply (fastforce simp: pte_of_def)
  done

lemma pt_lookup_from_level_is_subject:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<and>
        is_subject aag pt_ptr \<and> level \<le> max_pt_level \<and> vref \<in> user_region \<and>
        (\<exists>asid pt. vs_lookup_table level asid vref s = Some (level, pt_ptr) \<and>
                   aobjs_of s pt_ptr = Some (PageTable pt))\<rbrace>
   pt_lookup_from_level level pt_ptr vref pt
   \<lbrace>\<lambda>rv _. is_subject aag (table_base rv)\<rbrace>,-"
  apply (induct level arbitrary: pt_ptr)
   apply (subst pt_lookup_from_level_simps, simp)
   apply wpsimp

   apply (subst pt_lookup_from_level_simps, simp)
apply wp
apply (erule meta_allE)+
apply assumption
apply wpsimp+
apply safe

apply (subst pt_slot_offset_id)
apply (rule is_aligned_pt)
apply (fastforce simp add: opt_map_def aobj_of_def pte_of_def obj_at_def split: option.splits kernel_object.splits)
apply clarsimp
apply clarsimp

prefer 4
apply (subst pt_slot_offset_id)
apply (rule is_aligned_pt)
apply (fastforce simp add: opt_map_def aobj_of_def pte_of_def obj_at_def split: option.splits kernel_object.splits)
apply clarsimp
apply clarsimp

apply (subst aag_has_Control_iff_owns[symmetric])
apply assumption

apply (clarsimp simp: pas_refined_def)
apply (erule subsetD)
apply (clarsimp simp: auth_graph_map_def)
apply (rule_tac x=pt_ptr in exI, rule conjI)
apply simp
apply (rule exI, rule conjI, rule refl)


apply (rule sta_vref)

apply (simp add: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
apply (rule exI, rule exI, rule conjI, rule refl)
apply (rule exI, rule exI, rule exI, rule conjI, assumption)
apply simp

apply (subst vs_refs_aux_def)
apply clarsimp

apply (frule ptes_of_idx)
apply (simp add: opt_map_def)
apply clarsimp
apply (case_tac rv; clarsimp)

apply (clarsimp simp: graph_of_def
pte_ref2_def
)
apply (rule_tac x="table_index (pt_slot_offset level pt_ptr vref)" in exI)
apply_trace clarsimp

apply (intro conjI)
apply (clarsimp simp: pptr_from_pte_def)
apply (rule refl)
apply (rule refl)

apply (rule_tac x=asid in exI)
apply (rule vs_lookup_table_step)
apply assumption
apply simp
apply simp
apply simp
apply simp
apply (case_tac rv; clarsimp simp: pptr_from_pte_def)


apply (prop_tac "\<exists>asid. vs_lookup_table (level - 1) asid vref s = Some (level - 1, pptr_from_pte rv)")
apply (rule_tac x=asid in exI)
apply (rule vs_lookup_table_step)
apply assumption
apply simp
apply simp
apply simp
apply simp
apply (case_tac rv; clarsimp simp: pptr_from_pte_def)

apply clarsimp
apply (drule vs_lookup_table_pt_at) back
apply simp
apply simp
apply simp
apply simp
apply simp

apply (clarsimp simp: opt_map_def obj_at_def)

done

thm vs_lookup_table_def
thm vspace_for_asid_def
(* Good, no delete please *)
lemma find_vspace_for_asid_is_subject:
  "\<lbrace>pas_refined aag and K (is_subject_asid aag asid)\<rbrace>
   find_vspace_for_asid asid
   \<lbrace>\<lambda>pt _. is_subject aag pt\<rbrace>,-"
 apply (rule hoare_pre)
   apply (simp add: find_vspace_for_asid_def)
   apply wpsimp
  apply clarsimp
apply (subst aag_has_Control_iff_owns[symmetric])
apply assumption

  apply (clarsimp simp: vspace_for_asid_def)
  apply (clarsimp simp: obj_at_def pas_refined_def)
apply (drule sym)
apply clarsimp
apply (erule subsetD) back
apply (rule sata_asid_lookup)
apply (simp add: vspace_for_pool_def pool_for_asid_def)

apply (clarsimp simp: state_vrefs_def)

apply (prop_tac "vs_lookup_table max_pt_level asid 0 s = Some (max_pt_level, y)")
apply (clarsimp simp: vs_lookup_table_def obind_def)
apply (clarsimp simp: vspace_for_pool_def pool_for_asid_def obind_def opt_map_def split: option.splits)

apply (rule exI)
apply (rule conjI)
apply (rule_tac x=asid_pool_level in exI)
apply (rule exI)
apply (rule conjI)
apply (rule refl)
apply (rule_tac x=asid_pool_level in exI)
apply (rule_tac x=asid in exI)
apply (rule_tac x=0 in exI)
apply (rule conjI)
apply (simp add: vs_lookup_table_def)
apply (simp add: obind_def)
apply (simp add: vspace_for_pool_def pool_for_asid_def obind_def opt_map_def
split: option.splits)
apply simp


apply (subst vs_refs_aux_def)
apply clarsimp
apply (clarsimp simp: map_set_in)

apply (prop_tac "(asid_low_bits_of asid, y) \<in> graph_of x2")
apply (clarsimp simp: graph_of_def)
apply (erule bexI[rotated])
apply clarsimp
apply (subst ucast_up_ucast[symmetric])
prefer 2
apply (subst asid_low_bits_of_mask_eq)
apply simp
  apply (simp add: is_up_def source_size_def target_size_def word_size)
done



thm pt_lookup_from_level_wrp
lemma unmap_page_table_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs and K (is_subject_asid aag asid \<and> vaddr \<in> user_region)\<rbrace>
   unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: unmap_page_table_def  )
  apply (rule hoare_pre)
apply wpsimp
   apply ((wpsimp wp:  hoare_vcg_all_lift_R dmo_mol_respects store_pte_respects pt_lookup_from_level_wrp
               simp: sfence_def
          | wp (once) hoare_drop_imps)+)[1]
   apply ((wpsimp wp:  hoare_vcg_all_lift_R dmo_mol_respects store_pte_respects pt_lookup_from_level_wrp
               simp: sfence_def
          | wp (once) hoare_drop_imps)+)[1]
apply clarsimp

apply (rule hoare_vcg_conj_liftE)
   apply ((wpsimp wp:  hoare_vcg_all_lift_R dmo_mol_respects store_pte_respects pt_lookup_from_level_wrp
               simp: sfence_def
          | wp (once) hoare_drop_imps)+)[1]

apply (rule hoare_vcg_E_elim)
prefer 2
apply (rule pt_lookup_from_level_is_subject)
apply wp
   apply ((wpsimp wp:  hoare_vcg_all_lift_R dmo_mol_respects store_pte_respects pt_lookup_from_level_wrp

               simp: sfence_def
          | wp (once) hoare_drop_imps)+)[1]

apply clarsimp

apply auto

(*****************************)
apply (subst aag_has_Control_iff_owns[symmetric])
apply assumption

  apply (clarsimp simp: vspace_for_asid_def)
  apply (clarsimp simp: obj_at_def pas_refined_def)
apply (drule sym)
apply clarsimp
apply (erule subsetD) back
apply (rule sata_asid_lookup)
apply (simp add: vspace_for_pool_def pool_for_asid_def)

apply (clarsimp simp: state_vrefs_def)

apply (prop_tac "vs_lookup_table max_pt_level asid 0 s = Some (max_pt_level, pt)")
apply (clarsimp simp: vs_lookup_table_def obind_def)
apply (clarsimp simp: vspace_for_pool_def pool_for_asid_def obind_def opt_map_def split: option.splits)

apply (rule exI)
apply (rule conjI)
apply (rule_tac x=asid_pool_level in exI)
apply (rule exI)
apply (rule conjI)
apply (rule refl)
apply (rule_tac x=asid_pool_level in exI)
apply (rule_tac x=asid in exI)
apply (rule_tac x=0 in exI)
apply (rule conjI)
apply (simp add: vs_lookup_table_def)
apply (simp add: obind_def)
apply (simp add: vspace_for_pool_def pool_for_asid_def obind_def opt_map_def
split: option.splits)
apply simp

apply (subst vs_refs_aux_def)
apply clarsimp
apply (clarsimp simp: map_set_in)

apply (prop_tac "(asid_low_bits_of asid, pt) \<in> graph_of x2")
apply (clarsimp simp: graph_of_def)
apply (erule bexI[rotated])
apply clarsimp
apply (subst ucast_up_ucast[symmetric])
prefer 2
apply (subst asid_low_bits_of_mask_eq)
apply simp
  apply (simp add: is_up_def source_size_def target_size_def word_size)
(*************************)

apply (rule_tac x=asid in exI)
apply (clarsimp simp: vs_lookup_table_def vspace_for_asid_def vspace_for_pool_def pool_for_asid_def)
apply (clarsimp simp: obind_def)

apply (prop_tac "\<exists>asid. vs_lookup_table max_pt_level asid vaddr s = Some (max_pt_level, pt)")
apply (rule_tac x=asid in exI)
apply (clarsimp simp: vs_lookup_table_def vspace_for_asid_def vspace_for_pool_def pool_for_asid_def)
apply (clarsimp simp: obind_def)

apply clarsimp
apply (drule vs_lookup_table_pt_at)
apply simp
apply simp
apply fastforce
apply fastforce
apply fastforce

apply (clarsimp simp: opt_map_def obj_at_def)

done

(*
(* (case_option True (is_subject aag o fst) (pde_ref2 pde)) \<and> *)
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
*)


lemma perform_page_table_invocation_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs and valid_pti page_table_invocation
                       and K (authorised_page_table_inv aag page_table_invocation)\<rbrace>
   perform_page_table_invocation page_table_invocation
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: perform_page_table_invocation_def perform_pt_inv_map_def perform_pt_inv_unmap_def
             cong: page_table_invocation.case_cong option.case_cong prod.case_cong
                   cap.case_cong arch_cap.case_cong)
apply (cases page_table_invocation; clarsimp)
  apply (wpsimp wp: set_cap_integrity_autarch
                    store_pte_respects unmap_page_table_respects mapM_wp'
              simp: mapM_x_mapM authorised_page_table_inv_def  sfence_def
)
apply (rename_tac cap fst_cslot_ptr snd_cslot_ptr)
apply (wpsimp wp: set_cap_integrity_autarch )
apply (rule mapM_x_inv_wp)
apply (prop_tac "integrity aag X st s \<and> is_subject aag fst_cslot_ptr \<and> is_PageTableCap cap")
apply assumption
apply clarsimp
apply clarsimp
apply (rule hoare_vcg_conj_lift)

apply (wpsimp wp: store_pte_respects)
apply (prop_tac "integrity aag X st s \<and> is_PageTableCap cap")
apply assumption
apply (clarsimp simp: authorised_page_table_inv_def)
apply (case_tac cap; clarsimp)
  apply (wpsimp wp: set_cap_integrity_autarch
                    store_pte_respects unmap_page_table_respects mapM_wp'
              simp: mapM_x_mapM authorised_page_table_inv_def  sfence_def
)
apply clarsimp
  apply (wpsimp wp: set_cap_integrity_autarch
                    store_pte_respects unmap_page_table_respects mapM_wp'
              simp: mapM_x_mapM authorised_page_table_inv_def  sfence_def
)
apply wp
apply clarsimp
apply (rule conjI)
apply (clarsimp simp: authorised_page_table_inv_def)
apply clarsimp
apply (rule conjI)
apply (case_tac cap; clarsimp simp: authorised_page_table_inv_def)
apply (rule conjI)
prefer 2
apply (clarsimp simp: authorised_page_table_inv_def)

apply (clarsimp simp: valid_pti_def)
apply (clarsimp simp: valid_arch_cap_def)
apply (clarsimp simp: wellformed_acap_def)
apply (case_tac cap; clarsimp)
apply (clarsimp simp: wellformed_mapdata_def)
done

(*
crunch arm_asid_table_inv [wp]: unmap_page_table "\<lambda>s. P (arm_asid_table (arch_state s))"
  (wp: crunch_wps simp: crunch_simps)

lemma clas_update_map_data_strg:
  "(is_pg_cap cap \<or> is_pt_cap cap)
   \<longrightarrow> cap_links_asid_slot aag p (ArchObjectCap (update_map_data (the_arch_cap cap) None))"
  unfolding cap_links_asid_slot_def
  by (fastforce simp: is_cap_simps update_map_data_def)

lemmas pte_ref_simps = pte_ref_def[split_simps pte.split]

lemmas store_pde_pas_refined_simple =
  store_pde_pas_refined[where pde=InvalidPDE, simplified pde_ref_simps, simplified]

crunch pas_refined[wp]: unmap_page_table "pas_refined aag"
  (wp: crunch_wps store_pde_pas_refined_simple simp: crunch_simps pde_ref_simps)

lemma pde_ref_pde_ref2:
  "\<lbrakk> pde_ref x = Some v; pde_ref2 x = Some v' \<rbrakk>
     \<Longrightarrow> v' = (v, 0, {Control})"
  unfolding pde_ref_def pde_ref2_def
  by (cases x, simp_all)

lemma mask_PTCap_eq:
  "(ArchObjectCap (PageTableCap a b) = mask_cap R cap) = (cap = ArchObjectCap (PageTableCap a b))"
  by (auto simp: mask_cap_def cap_rights_update_def acap_rights_update_def
          split: arch_cap.splits cap.splits bool.splits)

(* FIXME MOVE *)
crunch cdt[wp]: unmap_page_table "\<lambda>s. P (cdt s)"
  (simp: crunch_simps wp: crunch_wps)
*)

lemma is_transferable_is_arch_update:
  "is_arch_update cap cap' \<Longrightarrow> is_transferable (Some cap) = is_transferable (Some cap')"
  using is_transferable.simps is_arch_cap_def is_arch_update_def cap_master_cap_def
  by (simp split: cap.splits arch_cap.splits)

lemma perform_page_table_invocation_pas_refined [wp]:
  "\<lbrace>pas_refined aag and invs and valid_pti iv and K (authorised_page_table_inv aag iv)\<rbrace>
   perform_page_table_invocation iv
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  by (wpsimp wp: perform_page_table_invocation_pas_refined)

(*
definition authorised_slots :: "'a PAS \<Rightarrow> pte \<times> obj_ref list + pde \<times> obj_ref list \<Rightarrow> bool" where
 "authorised_slots aag m \<equiv> case m of
    Inl (pte, slots) \<Rightarrow>
      (\<forall>x. pte_ref pte = Some x
           \<longrightarrow> (\<forall>a \<in> snd (snd x). \<forall>p \<in> ptr_range (fst x) (fst (snd x)). aag_has_auth_to aag a p)) \<and>
      (\<forall>x \<in> set slots. is_subject aag (x && ~~ mask pt_bits))
  | Inr (pde, slots) \<Rightarrow>
      (\<forall>x. pde_ref2 pde = Some x
           \<longrightarrow> (\<forall>a \<in> snd (snd x). \<forall>p \<in> ptr_range (fst x) (fst (snd x)). aag_has_auth_to aag a p)) \<and>
      (\<forall>x \<in> set slots. is_subject aag (x && ~~ mask pd_bits))"

definition authorised_page_inv :: "'a PAS \<Rightarrow> page_invocation \<Rightarrow> bool" where
  "authorised_page_inv aag pgi \<equiv> case pgi of
     PageMap asid cap ptr slots \<Rightarrow>
       pas_cap_cur_auth aag cap \<and> is_subject aag (fst ptr) \<and> authorised_slots aag slots
   | PageUnmap cap ptr \<Rightarrow> pas_cap_cur_auth aag (ArchObjectCap cap) \<and> is_subject aag (fst ptr)
   | PageFlush typ start end pstart pd asid \<Rightarrow> True
   | PageGetAddr ptr \<Rightarrow> True"
*)

definition authorised_slots :: "'a PAS \<Rightarrow> pte \<times> obj_ref \<Rightarrow> bool" where
 "authorised_slots aag m \<equiv> case m of
    (pte, slot) \<Rightarrow>
\<comment> \<open>
      (\<forall>level x. pte_ref2 level pte = Some x
           \<longrightarrow> (\<forall>a \<in> snd (snd x). \<forall>p \<in> ptr_range (fst x) (fst (snd x)). aag_has_auth_to aag a p)) \<and> \<close>
      (is_subject aag (slot && ~~ mask pt_bits))"

(* FIXME ryanb - pass level to authorised slots *)
definition authorised_page_inv :: "'a PAS \<Rightarrow> page_invocation \<Rightarrow> bool" where
  "authorised_page_inv aag pgi \<equiv> case pgi of
     PageMap cap ptr slots \<Rightarrow>
       pas_cap_cur_auth aag (ArchObjectCap cap) \<and> is_subject aag (fst ptr) \<and> authorised_slots aag slots
   | PageUnmap cap ptr \<Rightarrow> pas_cap_cur_auth aag (ArchObjectCap cap) \<and> is_subject aag (fst ptr)
   | PageGetAddr ptr \<Rightarrow> True"

(*

datatype page_invocation =
    PageMap
      (pg_inv_cap : arch_cap)
      (pg_inv_cslot : cslot_ptr)
      (pg_inv_entries : "pte \<times> obj_ref")

datatype page_invocation
     = PageMap
         (page_map_asid: asid)
         (page_map_cap: cap)
         (page_map_ct_slot: cslot_ptr)
         (page_map_entries: "pte \<times> (obj_ref list) + pde \<times> (obj_ref list)")

*)

(*

crunch respects[wp]: lookup_pt_slot "integrity X aag st"

lemma vs_refs_no_global_pts_pdI:
  "\<lbrakk> pd (ucast r) = PageTablePDE x a b; (ucast r :: 12 word) < ucast (kernel_base >> 20) \<rbrakk>
     \<Longrightarrow> (ptrFromPAddr x, r && mask 12, APageDirectory, Control) \<in>
           vs_refs_no_global_pts (ArchObj (PageDirectory pd))"
  apply (clarsimp simp: vs_refs_no_global_pts_def)
  apply (drule_tac f=pde_ref2 in arg_cong, simp add: pde_ref_simps o_def)
  apply (rule rev_bexI, rule DiffI, erule graph_ofI)
   apply simp
  apply (clarsimp simp: ucast_ucast_mask)
  done

lemma lookup_pt_slot_authorised:
  "\<lbrace>\<exists>\<rhd> pd and valid_vspace_objs and pspace_aligned and pas_refined aag
          and K (is_subject aag pd) and K (is_aligned pd 14 \<and> vptr < kernel_base)\<rbrace>
   lookup_pt_slot pd vptr
   \<lbrace>\<lambda>rv _. is_subject aag (rv && ~~ mask pt_bits)\<rbrace>, -"
  apply (simp add: lookup_pt_slot_def)
  apply (wp get_pde_wp | wpc)+
  apply (subgoal_tac "is_aligned pd pd_bits")
   apply (clarsimp simp: lookup_pd_slot_pd)
   apply (drule(2) valid_vspace_objsD)
   apply (clarsimp simp: obj_at_def)
   apply (drule kheap_eq_state_vrefs_pas_refinedD)
     apply (erule vs_refs_no_global_pts_pdI)
     apply (drule(1) less_kernel_base_mapping_slots)
     apply (simp add: kernel_mapping_slots_def)
    apply assumption
   apply (simp add: aag_has_Control_iff_owns)
   apply (drule_tac f="\<lambda>pde. valid_pde pde s" in arg_cong, simp)
   apply (clarsimp simp: obj_at_def less_kernel_base_mapping_slots)
   apply (erule pspace_alignedE, erule domI)
   apply (simp add: pt_bits_def pageBits_def)
   apply (subst is_aligned_add_helper, assumption)
    apply (rule shiftl_less_t2n)
     apply (rule order_le_less_trans, rule word_and_le1, simp)
    apply simp
   apply simp
  apply (simp add: pd_bits_def pageBits_def)
  done

lemma is_aligned_6_masks:
  "\<lbrakk> is_aligned (p :: obj_ref) 6; bits = pt_bits \<or> bits = pd_bits \<rbrakk>
     \<Longrightarrow> \<forall>x \<in> set [0, 4 .e. 0x3C]. x + p && ~~ mask bits = p && ~~ mask bits"
  apply clarsimp
  apply (drule subsetD[OF upto_enum_step_subset])
  apply (subst mask_lower_twice[symmetric, where n=6])
   apply (auto simp add: pt_bits_def pageBits_def pd_bits_def)[1]
  apply (subst add.commute, subst is_aligned_add_helper, assumption)
   apply (simp add: order_le_less_trans)
  apply simp
  done

lemma lookup_pt_slot_authorised2:
  "\<lbrace>\<exists>\<rhd> pd and K (is_subject aag pd) and
    K (is_aligned pd 14 \<and> is_aligned vptr 16 \<and> vptr < kernel_base) and
    valid_vspace_objs and valid_arch_state and equal_kernel_mappings and
    valid_global_objs and pspace_aligned and pas_refined aag\<rbrace>
   lookup_pt_slot pd vptr
   \<lbrace>\<lambda>rv _. \<forall>x\<in>set [0 , 4 .e. 0x3C]. is_subject aag (x + rv && ~~ mask pt_bits)\<rbrace>, -"
  apply (clarsimp simp: validE_R_def valid_def validE_def
                 split: sum.split)
  apply (frule use_validE_R[OF _ lookup_pt_slot_authorised])
   apply fastforce
  apply (frule use_validE_R[OF _ lookup_pt_slot_is_aligned_6])
   apply (fastforce simp add: vmsz_aligned_def pd_bits_def pageBits_def)
  apply (simp add: is_aligned_6_masks)
  done

lemma lookup_pt_slot_authorised3:
  "\<lbrace>\<exists>\<rhd> pd and K (is_subject aag pd) and
    K (is_aligned pd 14 \<and> is_aligned vptr 16 \<and> vptr < kernel_base) and
    valid_vspace_objs and valid_arch_state and equal_kernel_mappings and
    valid_global_objs and pspace_aligned and pas_refined aag\<rbrace>
   lookup_pt_slot pd vptr
   \<lbrace>\<lambda>rv _.  \<forall>x\<in>set [rv, rv + 4 .e. rv + 0x3C]. is_subject aag (x && ~~ mask pt_bits)\<rbrace>, -"
  apply (rule_tac Q'="\<lambda>rv s. is_aligned rv 6 \<and> (\<forall>x\<in>set [0, 4 .e. 0x3C].
                                                  is_subject aag (x + rv && ~~ mask pt_bits))"
               in hoare_post_imp_R)
  apply (rule hoare_pre)
  apply (wp lookup_pt_slot_is_aligned_6 lookup_pt_slot_authorised2)
   apply (fastforce simp: vmsz_aligned_def pd_bits_def pageBits_def)
  apply simp
  apply (simp add: p_0x3C_shift)
  done

crunch respects[wp]: flush_page "integrity aag X st"
  (simp: invalidateLocalTLB_VAASID_def ignore: do_machine_op)

lemma find_pd_for_asid_pd_owned[wp]:
  "\<lbrace>pas_refined aag and K (is_subject_asid aag asid)\<rbrace>
   find_pd_for_asid asid
   \<lbrace>\<lambda>rv _. is_subject aag rv\<rbrace>,-"
  apply (wp find_pd_for_asid_authority2)
  apply (auto simp: aag_has_Control_iff_owns)
  done

lemmas store_pte_pas_refined_simple =
  store_pte_pas_refined[where pte=InvalidPTE, simplified pte_ref_simps, simplified]

crunch pas_refined[wp]: unmap_page "pas_refined aag"
  (wp: crunch_wps store_pde_pas_refined_simple store_pte_pas_refined_simple simp: crunch_simps)

*)

lemma is_subject_trans:
  "\<lbrakk> is_subject aag x;  pas_refined aag s; (pasObjectAbs aag x, Control, pasObjectAbs aag y) \<in> pasPolicy aag \<rbrakk>
     \<Longrightarrow> is_subject aag y"
apply (subst aag_has_Control_iff_owns[symmetric])
apply simp
apply simp
done

lemma is_subject_asid_trans:
  "\<lbrakk> is_subject_asid aag x;  pas_refined aag s; (pasASIDAbs aag x, Control, pasObjectAbs aag y) \<in> pasPolicy aag \<rbrakk>
     \<Longrightarrow> is_subject aag y"
apply (subst aag_has_Control_iff_owns[symmetric])
apply simp
apply simp
done



lemma pt_walk_is_subject:
  "\<lbrakk> pas_refined aag s; valid_vspace_objs s; valid_asid_table s; pspace_aligned s;
     pt_walk level bot_level pt_ptr vptr (ptes_of s) = Some (level', pt);
     (\<exists>asid. vs_lookup_table level asid vptr s = Some (level, pt_ptr));
     level \<le> max_pt_level; vptr \<in> user_region; is_subject aag pt_ptr \<rbrakk>
     \<Longrightarrow> is_subject aag pt"
apply (induct level arbitrary: pt_ptr )
apply (subst (asm) pt_walk.simps, simp)

apply (subst (asm) pt_walk.simps) back
apply (clarsimp simp: obind_def split: if_splits option.splits)
apply (erule meta_allE)
apply (drule meta_mp)
apply assumption
apply (drule meta_mp)
prefer 2
apply (drule meta_mp)
prefer 2
apply simp
prefer 2
apply (rule_tac x=asid in exI)

apply (rule vs_lookup_table_extend)
apply assumption
apply (subst pt_walk.simps)
apply simp
apply (clarsimp simp: obind_def)

apply clarsimp


apply (frule vs_lookup_table_pt_at)
apply clarsimp
apply clarsimp
apply clarsimp

apply clarsimp
apply clarsimp


apply (clarsimp simp: typ_at_eq_kheap_obj)


apply (erule (1) is_subject_trans)
apply (clarsimp simp: pas_refined_def)
apply (erule subsetD)
apply (clarsimp simp: auth_graph_map_def)
apply (rule exI, rule conjI, rule refl)+
apply (rule sta_vref)
apply (subst state_vrefs_def)
apply clarsimp

apply (rule exI)
apply (rule conjI)
apply (rule exI, rule exI, rule conjI, rule refl)

apply (rule exI, rule exI, rule exI)
apply (rule conjI)
apply (assumption)

apply (rule conjI)
apply (simp add: opt_map_def)
apply clarsimp

apply (frule ptes_of_idx)
apply (simp add: opt_map_def)
apply clarsimp
apply clarsimp

apply (clarsimp simp: ptes_of_def obind_def is_PageTablePTE_def split: option.splits)

apply (clarsimp simp: vs_refs_aux_def)
apply (prop_tac "(table_index (pt_slot_offset level pt_ptr vptr), ptrFromPAddr (addr_from_ppn x31), 0, {Control}) \<in>graph_of (pte_ref2 level \<circ> pta)")
apply (clarsimp simp: graph_of_def pte_ref2_def)

apply (rule bexI)
prefer 2
apply assumption
apply clarsimp
apply (clarsimp simp: pptr_from_pte_def)
apply auto
done


lemma pt_lookup_slot_from_level_is_subject:
  "\<lbrakk> pas_refined aag s; valid_vspace_objs s; valid_asid_table s; pspace_aligned s;
     pt_lookup_slot_from_level level bot_level pt_ptr vptr (ptes_of s) = Some (level', pt);
     (\<exists>asid. vs_lookup_table level asid vptr s = Some (level, pt_ptr));
     level \<le> max_pt_level; vptr \<in> user_region; is_subject aag pt_ptr \<rbrakk>
     \<Longrightarrow> is_subject aag (table_base pt)"
apply (clarsimp simp: pt_lookup_slot_from_level_def obind_def split: option.splits)
apply (drule (4) pt_walk_is_subject)
defer
apply clarsimp+
apply (subst pt_slot_offset_id)
apply (erule pt_walk_is_aligned)
apply (erule vs_lookup_table_is_aligned)
apply clarsimp+
apply fastforce
done

thm pt_lookup_slot_def
pt_lookup_slot_from_level_def


lemma unmap_page_respects:
  "\<lbrace>integrity aag X st and pspace_aligned and valid_vspace_objs and valid_arch_state
                       and K (is_subject_asid aag asid) and pas_refined aag
                       and K (vptr \<in> user_region)\<rbrace>
   unmap_page sz asid vptr pptr
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: unmap_page_def swp_def cong: vmpage_size.case_cong)
  apply (rule hoare_pre)
   apply (wpsimp wp: store_pte_respects
                     hoare_drop_imps[where Q="\<lambda>rv. integrity aag X st"]
               simp: sfence_def  is_aligned_mask[symmetric]
          | wp (once) hoare_drop_imps
                      mapM_set''[where f="(\<lambda>a. store_pte a InvalidPTE)"
                                   and I="\<lambda>x s. is_subject aag (x && ~~ mask pt_bits)"
                                   and Q="integrity aag X st"]
          | wp (once) hoare_drop_imps[where R="\<lambda>rv s. rv"])+

apply (clarsimp simp: pt_lookup_slot_def)
apply (frule pt_lookup_slot_from_level_is_subject)
apply (fastforce intro: valid_arch_state_asid_table)+

apply (clarsimp simp: vspace_for_asid_def)
apply (fastforce simp: vs_lookup_table_def obind_def split: option.splits)
apply clarsimp
apply clarsimp
prefer 2
apply clarsimp

apply (erule (1) is_subject_asid_trans)

apply (prop_tac "\<exists>pool_ptr pool. asid_table s (asid_high_bits_of asid) = Some pool_ptr \<and>
asid_pools_of s pool_ptr = Some pool")
apply (simp add: vspace_for_asid_def obind_def pool_for_asid_def
vspace_for_pool_def
 split: option.splits)

apply (clarsimp simp: pas_refined_def)
apply (erule subsetD) back
apply (rule sata_asid_lookup)
apply simp

apply (simp add: state_vrefs_def)

apply (rule exI)
apply (rule conjI)
apply (rule exI, rule exI, rule conjI, rule refl)

apply (rule_tac x=asid_pool_level in exI)
apply (rule_tac x=asid in exI)
apply (rule_tac x=vptr in exI)
apply (rule conjI)
apply (clarsimp simp: vs_lookup_table_def obind_def split: option.splits)
apply (rule conjI)
apply (clarsimp simp: vspace_for_asid_def)
apply clarsimp
apply (rule conjI)
apply (rule refl)
apply (clarsimp simp: vspace_for_asid_def pool_for_asid_def)
apply (clarsimp simp: vspace_for_asid_def)

apply (clarsimp simp: opt_map_def split: option.splits)
apply simp

apply (clarsimp simp: vs_refs_aux_def graph_of_def)
apply (clarsimp simp: vspace_for_asid_def obind_def vspace_for_pool_def
pool_for_asid_def
opt_map_def map_set_in
split: option.splits)
apply (rule exI)
apply auto

apply (subst ucast_up_ucast[symmetric])
prefer 2
apply (subst asid_low_bits_of_mask_eq)
apply simp
  apply (simp add: is_up_def source_size_def target_size_def word_size)
  done

(*

(* FIXME: CLAG *)
lemmas do_machine_op_bind =
  submonad_bind [OF submonad_do_machine_op submonad_do_machine_op submonad_do_machine_op]

lemmas do_flush_defs =
  cleanCacheRange_RAM_def cleanCacheRange_PoC_def cleanCacheRange_PoU_def branchFlushRange_def
  invalidateCacheRange_RAM_def invalidateCacheRange_I_def cleanInvalidateCacheRange_RAM_def

lemma do_flush_respects[wp]:
  "do_machine_op (do_flush typ start end pstart) \<lbrace>integrity aag X st\<rbrace>"
  by (cases "typ"; wpsimp wp: dmo_no_mem_respects simp: do_flush_def cache_machine_op_defs do_flush_defs)

lemma invalidate_tlb_by_asid_respects[wp]:
  "invalidate_tlb_by_asid asid \<lbrace>integrity aag X st\<rbrace>"
  unfolding invalidate_tlb_by_asid_def
  by (wpsimp wp: dmo_no_mem_respects simp: invalidateLocalTLB_ASID_def)

lemma invalidate_tlb_by_asid_pas_refined[wp]:
  "invalidate_tlb_by_asid asid \<lbrace>pas_refined aag\<rbrace>"
  by (wpsimp wp: dmo_no_mem_respects simp: invalidate_tlb_by_asid_def invalidateLocalTLB_ASID_def)

*)

lemma perform_page_invocation_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and K (authorised_page_inv aag pgi)
                       and valid_page_inv pgi and valid_vspace_objs
                       and pspace_aligned and valid_vspace_objs and valid_arch_state
                       and is_subject aag  \<circ> cur_thread\<rbrace>
   perform_page_invocation pgi
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
proof -
  (* does not work as elim rule with clarsimp, which hammers Ball in concl. *)
  have set_tl_subset_mp: "\<And>xs a. a \<in> set (tl xs) \<Longrightarrow> a \<in> set xs" by (case_tac xs; clarsimp)
(*
  have hd_valid_slots:
    "\<And>a xs s. valid_slots (Inl (a, xs)) s \<Longrightarrow> hd xs \<in> set xs"
    "\<And>a xs s. valid_slots (Inr (a, xs)) s \<Longrightarrow> hd xs \<in> set xs"
    by (simp_all add: valid_slots_def)
*)
  show ?thesis
  apply (simp add: perform_page_invocation_def mapM_discarded swp_def
                   valid_page_inv_def valid_unmap_def
                   authorised_page_inv_def authorised_slots_def
perform_pg_inv_map_def perform_pg_inv_unmap_def
sfence_def
            split: page_invocation.split sum.split
                   arch_cap.split option.split,
         safe)
        apply (wp set_cap_integrity_autarch unmap_page_respects
                  mapM_x_and_const_wp[OF store_pte_respects] store_pte_respects
               | elim conjE
               | clarsimp dest!: set_tl_subset_mp
               | wpc )+



   apply (clarsimp simp: cte_wp_at_caps_of_state cap_rights_update_def
                         acap_rights_update_def update_map_data_def
                         valid_page_inv_def valid_cap_simps
                  dest!: cap_master_cap_eqDs)

apply (rule conjI)
prefer 2

apply (case_tac m; clarsimp)
apply (clarsimp simp: valid_arch_cap_def wellformed_mapdata_def split: if_splits)
apply (case_tac m; clarsimp)
apply (clarsimp simp: aag_cap_auth_def)

apply (prop_tac "a \<in> acap_asid' (FrameCap r R sz dev (Some (a,b)))")
apply (clarsimp)
apply (drule (1) sata_asid[where aag=aag])
apply (clarsimp simp: pas_refined_def)
apply (drule (1) subsetD)
apply (fastforce dest: aag_wellformed_Control)
apply (simp add: perform_pg_inv_get_addr_def)
    apply (wpsimp wp: set_mrs_integrity_autarch set_message_info_integrity_autarch
                simp: ipc_buffer_has_auth_def)+
  done
qed

(*

(* FIXME MOVE *)
crunch cdt[wp]: unmap_page "\<lambda>s. P (cdt s)"
  (simp: crunch_simps wp: crunch_wps)

lemma perform_page_invocation_pas_refined [wp]:
  "\<lbrace>pas_refined aag and K (authorised_page_inv aag pgi) and valid_page_inv pgi\<rbrace>
   perform_page_invocation pgi
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: perform_page_invocation_def mapM_discarded valid_page_inv_def valid_unmap_def
                   swp_def authorised_page_inv_def authorised_slots_def
             cong: page_invocation.case_cong sum.case_cong)
  apply (rule hoare_pre)
   apply wpc
      apply (wp set_cap_pas_refined unmap_page_pas_refined case_sum_wp case_prod_wp get_cap_wp
                mapM_x_and_const_wp[OF store_pte_pas_refined] hoare_vcg_all_lift
                mapM_x_and_const_wp[OF store_pde_pas_refined] hoare_vcg_const_imp_lift
             | (wp hoare_vcg_imp_lift, unfold disj_not1)
             | strengthen clas_update_map_data_strg
             | wpc | wps | simp)+
  apply (case_tac pgi)
      apply ((force simp: valid_slots_def pte_ref_def cte_wp_at_caps_of_state
                          is_transferable_is_arch_update[symmetric]
                          pde_ref2_def auth_graph_map_mem pas_refined_refl
                   split: sum.splits)+)[2]
    apply (clarsimp simp: cte_wp_at_caps_of_state is_transferable_is_arch_update[symmetric]
                          pte_ref_def pde_ref2_def is_cap_simps is_pg_cap_def)
    apply (frule(1) cap_cur_auth_caps_of_state, simp)
    apply (intro impI conjI;
           clarsimp; (* NB: for speed *)
           clarsimp simp: update_map_data_def clas_no_asid aag_cap_auth_def
                          cap_auth_conferred_def arch_cap_auth_conferred_def
                          vspace_cap_rights_to_auth_def cli_no_irqs is_pg_cap_def
                          pte_ref_def[simplified aag_cap_auth_def])+
  done


*)

definition authorised_asid_control_inv :: "'a PAS \<Rightarrow> asid_control_invocation \<Rightarrow> bool" where
 "authorised_asid_control_inv aag aci \<equiv>
  case aci of MakePool frame slot parent base \<Rightarrow>
    is_subject aag (fst slot) \<and> is_aligned frame pageBits \<and>
    (\<forall>asid. is_subject_asid aag asid) \<and> is_subject aag (fst parent) \<and>
            (\<forall>x \<in> {frame..frame + 2 ^ pageBits - 1}. is_subject aag x)"


lemma integrity_asid_table_entry_update':
  "\<lbrakk> integrity aag X st s; atable = riscv_asid_table (arch_state s);
     (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of asid
             \<longrightarrow> is_subject_asid aag asid') \<rbrakk>
     \<Longrightarrow> integrity aag X st (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table :=
                                                          \<lambda>a. if a = asid_high_bits_of asid
                                                              then v
                                                              else atable a\<rparr>\<rparr>)"
  by (clarsimp simp: integrity_def)


lemma asid_table_entry_update_integrity[wp]:
 "\<lbrace>integrity aag X st and (\<lambda> s. atable = riscv_asid_table (arch_state s)) and
   K (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of asid
              \<longrightarrow> is_subject_asid aag asid')\<rbrace>
  modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := atable(asid_high_bits_of asid := v)\<rparr>\<rparr>)
  \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (wp | simp)+
  apply (blast intro: integrity_asid_table_entry_update')
  done

lemma perform_asid_control_invocation_respects:
  "\<lbrace>integrity aag X st and invs and valid_aci aci and K (authorised_asid_control_inv aag aci)\<rbrace>
   perform_asid_control_invocation aci
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: perform_asid_control_invocation_def)
  apply (rule hoare_pre)
   apply (wpc, simp)
   apply_trace (wpsimp wp: set_cap_integrity_autarch cap_insert_integrity_autarch
                     retype_region_integrity[where sz=12] static_imp_wp
delete_objects_valid_vspace_objs delete_objects_valid_arch_state
)
  apply (clarsimp simp: authorised_asid_control_inv_def
                        ptr_range_def page_bits_def add.commute
                        range_cover_def obj_bits_api_def default_arch_object_def
                        pageBits_def word_bits_def)
  apply (subst is_aligned_neg_mask_eq[THEN sym], assumption)
  apply (simp add: and_mask_eq_iff_shiftr_0 mask_zero)
apply (intro conjI)
apply (clarsimp simp: word_size_bits_def)
apply clarsimp

apply (clarsimp simp: valid_aci_def)
apply (rule_tac x=aa in exI)
apply (rule_tac x=ba in exI)

apply (erule cte_wp_at_weakenE)
apply (clarsimp simp: descendants_range_def pageBits_def)
  done

(*

lemma pas_refined_set_asid_strg:
  "pas_refined aag s \<and> is_subject aag pool \<and>
   (\<forall>asid. asid_high_bits_of asid = base \<longrightarrow> is_subject_asid aag asid)
   \<longrightarrow> pas_refined aag (s\<lparr>arch_state :=
                          arch_state s\<lparr>arm_asid_table := (arm_asid_table (arch_state s))(base \<mapsto> pool)\<rparr>\<rparr>)"
  apply (clarsimp simp: pas_refined_def state_objs_to_policy_def)
  apply (erule state_asids_to_policy_aux.cases, simp_all split: if_split_asm)
      apply (auto intro: state_asids_to_policy_aux.intros auth_graph_map_memI[OF sbta_vref]
                 intro!: pas_refined_refl[simplified pas_refined_def state_objs_to_policy_def])
  done

lemma perform_asid_control_invocation_pas_refined [wp]:
  "\<lbrace>pas_refined aag and pas_cur_domain aag and invs and valid_aci aci and ct_active
                    and K (authorised_asid_control_inv aag aci)\<rbrace>
   perform_asid_control_invocation aci
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: perform_asid_control_invocation_def)
  apply (rule hoare_pre)
   apply (wp cap_insert_pas_refined' static_imp_wp
          | strengthen pas_refined_set_asid_strg
          | wpc
          | simp add: delete_objects_def2 fun_upd_def[symmetric])+
      apply (wp retype_region_pas_refined'[where sz=pageBits]
                hoare_vcg_ex_lift hoare_vcg_all_lift static_imp_wp hoare_wp_combs hoare_drop_imp
                retype_region_invs_extras(4)[where sz = pageBits]
             | simp add: do_machine_op_def split_def cte_wp_at_neg2)+
      apply (wp retype_region_cte_at_other'[where sz=pageBits]
                max_index_upd_invs_simple max_index_upd_caps_overlap_reserved
                hoare_vcg_ex_lift set_cap_cte_wp_at hoare_vcg_disj_lift set_free_index_valid_pspace
                set_cap_descendants_range_in set_cap_no_overlap get_cap_wp set_cap_caps_no_overlap
                hoare_vcg_all_lift static_imp_wp retype_region_invs_extras
                set_cap_pas_refined_not_transferable
             | simp add: do_machine_op_def split_def cte_wp_at_neg2 region_in_kernel_window_def)+
   apply (rename_tac frame slot parent base cap)
   apply (case_tac slot, rename_tac slot_ptr slot_idx)
   apply (case_tac parent, rename_tac parent_ptr parent_idx)
   apply (rule_tac Q="\<lambda>rv s.
             (\<exists>idx. cte_wp_at ((=) (UntypedCap False frame pageBits idx)) parent s) \<and>
             (\<forall>x\<in>ptr_range frame pageBits. is_subject aag x) \<and>
             pas_refined aag s \<and>
             pas_cur_domain aag s \<and>
             pspace_no_overlap_range_cover frame pageBits s \<and>
             invs s \<and>
             descendants_range_in
               {frame..(frame && ~~ mask pageBits) + 2 ^ pageBits - 1} parent s \<and>
             range_cover frame pageBits
               (obj_bits_api (ArchObject ASIDPoolObj) 0) (Suc 0) \<and>
             is_subject aag slot_ptr \<and>
             is_subject aag parent_ptr \<and>
             pas_cap_cur_auth aag (ArchObjectCap (ASIDPoolCap frame base)) \<and>
             is_subject aag frame \<and>
             (\<forall>x. asid_high_bits_of x = asid_high_bits_of base \<longrightarrow>
                 is_subject_asid aag x)"
             in hoare_strengthen_post)
    apply (simp add: page_bits_def)
    apply (wp add: delete_objects_pspace_no_overlap hoare_vcg_ex_lift
                   delete_objects_descendants_range_in delete_objects_invs_ex
                   delete_objects_pas_refined
              del: Untyped_AI.delete_objects_pspace_no_overlap
           | simp add: page_bits_def)+
   apply clarsimp
   apply (rename_tac s idx)
   apply (frule untyped_cap_aligned, simp add: invs_valid_objs)
   apply (clarsimp simp: cte_wp_at_def aag_cap_auth_def ptr_range_def pas_refined_refl
                         cap_links_asid_slot_def cap_links_irq_def
                         obj_bits_api_def default_arch_object_def retype_addrs_def)
   apply (rule conjI, force intro: descendants_range_caps_no_overlapI
                             simp: cte_wp_at_def)
   apply (rule conjI)
    apply (cut_tac s=s and ptr="(parent_ptr, parent_idx)" in cap_refs_in_kernel_windowD)
      apply ((fastforce simp add: caps_of_state_def cap_range_def)+)[3]
   apply (rule conjI, force simp: field_simps)
   apply (rule conjI, fastforce)
   apply (fastforce dest: caps_of_state_valid
                    simp: caps_of_state_def free_index_of_def max_free_index_def valid_cap_def)
  apply (clarsimp simp: valid_aci_def authorised_asid_control_inv_def)
  apply (rename_tac frame slot_ptr slot_idx parent_ptr parent_idx base)
  apply (subgoal_tac "is_aligned frame pageBits")
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (rule conjI)
    apply (drule untyped_slots_not_in_untyped_range)
         apply (erule empty_descendants_range_in)
        apply (simp add: cte_wp_at_caps_of_state)
       apply simp
      apply (rule refl)
     apply (rule subset_refl)
    apply (simp add: page_bits_def)
   apply (clarsimp simp: ptr_range_def invs_psp_aligned invs_valid_objs
                         descendants_range_def2 empty_descendants_range_in page_bits_def)
   apply ((strengthen refl | simp)+)?
   apply (rule conjI, fastforce)
   apply (rule conjI, fastforce intro: empty_descendants_range_in)
   apply (rule conjI)
    apply (clarsimp simp: range_cover_def obj_bits_api_def default_arch_object_def)
    apply (subst is_aligned_neg_mask_eq[THEN sym], assumption)
    apply (simp add: and_mask_eq_iff_shiftr_0 pageBits_def mask_zero)
   apply (clarsimp simp: aag_cap_auth_def pas_refined_refl)
   apply (drule_tac x=frame in bspec)
    apply (simp add: is_aligned_no_overflow)
   apply (clarsimp simp: pas_refined_refl cap_links_asid_slot_def
                         label_owns_asid_slot_def cap_links_irq_def)
  apply (fastforce dest: cte_wp_at_valid_objs_valid_cap simp: valid_cap_def cap_aligned_def)
  done

*)

definition authorised_asid_pool_inv :: "'a PAS \<Rightarrow> asid_pool_invocation \<Rightarrow> bool" where
 "authorised_asid_pool_inv aag api \<equiv>
  case api of Assign asid pool_ptr ct_slot \<Rightarrow>
    is_subject aag pool_ptr \<and> is_subject aag (fst ct_slot) \<and> asid \<noteq> 0 \<and>
    (\<forall>asid'. asid_high_bits_of asid' = asid_high_bits_of asid \<and> asid' \<noteq> 0
             \<longrightarrow> is_subject_asid aag asid')"

(*
(* Borrowed from part of copy_global_mappings_nonempty_table in Untyped_R.thy *)
lemma copy_global_mappings_index_subset:
  "set [pt_index max_pt_level pptr_base .e. 2 ^ ptTranslationBits - 1] \<subseteq> {x. \<exists>y. x = y >> 20}"
  apply clarsimp
  apply (rule_tac x="x << 20" in exI)
  apply (subst shiftl_shiftr1, simp)
  apply (simp add: word_size)
  apply (rule sym, rule less_mask_eq)
  apply (simp add: word_leq_minus_one_le ptTranslationBits_def pageBits_def)
  done
*)

(*
lemma pd_shifting':
   "is_aligned pd pd_bits \<Longrightarrow>
    (pd + (vptr >> 20 << 2) && ~~ mask pd_bits) = (pd::word32)"
  apply (simp add: pd_bits_def pageBits_def)
  apply (rule word_eqI[rule_format])
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size nth_shiftr nth_shiftl is_aligned_nth)
   apply (erule_tac x=na in allE)
   apply (simp add: linorder_not_less)
   apply (drule test_bit_size)+
   apply (simp add: word_size)
  apply (clarsimp simp: word_size nth_shiftr nth_shiftl is_aligned_nth
                        word_ops_nth_size pd_bits_def linorder_not_less)
  apply (rule iffI)
   apply clarsimp
   apply (drule test_bit_size)+
   apply (simp add: word_size)
  apply clarsimp
  apply (erule_tac x=n in allE)
  apply simp
  done
*)


lemma pt_slot_offset_id':
  "is_aligned pt_ptr pt_bits \<Longrightarrow>
mask pt_bits && (xa << pte_bits) = xa << pte_bits \<Longrightarrow>
table_base (pt_ptr + (xa << pte_bits)) = pt_ptr"
  apply (simp add: pt_slot_offset_def is_aligned_mask_out_add_eq mask_eq_x_eq_0[symmetric])
apply (simp add: pt_index_def pt_bits_def table_size_def shiftl_over_and_dist mask_shiftl_decompose
                word_bool_alg.conj_ac)
done

lemma copy_global_mappings_integrity:
  "\<lbrace>integrity aag X st and K (is_aligned x pt_bits \<and> is_subject aag x)\<rbrace>
       copy_global_mappings x
       \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: copy_global_mappings_def)
  apply (wp mapM_x_wp[OF _ subset_refl] store_pte_respects)
apply (simp only: pt_index_def)
apply (subst pt_slot_offset_id')
apply simp
apply (clarsimp simp: pte_bits_def word_size_bits_def pt_bits_def table_size_def ptTranslationBits_def mask_def)
apply (word_bitwise)
apply auto[1]
apply clarsimp
   apply wpsimp+
  done

thm valid_arch_inv_def
lemma perform_asid_pool_invocation_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs and valid_apinv api and K (authorised_asid_pool_inv aag api)\<rbrace>
   perform_asid_pool_invocation api
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (unfold perform_asid_pool_invocation_def store_asid_pool_entry_def)
  apply (wpsimp wp: set_asid_pool_integrity_autarch get_cap_wp set_cap_integrity_autarch
copy_global_mappings_integrity
hoare_drop_imps
)
  apply (auto iff: authorised_asid_pool_inv_def)
defer

thm valid_apinv_def
apply (clarsimp simp: valid_apinv_def)
apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)
apply (case_tac m; clarsimp)

apply (frule_tac ptr="(a,b)" in sbta_caps)
apply simp
apply (simp add: cap_auth_conferred_def arch_cap_auth_conferred_def)
apply (erule (1) is_subject_trans) back
apply (fastforce simp: pas_refined_def auth_graph_map_def state_objs_to_policy_def)


apply (clarsimp simp: valid_apinv_def)
apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)
apply (case_tac m; clarsimp)
apply (rule_tac s=s in is_aligned_pt)
apply (frule (1) caps_of_state_valid)
apply (clarsimp simp: valid_cap_def)
apply fastforce
done

(*

lemma asid_pool_into_aag:
  "\<lbrakk> kheap s p = Some (ArchObj (ASIDPool pool)); pool r = Some p'; pas_refined aag s \<rbrakk>
     \<Longrightarrow> abs_has_auth_to aag Control p p'"
  apply (rule pas_refined_mem [rotated], assumption)
  apply (rule sta_vref)
  apply (fastforce simp: state_vrefs_def vs_refs_no_global_pts_def intro!: graph_ofI)
  done

lemma asid_pool_uniqueness:
  "\<lbrakk> ([VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> p) s;
     arm_asid_table (arch_state s) (asid_high_bits_of asid') = Some p;
     invs s; \<forall>pt. \<not> ko_at (ArchObj (PageTable pt)) p s \<rbrakk>
     \<Longrightarrow> asid_high_bits_of asid' = asid_high_bits_of asid"
  apply (drule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], clarsimp)
  apply (drule vs_lookup_atI, drule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], clarsimp)
  apply (clarsimp dest!: obj_ref_elemD)
  apply (drule(1) unique_table_refsD[where cps="caps_of_state s", rotated])
    apply simp
   apply (clarsimp simp: vs_cap_ref_def table_cap_ref_def up_ucast_inj_eq
                  split: vmpage_size.splits option.splits cap.splits arch_cap.splits)+
  done

lemma perform_asid_pool_invocation_pas_refined [wp]:
  "\<lbrace>pas_refined aag and invs and valid_apinv api and K (authorised_asid_pool_inv aag api)\<rbrace>
   perform_asid_pool_invocation api
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: perform_asid_pool_invocation_def)
  apply (rule hoare_pre)
  apply (wp get_cap_auth_wp[where aag = aag] set_cap_pas_refined_not_transferable | wpc)+
  apply (clarsimp simp: authorised_asid_pool_inv_def cap_links_asid_slot_def
                        is_subject_asid_into_loas aag_cap_auth_def)
  apply (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def
                        is_cap_simps is_page_cap_def auth_graph_map_mem
                        pas_refined_all_auth_is_owns pas_refined_refl cli_no_irqs
                        cte_wp_at_caps_of_state
                 dest!: graph_ofD)
  apply (clarsimp split: if_split_asm)
   apply (clarsimp simp add: pas_refined_refl auth_graph_map_def2
                             mask_asid_low_bits_ucast_ucast[symmetric]
                             valid_apinv_def obj_at_def)
   apply (drule(2) asid_pool_uniqueness)
    apply (simp add: obj_at_def)
   apply (case_tac "asid = 0"; simp add: pas_refined_refl)
   apply (simp add: asid_low_high_bits[rotated, OF arg_cong[where f=ucast]])
  apply (clarsimp simp: obj_at_def)
  apply (frule (2) asid_pool_into_aag)
  apply (drule kheap_eq_state_vrefsD)
  apply (clarsimp simp: auth_graph_map_def2 pas_refined_refl)
  apply (clarsimp simp: pas_refined_def vs_refs_no_global_pts_def)
  apply (erule subsetD, erule state_asids_to_policy_aux.intros,
         simp add: split_def, rule image_eqI[rotated], erule graph_ofI)
  apply simp
  done

definition authorised_page_directory_inv :: "'a PAS \<Rightarrow> page_directory_invocation \<Rightarrow> bool" where
  "authorised_page_directory_inv aag pdi \<equiv> True"

*)

definition authorised_arch_inv :: "'a PAS \<Rightarrow> arch_invocation \<Rightarrow> bool" where
 "authorised_arch_inv aag ai \<equiv> case ai of
     InvokePageTable pti \<Rightarrow> authorised_page_table_inv aag pti
   | InvokePage pgi \<Rightarrow> authorised_page_inv aag pgi
   | InvokeASIDControl aci \<Rightarrow> authorised_asid_control_inv aag aci
   | InvokeASIDPool api \<Rightarrow> authorised_asid_pool_inv aag api"

(*
crunch respects [wp]: perform_page_directory_invocation "integrity aag X st"
  (ignore: do_machine_op)

crunch pas_refined [wp]: perform_page_directory_invocation "pas_refined aag"
*)

lemma invoke_arch_respects:
  "\<lbrace>integrity aag X st and K (authorised_arch_inv aag ai) and
    pas_refined aag and invs and valid_arch_inv ai and is_subject aag \<circ> cur_thread\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: arch_perform_invocation_def)
  apply (wpsimp wp: perform_page_table_invocation_respects perform_page_invocation_respects
                    perform_asid_control_invocation_respects perform_asid_pool_invocation_respects)
  apply (auto simp: authorised_arch_inv_def valid_arch_inv_def)
  done


thm
perform_page_table_invocation_pas_refined
perform_page_invocation_pas_refined
perform_asid_control_invocation_pas_refined
perform_asid_pool_invocation_pas_refined


lemma invoke_arch_pas_refined:
  "\<lbrace>pas_refined aag and pas_cur_domain aag and invs and ct_active
                    and valid_arch_inv ai and K (authorised_arch_inv aag ai)\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: arch_perform_invocation_def valid_arch_inv_def)
  apply (rule hoare_pre)
  apply (wp | wpc)+
sorry (*
  apply (fastforce simp add: authorised_arch_inv_def)
  done *)

end (*

lemma create_mapping_entries_authorised_slots [wp]:
  "\<lbrace>\<exists>\<rhd> pd and invs and pas_refined aag and
    K (is_subject aag pd \<and> is_aligned pd pd_bits \<and>
       vmsz_aligned vptr vmpage_size \<and> vptr < kernel_base \<and>
       (\<forall>a\<in>vspace_cap_rights_to_auth rights.
          \<forall>p\<in>ptr_range (ptrFromPAddr base) (pageBitsForSize vmpage_size). aag_has_auth_to aag a p))\<rbrace>
   create_mapping_entries base vptr vmpage_size rights attrib pd
   \<lbrace>\<lambda>rv _. authorised_slots aag rv\<rbrace>, -"
  unfolding authorised_slots_def
  apply (rule hoare_gen_asmE)
  apply (cases vmpage_size)
     apply (wp lookup_pt_slot_authorised | simp add: pte_ref_simps | fold validE_R_def)+
     apply (auto simp: pd_bits_def pageBits_def)[1]
    apply (wp lookup_pt_slot_authorised2
           | simp add: pte_ref_simps largePagePTE_offsets_def
           | fold validE_R_def)+
    apply (auto simp: pd_bits_def pageBits_def vmsz_aligned_def)[1]
   apply (wp | simp)+
   apply (auto simp: pde_ref2_def lookup_pd_slot_pd)[1]
  apply (wp | simp add: superSectionPDE_offsets_def)+
  apply (auto simp: pde_ref2_def vmsz_aligned_def lookup_pd_slot_add_eq)
  done

lemma pageBitsForSize_le_t29:
  "pageBitsForSize sz \<le> 29"
  by (cases sz, simp_all)

lemma x_t2n_sub_1_neg_mask:
  "\<lbrakk> is_aligned x n; n \<le> m \<rbrakk>
     \<Longrightarrow> x + 2 ^ n - 1 && ~~ mask m = x && ~~ mask m"
  apply (erule is_aligned_get_word_bits)
   apply (rule trans, rule mask_lower_twice[symmetric], assumption)
   apply (subst add_diff_eq[symmetric], subst is_aligned_add_helper, assumption)
    apply simp+
  apply (simp add: mask_def power_overflow)
  done

lemmas vmsz_aligned_t2n_neg_mask =
  x_t2n_sub_1_neg_mask[OF _ pageBitsForSize_le_t29, folded vmsz_aligned_def]

lemma decode_arch_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                  aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                  is_subject aag (fst slot) \<and>
                  (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v))\<rbrace>
   arch_decode_invocation label msg x_slot slot cap excaps
   \<lbrace>\<lambda>rv _. authorised_arch_inv aag rv\<rbrace>,-"
  unfolding arch_decode_invocation_def authorised_arch_inv_def aag_cap_auth_def
  apply (rule hoare_pre)
   apply (simp add: split_def Let_def split del: if_split
              cong: cap.case_cong arch_cap.case_cong if_cong option.case_cong)
   apply (wp select_wp whenE_throwError_wp check_vp_wpR
             find_pd_for_asid_authority2
          | wpc
          | simp add: authorised_asid_control_inv_def authorised_page_inv_def
                      authorised_page_directory_inv_def
                 del: hoare_True_E_R
                 split del: if_split)+
  apply (clarsimp simp: authorised_asid_pool_inv_def authorised_page_table_inv_def
                        neq_Nil_conv invs_psp_aligned invs_vspace_objs cli_no_irqs)
  apply (drule cte_wp_valid_cap, clarsimp+)
  apply (cases cap; simp)
      \<comment> \<open>asid pool\<close>
     apply (find_goal \<open>match premises in "cap = ASIDPoolCap _ _" \<Rightarrow> succeed\<close>)
     subgoal for s obj_ref asid
       by (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def is_page_cap_def
                          pas_refined_all_auth_is_owns asid_high_bits_of_add_ucast valid_cap_simps)
     \<comment> \<open>ControlCap\<close>
    apply (find_goal \<open>match premises in "cap = ASIDControlCap" \<Rightarrow> succeed\<close>)
    subgoal
      apply (clarsimp simp: neq_Nil_conv split_def valid_cap_simps)
      apply (cases excaps, solves simp)
      apply (clarsimp simp: neq_Nil_conv aag_has_Control_iff_owns)
      apply (drule cte_wp_at_valid_objs_valid_cap, clarsimp)
      apply (clarsimp simp: valid_cap_def cap_aligned_def)
      apply (clarsimp simp: is_cap_simps cap_auth_conferred_def
                            pas_refined_all_auth_is_owns aag_cap_auth_def)
      done
   \<comment> \<open>PageCap\<close>
   apply (find_goal \<open>match premises in "cap = PageCap _ _ _ _ _" \<Rightarrow> succeed\<close>)
   subgoal for s is_dev obj_ref cap_rights vmpage_size mapping
     apply (clarsimp simp: valid_cap_simps cli_no_irqs)
     apply (cases "invocation_type label"; (solves \<open>simp\<close>)?)
     apply (find_goal \<open>match premises in "_ = ArchInvocationLabel _" \<Rightarrow> succeed\<close>)
     apply (rename_tac archlabel)
     apply (case_tac archlabel; (solves \<open>simp\<close>)?)
       \<comment> \<open>Map\<close>
      apply (find_goal \<open>match premises in "_ = ARMPageMap" \<Rightarrow> succeed\<close>)
      subgoal
       apply (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def is_cap_simps is_page_cap_def
                             pas_refined_all_auth_is_owns)
       apply (rule conjI)
        apply (clarsimp simp: is_page_cap_def pas_refined_all_auth_is_owns
                              aag_cap_auth_def cli_no_irqs cap_links_asid_slot_def)
        apply (simp only: linorder_not_le kernel_base_less_observation
                          vmsz_aligned_t2n_neg_mask simp_thms)
         apply (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def
                               vspace_cap_rights_to_auth_def mask_vm_rights_def
                               validate_vm_rights_def vm_read_only_def vm_kernel_only_def)
        apply clarsimp
        apply (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def aag_cap_auth_def
                               cli_no_irqs vspace_cap_rights_to_auth_def mask_vm_rights_def
                              validate_vm_rights_def vm_read_only_def vm_kernel_only_def)
       done
     \<comment> \<open>Unmap\<close>
     subgoal by (simp add: aag_cap_auth_def cli_no_irqs)
     done
  \<comment> \<open>PageTableCap\<close>
  apply (find_goal \<open>match premises in "cap = PageTableCap _ _" \<Rightarrow> succeed\<close>)
  subgoal for s word option
    apply (cases "invocation_type label"; (solves \<open>simp\<close>)?)
    apply (find_goal \<open>match premises in "_ = ArchInvocationLabel _" \<Rightarrow> succeed\<close>)
    apply (rename_tac archlabel)
    apply (case_tac archlabel; (solves \<open>simp\<close>)?)
     \<comment> \<open>PTMap\<close>
     apply (find_goal \<open>match premises in "_ = ARMPageTableMap" \<Rightarrow> succeed\<close>)
     apply (clarsimp simp: aag_cap_auth_def cli_no_irqs cap_links_asid_slot_def
                           cap_auth_conferred_def arch_cap_auth_conferred_def is_page_cap_def
                           pde_ref2_def pas_refined_all_auth_is_owns pas_refined_refl
                           pd_shifting[folded pd_bits_14])
    \<comment> \<open>Unmap\<close>
    apply (find_goal \<open>match premises in "_ = ARMPageTableUnmap" \<Rightarrow> succeed\<close>)
    subgoal
      apply (clarsimp simp: aag_cap_auth_def cli_no_irqs cap_links_asid_slot_def
                            cap_auth_conferred_def arch_cap_auth_conferred_def is_page_cap_def
                            pde_ref2_def pas_refined_all_auth_is_owns pas_refined_refl)
      apply (subgoal_tac "x && ~~ mask pt_bits = word")
       apply simp
      apply (clarsimp simp: valid_cap_simps cap_aligned_def split: if_split_asm)
      apply (subst (asm) upto_enum_step_subtract)
      apply (subgoal_tac "is_aligned word pt_bits")
       apply (simp add: is_aligned_no_overflow)
      apply (simp add: pt_bits_def pageBits_def)
      apply simp
      apply (subst (asm) upto_enum_step_red [where us = 2, simplified])
      apply (simp add: pt_bits_def pageBits_def word_bits_conv)
      apply (simp add: pt_bits_def pageBits_def word_bits_conv)
      apply clarsimp
      apply (subst is_aligned_add_helper)
      apply (simp add: pt_bits_def pageBits_def)
      apply (erule word_less_power_trans_ofnat [where k = 2, simplified])
        apply (simp add: pt_bits_def pageBits_def)
       apply (simp add: pt_bits_def pageBits_def word_bits_conv)
      apply simp
      done
    done
  done

crunch pas_refined[wp]: invalidate_asid_entry "pas_refined aag"
  (wp: crunch_wps simp: crunch_simps)

crunch pas_refined[wp]: flush_space "pas_refined aag"
  (wp: crunch_wps simp: crunch_simps)

lemma delete_asid_pas_refined[wp]:
  "delete_asid asid pd \<lbrace>pas_refined aag\<rbrace>"
  apply (simp add: delete_asid_def)
  apply (wp | wpc)+
  apply (clarsimp simp add: split_def Ball_def obj_at_def)
  apply (rule conjI)
   apply (clarsimp dest!: auth_graph_map_memD graph_ofD)
   apply (erule pas_refined_mem[OF sta_vref, rotated])
   apply (fastforce simp: state_vrefs_def vs_refs_no_global_pts_def
                         image_def graph_of_def split: if_split_asm)
  apply (clarsimp simp: pas_refined_def dest!: graph_ofD)
  apply (erule subsetD, erule state_asids_to_policy_aux.intros)
  apply (fastforce simp: state_vrefs_def vs_refs_no_global_pts_def
                        graph_of_def image_def split: if_split_asm)
  done

lemma delete_asid_pool_pas_refined [wp]:
  "delete_asid_pool param_a param_b \<lbrace>pas_refined aag\<rbrace>"
  unfolding delete_asid_pool_def
  apply (wp | wpc | simp)+
      apply (rule_tac Q = "\<lambda>_ s. pas_refined aag s \<and>
                                 asid_table = arm_asid_table (arch_state s)" in hoare_post_imp)
       apply clarsimp
       apply (erule pas_refined_clear_asid)
      apply (wp mapM_wp' | simp)+
  done

crunch respects[wp]: invalidate_asid_entry "integrity aag X st"

crunch respects[wp]: flush_space "integrity aag X st"
  (ignore: do_machine_op simp: invalidateLocalTLB_ASID_def cleanCaches_PoU_def
           dsb_def clean_D_PoU_def invalidate_I_PoU_def do_machine_op_bind)

lemma delete_asid_pool_respects[wp]:
  "\<lbrace>integrity aag X st and
    K (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of x
               \<longrightarrow> is_subject_asid aag asid')\<rbrace>
   delete_asid_pool x y
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding delete_asid_pool_def
  apply simp
  apply (wp mapM_wp[OF _ subset_refl] | simp)+
  done

lemma set_asid_pool_respects_clear:
  "\<lbrace>integrity aag X st and (\<lambda>s. \<forall>pool'. ko_at (ArchObj (arch_kernel_obj.ASIDPool pool')) ptr s
                                        \<longrightarrow> asid_pool_integrity {pasSubject aag} aag pool' pool)\<rbrace>
   set_asid_pool ptr pool
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: set_object_wp_strong
              simp: obj_at_def a_type_def
             split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm if_splits)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def)
  apply (rule tro_arch; fastforce simp: arch_integrity_obj_atomic.simps)
  done

lemma delete_asid_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs and K (is_subject aag pd)\<rbrace>
   delete_asid asid pd
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (wpsimp wp: set_asid_pool_respects_clear hoare_vcg_all_lift
           simp: obj_at_def pas_refined_refl delete_asid_def asid_pool_integrity_def)

end


context begin interpretation Arch .

requalify_facts
  invoke_arch_pas_refined
  invoke_arch_respects
  decode_arch_invocation_authorised

requalify_consts
  authorised_arch_inv

end

end
