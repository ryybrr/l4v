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

lemma [simp]: "mask 12 >> 3 = (0x1FF :: obj_ref)"
by (clarsimp simp: mask_def)


lemma ucast_thingy:
 "UCAST(64 \<rightarrow> 9) (ptr && mask ptTranslationBits)
\<le> mask ptTranslationBits"
  by (metis AND_twice and_mask_eq_iff_le_mask ucast_and_mask)


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
apply (clarsimp simp: Bex_def)

apply (case_tac "level = max_pt_level"; clarsimp)

prefer 2

apply (rule_tac x="table_index (pt_slot_offset level pt_ptr vref)" in exI)
apply_trace clarsimp

apply (intro conjI)

apply (clarsimp simp: pptr_from_pte_def)
apply (rule refl)
apply (rule refl)

apply (rule_tac x="table_index (pt_slot_offset max_pt_level pt_ptr vref)" in exI)
apply_trace clarsimp

apply (intro conjI)

apply (rule table_index_max_level_slots)
apply clarsimp
  using pts_of_Some pts_of_Some_alignedD apply blast

apply (clarsimp simp: pptr_from_pte_def)

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

thm valid_page_inv_def

lemma "cte_wp_at (is_arch_update (ArchObjectCap acap)) ptr s \<Longrightarrow>
 cte_wp_at is_frame_cap ptr s  \<Longrightarrow>
same_ref (pte,slot) (ArchObjectCap acap) s \<Longrightarrow>
  P"
apply (clarsimp simp: cte_wp_at_caps_of_state)
apply (clarsimp simp: is_arch_update_def)
apply (clarsimp simp: is_frame_cap_def is_FrameCap_def)

apply (clarsimp simp: cap_master_cap_def)
apply (case_tac acap; clarsimp)
apply (clarsimp simp: is_cap_simps)

apply (clarsimp simp: same_ref_def)
oops


term valid_vspace_objs
definition authorised_slots :: "'a PAS \<Rightarrow> pte \<times> obj_ref \<Rightarrow> 's :: state_ext state \<Rightarrow>  bool" where
 "authorised_slots aag m s \<equiv> case m of
    (pte, slot) \<Rightarrow>
      (\<forall>level asid vref x.
vs_lookup_slot level asid vref s = Some (level, slot) \<longrightarrow>
vref \<in> user_region \<longrightarrow>
level \<le> max_pt_level \<longrightarrow>
pte_ref2 level pte = Some x
           \<longrightarrow> (\<forall>a \<in> snd (snd x). \<forall>p \<in> ptr_range (fst x) (fst (snd x)). aag_has_auth_to aag a p)) \<and>
      (is_subject aag (slot && ~~ mask pt_bits))"

(* FIXME ryanb - pass level to authorised slots *)
definition authorised_page_inv :: "'a PAS \<Rightarrow> page_invocation \<Rightarrow> 's :: state_ext state \<Rightarrow>  bool" where
  "authorised_page_inv aag pgi s \<equiv> case pgi of
     PageMap cap ptr slots \<Rightarrow>
       pas_cap_cur_auth aag (ArchObjectCap cap) \<and> is_subject aag (fst ptr) \<and> authorised_slots aag slots s
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

*)

find_theorems store_pte pas_refined


lemma perform_pg_inv_get_addr_pas_refined [wp]:
  "\<lbrace>pas_refined aag and invs\<rbrace>
   perform_pg_inv_get_addr ptr
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
unfolding perform_pg_inv_get_addr_def
apply wpsimp
apply fastforce
done


thm perform_pg_inv_get_addr_def

lemma perform_pg_inv_unmap_pas_refined:
   "\<lbrace>pas_refined aag and invs and valid_page_inv (PageUnmap cap ct_slot)
                     and authorised_page_inv aag (PageUnmap cap ct_slot)\<rbrace>
    perform_pg_inv_unmap cap ct_slot
    \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pg_inv_unmap_def unmap_page_def
  apply (wps | clarsimp simp: conj_ac | wpsimp wp: store_pte_pas_refined set_cap_pas_refined_not_transferable get_cap_wp
  hoare_vcg_all_lift hoare_vcg_imp_lift' store_pte_valid_arch_state_unreachable
  simp: unmap_page_def)+

  apply (strengthen invs_strgs invs_arch_state invs_vspace_objs invs_valid_global_vspace_mappings invs_valid_asid_table)
  apply (clarsimp simp: conj_ac)


  apply (rule conjI)
   apply (fastforce simp: is_FrameCap_def authorised_page_inv_def
                          valid_page_inv_def update_map_data_def cte_wp_at_caps_of_state)
  apply clarsimp
  apply (case_tac "cte_wp_at ((=) x) ct_slot s"; clarsimp)
  apply (clarsimp simp: is_FrameCap_def authorised_page_inv_def valid_page_inv_def
                        valid_arch_cap_def cte_wp_at_caps_of_state update_map_data_def
                        aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                        cap_links_asid_slot_def cap_links_irq_def is_transferable.simps)

  apply (intro conjI; clarsimp)

   apply (frule (1) pt_lookup_slot_vs_lookup_slotI0)
   apply (drule vs_lookup_slot_level)

   apply (case_tac "xc = asid_pool_level")
    apply (fastforce dest: vs_lookup_slot_no_asid)


   apply (frule vs_lookup_slot_table_base)
      apply (fastforce simp: wellformed_mapdata_def)+
   apply (frule vspace_for_asid_vs_lookup)

   apply (prop_tac "vs_lookup_table max_pt_level xa xb s = Some (max_pt_level, x)")
    apply (clarsimp simp: vs_lookup_table_def)

   apply (frule reachable_page_table_not_global)
      apply fastforce
     apply (fastforce simp: wellformed_mapdata_def)
    apply clarsimp
   apply clarsimp


   apply (rule conjI)
    apply (case_tac ct_slot; clarsimp)
    apply (clarsimp simp: wellformed_mapdata_def)
    apply (frule vs_lookup_table_pt_at; clarsimp?)
    apply (drule vs_lookup_table_valid_cap; clarsimp?)
    apply (fastforce simp: valid_cap_def valid_arch_cap_def valid_arch_cap_ref_def obj_at_def
                     dest: caps_of_state_valid split: cap.splits arch_cap.splits)
   apply (clarsimp simp: wellformed_mapdata_def)
  thm vs_lookup_table_vspace[rotated]
   apply (drule (1) vs_lookup_table_vspace)
     apply fastforce
    apply fastforce
   apply clarsimp

   apply (clarsimp simp: vs_lookup_slot_def)
   apply (frule user_region_slots)
   apply (clarsimp simp: pt_slot_offset_def)

   apply (metis (full_types, hide_lams) if_Some_None_eq_None invs_implies(7) pspace_aligned_pts_ofD pt_slot_offset_def pt_slot_offset_offset ptes_of_Some)

  apply (erule_tac x="dev" in allE)
  apply clarsimp
  done




lemma set_cap_vs_lookup_slot[wp]:
  "set_cap param_a param_b \<lbrace>\<lambda>s. P (vs_lookup_slot level asid vref s)\<rbrace> "
apply (clarsimp simp: vs_lookup_slot_def obind_def)
apply (rule hoare_pre)
apply (rule hoare_lift_Pf3[where f="\<lambda>s level asid vref. vs_lookup_table level asid vref s"])
apply (clarsimp split: option.splits)
apply wpsimp
apply wpsimp
apply (auto split: if_splits)
done

crunches set_cap
  for ptes_of[wp]: "\<lambda>s. P (ptes_of s)"
and level_of_table[wp]: "\<lambda>s. P (level_of_table p s)"
 (simp: level_of_table_def)

lemma set_cap_authorised_page_inv[wp]:
  "set_cap param_a param_b \<lbrace>\<lambda>s. P (authorised_page_inv aag (PageMap cap ct_slot (pte,slot)) s)\<rbrace> "
apply (clarsimp simp: authorised_page_inv_def authorised_slots_def)
apply (rule hoare_pre)
apply wps
apply (wpsimp)
apply clarsimp
done

thm same_ref_def
lemma set_cap_same_ref[wp]:
  "set_cap param_a param_b \<lbrace>\<lambda>s. P (same_ref pte_slot cap s)\<rbrace> "
apply (case_tac pte_slot; clarsimp)
apply (clarsimp simp: same_ref_def)
apply (rule hoare_pre)
apply wps
apply wpsimp
apply assumption
done



lemma perform_pg_inv_map_pas_refined:
  "\<lbrace>pas_refined aag and invs and valid_page_inv (PageMap cap ct_slot (pte,slot))
                    and authorised_page_inv aag (PageMap cap ct_slot (pte,slot))\<rbrace>
   perform_pg_inv_map cap ct_slot pte slot
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pg_inv_map_def
  apply wpsimp
    apply (clarsimp simp: pas_refined_def state_objs_to_policy_def)

apply wps
apply wpsimp
apply (subst conj_commute) back
apply (subst conj_commute)
apply clarsimp
apply (rule hoare_vcg_conj_lift)
apply wpsimp
apply (rule state_vrefs_store_NonPageTablePTE_wp')

apply (rule_tac Q="\<lambda>_. invs and pas_refined aag and K (\<not> is_PageTablePTE pte)
and authorised_page_inv aag (PageMap cap ct_slot (pte,slot))
and same_ref (pte,slot) (ArchObjectCap cap)" in hoare_strengthen_post[rotated])
apply (clarsimp simp: pas_refined_def)
apply (rule conjI)
apply clarsimp
apply (intro exI, rule conjI, assumption)
apply clarsimp
apply (rule conjI)
apply clarsimp
apply (erule subsetD) back

apply (erule state_asids_to_policy_aux.cases)
      apply (fastforce dest: sata_asid)
     apply (clarsimp simp: cte_wp_at_caps_of_state)
apply (clarsimp simp only: split: if_splits)
apply (clarsimp simp: vs_refs_aux_def)
apply (erule sata_asid_lookup)
apply assumption
apply (fastforce dest: sata_asidpool)

apply (clarsimp simp: auth_graph_map_def)
apply (clarsimp simp: authorised_page_inv_def)

apply (erule state_bits_to_policy.cases)
apply (fastforce dest: sbta_caps simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_untyped simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_ts simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_bounds simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_cdt simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_cdt_transferable simp: state_objs_to_policy_def)

apply (clarsimp simp only: split: if_split_asm)
prefer 2

apply (erule subsetD)
apply (simp only: state_objs_to_policy_def)
apply (drule sbta_vref)
apply fastforce

apply (clarsimp simp: vs_refs_aux_def)
apply (clarsimp simp: graph_of_def)

apply (case_tac "level \<noteq> max_pt_level \<or> a \<notin> kernel_mapping_slots"; clarsimp simp: word_le_not_less)
apply (subgoal_tac "(pasObjectAbs aag (table_base slot), ba, pasObjectAbs aag ac) \<in> pasPolicy aag")
apply clarsimp
apply (thin_tac "_ \<notin> _")


apply (case_tac "level = asid_pool_level")
apply clarsimp
apply (frule vs_lookup_slot_no_asid)
apply (fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
apply fastforce
apply fastforce
apply fastforce

apply (clarsimp split: if_split_asm)
apply (case_tac pte; clarsimp)
apply (clarsimp simp: pte_ref2_def)
apply (clarsimp simp: authorised_slots_def)

apply (subst (asm) vs_lookup_slot_table_unfold)
apply fastforce
apply fastforce
apply fastforce

apply (erule subsetD)
apply (simp only: state_objs_to_policy_def)
apply clarsimp
apply (rule exI, rule conjI, rule refl)+
apply (rule sbta_vref)
apply (clarsimp simp: state_vrefs_def)
apply (intro exI conjI)
apply (rule refl)
apply assumption
apply (fastforce simp: aobjs_of_Some obj_at_def)
apply fastforce
apply (fastforce simp: vs_refs_aux_def graph_of_def)

apply (clarsimp simp: same_ref_def)

apply (wpsimp wp: arch_update_cap_invs_map set_cap_pas_refined_not_transferable)
apply (clarsimp simp: valid_page_inv_def authorised_page_inv_def)
apply (clarsimp simp: cte_wp_at_caps_of_state is_frame_cap_def is_FrameCap_def)
apply (intro conjI)

apply (clarsimp simp: is_arch_update_def cap_master_cap_def)
apply (case_tac cap; clarsimp)
apply (clarsimp simp: same_ref_def parent_for_refs_def)
  using vs_lookup_slot_unique_level apply blast

apply (clarsimp simp: is_arch_update_def cap_master_cap_def)
apply (case_tac cap; clarsimp)
apply (clarsimp simp: is_arch_cap_def)
apply (drule (1) caps_of_state_valid)
apply (clarsimp simp: valid_arch_cap_def)
apply (clarsimp simp: valid_cap_def cap_aligned_def)

apply fastforce+
done



lemma perform_page_invocation_pas_refined [wp]:
  "\<lbrace>pas_refined aag and invs and authorised_page_inv aag pgi and valid_page_inv pgi\<rbrace>
   perform_page_invocation pgi
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
apply (simp add: perform_page_invocation_def)
apply (wpsimp wp: perform_pg_inv_map_pas_refined perform_pg_inv_unmap_pas_refined)
apply auto
done


(*
lemma "\<lbrace>pas_refined aag and invs and valid_page_inv (PageMap cap ct_slot (pte,slot))
                        and K (authorised_page_inv aag (PageMap cap ct_slot (pte,slot)))\<rbrace>
       perform_pg_inv_map cap ct_slot pte slot
      \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pg_inv_map_def
  apply (rule hoare_gen_asm)
  apply wpsimp
    apply (clarsimp simp: pas_refined_def state_objs_to_policy_def)
   apply (wps | wpsimp wp: state_vrefs_store_NonPageTablePTE_wp' arch_update_cap_invs_map  vs_lookup_slot_lift
                     hoare_vcg_ex_lift hoare_vcg_all_lift hoare_vcg_imp_lift' set_cap_arch_obj_neg set_cap_state_vrefs)+

apply (rule hoare_vcg_conj_lift)

apply (rule_tac Q="\<lambda>_ s. ((\<exists>level. \<exists>\<rhd> (level, table_base slot) s) \<longrightarrow> R s) \<and> (\<not>(\<exists>level. \<exists>\<rhd> (level, table_base slot) s) \<longrightarrow> R s)"
and R="\<lambda>_. R" for R in hoare_strengthen_post[rotated])
apply fastforce

apply (clarsimp cong: conj_cong)
apply (rule hoare_vcg_conj_lift)
apply (rule hoare_vcg_imp_lift')
apply wpsimp
apply (wpsimp wp: set_cap_state_vrefs hoare_vcg_all_lift hoare_vcg_imp_lift')+


apply (rule_tac Q="\<lambda>_ s. ((\<exists>level. \<exists>\<rhd> (level, table_base slot) s) \<longrightarrow> R s) \<and> (\<not>(\<exists>level. \<exists>\<rhd> (level, table_base slot) s) \<longrightarrow> R s)"
and R="\<lambda>_. R" for R in hoare_strengthen_post[rotated])
apply fastforce

apply (clarsimp cong: conj_cong)
apply (rule hoare_vcg_conj_lift)
apply (rule hoare_vcg_imp_lift')
apply wpsimp
apply (wpsimp wp: set_cap_state_vrefs hoare_vcg_all_lift hoare_vcg_imp_lift')+

apply (clarsimp simp: conj_ac)


apply (wps)
apply (wpsimp wp: set_cap.vs_lookup set_cap_state_vrefs)
thm state_vrefs_store_NonPageTablePTE_wp'
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
     vs_lookup_table level asid vptr s = Some (level, pt_ptr);
     level \<le> max_pt_level; vptr \<in> user_region; is_subject aag pt_ptr \<rbrakk>
     \<Longrightarrow> is_subject aag pt"
apply (induct level arbitrary: pt_ptr)
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

apply (case_tac "level = max_pt_level"; clarsimp)

prefer 2

apply (prop_tac "(table_index (pt_slot_offset level pt_ptr vptr), ptrFromPAddr (addr_from_ppn x31), 0, {Control}) \<in>graph_of (pte_ref2 level \<circ> pta)")
apply (clarsimp simp: graph_of_def pte_ref2_def)

apply (rule bexI)
prefer 2
apply assumption
apply clarsimp
apply (rule conjI)
apply (clarsimp simp: pptr_from_pte_def)
apply fastforce


apply (prop_tac "(table_index (pt_slot_offset max_pt_level pt_ptr vptr), ptrFromPAddr (addr_from_ppn x31), 0, {Control}) \<in>graph_of (pte_ref2 max_pt_level \<circ> pta)")
apply (clarsimp simp: graph_of_def pte_ref2_def)

apply (rule bexI)
prefer 2
apply clarsimp
apply (rule conjI)
apply assumption
apply clarsimp
apply (drule table_index_max_level_slots)
prefer 2
apply fastforce
  using aobjs_of_Some pts_of_Some pts_of_Some_alignedD apply blast
apply (clarsimp simp: pptr_from_pte_def)
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
  "\<lbrace>integrity aag X st and pas_refined aag and authorised_page_inv aag pgi
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
    apply (unfold authorised_page_inv_def)
  apply (simp add: perform_page_invocation_def mapM_discarded swp_def
                   valid_page_inv_def valid_unmap_def
                   authorised_page_inv_def authorised_slots_def
perform_pg_inv_map_def perform_pg_inv_unmap_def
sfence_def
            split: page_invocation.split sum.split
                   arch_cap.split option.split,
         safe)
        apply ((wp set_cap_integrity_autarch unmap_page_respects
                  mapM_x_and_const_wp[OF store_pte_respects] store_pte_respects
               | elim conjE
               | clarsimp dest!: set_tl_subset_mp
               | wpc )+)

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

*)

(*
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
apply (clarsimp simp: word_size_bits_def)
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

*)

thm pas_refined_def


lemma state_vrefs_helper_thing:
"\<lbrakk>ako_at (ASIDPool Map.empty) frame s;
          asid_table s (asid_high_bits_of base) = None\<rbrakk>
         \<Longrightarrow> (state_vrefs
                  (s\<lparr>arch_state := arch_state s
                       \<lparr>riscv_asid_table :=
                          \<lambda>a. if a = asid_high_bits_of base then Some frame
                               else asid_table s a\<rparr>\<rparr>)) = state_vrefs s"
apply (rule all_ext)
apply clarsimp
apply safe
prefer 2

apply (subst (asm) state_vrefs_def)
apply clarsimp

apply (clarsimp simp: state_vrefs_def)

apply (rule exI)
apply (rule conjI)
apply (rule_tac x=lvl in exI)

apply (rule_tac x=ao in exI)
apply (rule conjI)
apply (rule refl)
apply (rule_tac x=lvl in exI)
apply (rule_tac x=asid in exI)
apply (drule vs_lookup_level)
apply (rule_tac x=vref in exI)
apply clarsimp
prefer 2
apply clarsimp

apply (clarsimp simp: vs_lookup_table_def obind_def split: option.splits if_splits)
apply (clarsimp simp: pool_for_asid_def)
apply (clarsimp simp: pool_for_asid_def)
apply (fastforce simp: vspace_for_pool_def obind_def split: option.splits)

apply (subst (asm) state_vrefs_def)
apply clarsimp

apply (case_tac "asid_high_bits_of asid = asid_high_bits_of base")
prefer 2

apply (clarsimp simp: vs_lookup_table_def)
apply (clarsimp simp: pool_for_asid_def)

apply (clarsimp split: if_splits)
apply (clarsimp simp: state_vrefs_def)
apply (fastforce simp: vs_lookup_table_def obind_def pool_for_asid_def
                split: option.splits)
apply (clarsimp simp: state_vrefs_def)

apply (intro exI conjI)
apply (rule refl)
apply (clarsimp simp: vs_lookup_table_def obind_def pool_for_asid_def
                split: option.splits)
apply (rule conjI)
apply fastforce
apply clarsimp
apply (rule conjI)
prefer 2
apply clarsimp
apply (rule conjI)
prefer 2
apply clarsimp
apply assumption
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply fastforce

apply (clarsimp simp: vs_lookup_table_def)

apply (case_tac "bot = asid_pool_level")

prefer 2

apply (clarsimp simp: vs_lookup_table_def)
apply (clarsimp simp: pool_for_asid_def)

apply (clarsimp simp: vspace_for_pool_def)
apply (clarsimp simp: asid_pools_of_ko_at obj_at_def)


apply clarsimp

apply (clarsimp simp: pool_for_asid_def)
apply (clarsimp simp: obj_at_def vs_refs_aux_def aobjs_of_Some)
apply (clarsimp simp: authorised_asid_control_inv_def graph_of_def)
done


lemma pas_refined_asid_control_helper:
 "authorised_asid_control_inv aag (MakePool frame slot parent base) \<Longrightarrow>
\<lbrace>\<lambda>s. pas_refined aag s \<and>  ko_at (ArchObj (ASIDPool Map.empty)) frame s
 \<and> asid_table s (asid_high_bits_of base) = None
\<rbrace> do
                                          asid_table <- gets (riscv_asid_table \<circ> arch_state);
                                          asid_table' <- return (asid_table(asid_high_bits_of base \<mapsto> frame));
                                          modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := asid_table'\<rparr>\<rparr>)
od \<lbrace>\<lambda>_ s. pas_refined aag s\<rbrace>"
unfolding pas_refined_def
apply wpsimp

apply (rule conjI)
apply (clarsimp simp: state_objs_to_policy_def)
apply (clarsimp simp: auth_graph_map_def)
apply (erule state_bits_to_policy.cases)

apply (fastforce dest: sbta_caps simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_untyped simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_ts simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_bounds simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_cdt simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_cdt_transferable simp: state_objs_to_policy_def)
apply (subst (asm) state_vrefs_helper_thing)
apply clarsimp
apply clarsimp
apply (erule subsetD)
apply (simp only:)
apply (drule sbta_vref)
apply fastforce

apply clarsimp
apply (erule state_asids_to_policy_aux.cases)
thm sata_asid
thm sata_asid_lookup
thm sata_asidpool
apply (fastforce dest: sata_asid)
prefer 2
apply (clarsimp split: if_splits)
apply (clarsimp simp: authorised_asid_control_inv_def)
apply (drule_tac x=frame in bspec)
apply clarsimp
  using is_aligned_no_overflow apply blast
  apply (simp add: aag_wellformed_refl)
apply (fastforce dest: sata_asidpool)

apply (subst (asm) state_vrefs_helper_thing)
apply clarsimp
apply clarsimp


apply (case_tac "asid_high_bits_of asid = asid_high_bits_of base")
prefer 2



apply (drule sata_asid_lookup[rotated])
apply clarsimp
apply assumption
apply fastforce
apply (clarsimp simp: state_vrefs_def aobjs_of_Some obj_at_def vs_refs_aux_def graph_of_def)
done

(* FIXME ryanb: move *)
lemma retype_region_invs_extras_vspace_objs:
  "\<lbrace>invs and pspace_no_overlap_range_cover ptr sz and caps_no_overlap ptr sz
     and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
     and region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
     and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
     and K (ty = CapTableObject \<longrightarrow> 0 < us)
     and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
      retype_region ptr n us ty dev \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  apply (wp hoare_strengthen_post [OF retype_region_post_retype_invs],
    auto simp: post_retype_invs_def split: if_split_asm)+
  done


lemma perform_asid_control_invocation_pas_refined [wp]:
  "\<lbrace>pas_refined aag and pas_cur_domain aag and invs and valid_aci aci and ct_active
                    and K (authorised_asid_control_inv aag aci)\<rbrace>
   perform_asid_control_invocation aci
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
apply (rule hoare_gen_asm)
  apply (simp add: perform_asid_control_invocation_def)
apply (wpc)
apply (rule hoare_seq_ext)
apply (simp only: K_bind_def)
apply (rule hoare_seq_ext)
apply (rule hoare_seq_ext)
apply (rule hoare_seq_ext)
apply (rule hoare_seq_ext)
apply (rule hoare_seq_ext)
apply (rule pas_refined_asid_control_helper)
apply assumption
   apply (wp cap_insert_pas_refined' static_imp_wp
          | strengthen
          | wpc
          | simp add: delete_objects_def2 fun_upd_def[symmetric])+
      apply (wp retype_region_pas_refined'[where sz=pageBits]
                hoare_vcg_ex_lift hoare_vcg_all_lift static_imp_wp hoare_wp_combs hoare_drop_imp
                retype_region_invs_extras(4)[where sz = pageBits]
                retype_region_invs_extras(6)[where sz = pageBits]
                retype_region_invs_extras(1)[where sz = pageBits]
retype_region_invs_extras_vspace_objs[where sz = pageBits]
             | simp add: do_machine_op_def split_def cte_wp_at_neg2)+

      apply (wp retype_region_cte_at_other'[where sz=pageBits]
                max_index_upd_invs_simple max_index_upd_caps_overlap_reserved
                hoare_vcg_ex_lift set_cap_cte_wp_at hoare_vcg_disj_lift set_free_index_valid_pspace
                set_cap_descendants_range_in set_cap_no_overlap get_cap_wp set_cap_caps_no_overlap
                hoare_vcg_all_lift static_imp_wp retype_region_invs_extras
                set_cap_pas_refined_not_transferable arch_update_cap_valid_mdb
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
             invs s \<and> asid_table s (asid_high_bits_of base) = None \<and>
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
apply (clarsimp simp: conj_ac)
   apply (rule conjI, fastforce)
   apply (rule conjI, fastforce)
   apply (rule conjI, fastforce)
   apply (rule conjI, fastforce)
   apply (rule conjI, force intro: descendants_range_caps_no_overlapI
                             simp: cte_wp_at_def)
   apply (rule conjI)
apply (clarsimp simp: max_free_index_def)
apply (prop_tac "valid_cap (UntypedCap False frame pageBits idx) s")
apply (clarsimp simp: get_cap_caps_of_state)
  apply (simp add: Untyped_AI.caps_of_state_valid)
   apply (rule conjI)
apply (clarsimp simp: free_index_of_def max_free_index_def valid_cap_def)
   apply (rule conjI)
    apply (cut_tac s=s and ptr="(parent_ptr, parent_idx)" in cap_refs_in_kernel_windowD)
      apply ((fastforce simp add: caps_of_state_def cap_range_def)+)[3]
apply (clarsimp simp: valid_cap_def)
apply (prop_tac "frame \<le> frame + (2 ^ pageBits - 1)")
  using is_aligned_no_overflow' apply blast
apply (prop_tac "frame + (2 ^ pageBits - 1) \<le> frame + 2 ^ pageBits - 1")
  apply (simp add: x_power_minus_1)
apply fastforce

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


definition authorised_asid_pool_inv :: "'a PAS \<Rightarrow> asid_pool_invocation \<Rightarrow> bool" where
 "authorised_asid_pool_inv aag api \<equiv>
  case api of Assign asid pool_ptr ct_slot \<Rightarrow>
    is_subject aag pool_ptr \<and> is_subject aag (fst ct_slot) \<and> is_subject_asid aag asid"

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





thm valid_arch_inv_def
thm copy_global_mappings_invs

lemma store_pte_state_vrefs_unreachable:
  "\<lbrace>(\<lambda>s. P (state_vrefs s)) and pspace_aligned and valid_vspace_objs and valid_asid_table and (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, table_base p) s) \<rbrace>
  store_pte p pte \<lbrace>\<lambda>_. (\<lambda>s. P (state_vrefs s))\<rbrace>"
 supply fun_upd_apply[simp del]
  apply (wpsimp simp: store_pte_def set_pt_def wp: set_object_wp)
apply (erule rsubst[where P=P])
apply (rule all_ext)
apply safe
prefer 2

apply (clarsimp simp: state_vrefs_def)
apply (subst (asm) vs_lookup_table_unreachable_upd_idem)
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply fastforce

apply (prop_tac "x \<noteq> table_base p")
  using vs_lookup_level apply blast
apply (clarsimp simp: fun_upd_def)
apply (clarsimp simp: aobjs_of_Some)
apply fastforce

apply (clarsimp simp: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
apply (rule exI)
apply (rule exI)
apply (rule conjI, rule refl)
apply (rule exI)
apply (rule exI)
apply (rule_tac x=vref in exI)
apply (rule conjI)
apply (subst vs_lookup_table_unreachable_upd_idem)
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply assumption
apply (prop_tac "x \<noteq> table_base p")
  using vs_lookup_level apply blast
apply (fastforce simp: fun_upd_def aobjs_of_Some obj_at_def)
apply clarsimp
done

(* FIXME ryanb: do something with original? *)
lemma not_in_global_refs_vs_lookup:
  "(\<exists>\<rhd> (level,p)) s \<and> valid_vs_lookup s \<and> valid_global_refs s
            \<and> valid_arch_state s \<and> valid_global_objs s
            \<and> pt_at p s
        \<Longrightarrow> p \<notin> global_refs s"
  apply clarsimp
  apply (cases "level = asid_pool_level"; simp)
   apply (simp add: vs_lookup_table_def in_omonad)
   apply (drule (1) pool_for_asid_ap_at)
   apply (clarsimp simp: obj_at_def)
  apply (drule (1) vs_lookup_table_target)
  apply (drule valid_vs_lookupD; clarsimp simp: vref_for_level_user_region)
  apply (drule(1) valid_global_refsD2)
  apply (simp add: cap_range_def)
  done

(* FIXME ryanb: original has unnecessary condition *)
lemma store_pte_valid_vs_lookup_unreachable:
  "\<lbrace> valid_vs_lookup and pspace_aligned and valid_vspace_objs and valid_asid_table and
     (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, table_base p) s)  \<rbrace>
   store_pte p pte
   \<lbrace> \<lambda>_. valid_vs_lookup \<rbrace>"
  unfolding valid_vs_lookup_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' store_pte_vs_lookup_target_unreachable)
  apply (erule disjE; clarsimp)
  done

lemma copy_global_mappings_state_vrefs:
  "\<lbrace> (\<lambda>s. P (state_vrefs s)) and invs and K (is_aligned pt_ptr pt_bits) and
     (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, pt_ptr) s)  \<rbrace>
   copy_global_mappings pt_ptr
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  unfolding copy_global_mappings_def
apply clarsimp
  apply wp
      apply (rule hoare_strengthen_post)
       apply (rule_tac P="(\<lambda>s. P (state_vrefs s)) and pspace_aligned and valid_vspace_objs and valid_asid_table and
unique_table_refs and
            valid_vs_lookup and valid_objs and
 (\<lambda>s. is_aligned pt_ptr pt_bits \<and> is_aligned global_pt pt_bits \<and>

 (\<forall>level. \<not> \<exists>\<rhd> (level, table_base (pt_ptr)) s) \<and>
 (\<forall>level. \<not> \<exists>\<rhd> (level, table_base (global_pt)) s))" in mapM_x_wp')

apply (wpsimp wp: store_pte_state_vrefs_unreachable store_pte_valid_vspace_objs
hoare_vcg_all_lift hoare_vcg_imp_lift'
store_pte_vs_lookup_table_unreachable
store_pte_valid_vs_lookup_unreachable
)

apply (prop_tac "table_base (pt_ptr + (x << pte_bits)) = pt_ptr")
apply (frule_tac i=x in is_aligned_pte_offset)
      apply (metis mask_2pm1 table_base_plus)

apply (prop_tac "table_base (global_pt + (x << pte_bits)) = global_pt")
apply (frule_tac i=x in is_aligned_pte_offset)
      apply (metis mask_2pm1 table_base_plus)

apply (clarsimp simp: valid_objs_caps)
  using ptes_of_wellformed_pte apply blast
apply clarsimp

apply wpsimp
apply clarsimp
apply (intro conjI; fastforce?)
  apply (simp add: invs_valid_global_vspace_mappings)
  apply (simp add: invs_valid_global_vspace_mappings)
apply (clarsimp)
apply (prop_tac "global_pt s \<notin> global_refs s")
apply (rule_tac level=level in not_in_global_refs_vs_lookup)
  using invs_valid_global_arch_objs valid_global_arch_objs_pt_at apply fastforce
  using invs_valid_global_arch_objs riscv_global_pt_in_global_refs apply blast
done

(*
lemma copy_global_mappings_pas_refined:
  "is_aligned pd pd_bits
   \<Longrightarrow> \<lbrace>pas_refined aag and valid_kernel_mappings and valid_arch_state
                        and valid_global_objs and valid_global_refs and pspace_aligned\<rbrace>
       copy_global_mappings pd
       \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
*)

crunches copy_global_mappings
  for tcb_domain_map_wellformed[wp]: "\<lambda>s. P (tcb_domain_map_wellformed aag s)"
  and asid_table[wp]: "\<lambda>s. P (asid_table s)"
  and cdt[wp]: "\<lambda>s. P (cdt s)"
  and thread_states[wp]: "\<lambda>s. P (thread_states s)"
  and thread_bound_ntfns[wp]: "\<lambda>s. P (thread_bound_ntfns s)"
  (wp: crunch_wps)

lemma copy_global_mappings_pas_refined:
  "\<lbrace> pas_refined aag and invs and K (is_aligned pt_ptr pt_bits) and
     (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, pt_ptr) s)
 \<rbrace>
   copy_global_mappings pt_ptr
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
apply (clarsimp simp: pas_refined_def state_objs_to_policy_def)
apply (rule hoare_pre)
apply_trace (rule hoare_vcg_conj_lift, solves wpsimp)+
apply (rule hoare_vcg_conj_lift)
prefer 2
apply (rule hoare_vcg_conj_lift)
prefer 2
apply wpsimp
apply wps
apply (rule copy_global_mappings_state_vrefs)
apply wps
apply (rule copy_global_mappings_state_vrefs)
apply clarsimp
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
*)

thm state_vrefs_def

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
oops
(*
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
  apply fastforce+
  done
oops
*)

(*
     \<Union>{vs_refs_aux lvl ao | lvl ao bot asid vref.

if we can pt walk to x from pt base
then THE level and ao.
else state_vrefs s x

vs_lookup_table bot asid vref s = Some (lvl, p) \<and>

 aobjs_of s p = Some ao \<and>

vref \<in> user_region}"

if \<exists>level vref. pt_walk max_pt_level level pt_base vref (ptes_of s) = Some (level, x) \<and> vref \<in> user_region
then vs_refs_aux (level_of_table) (the (aobjs_of s x))
else state_vrefs s x
*)
thm vs_lookup_table_def
thm level_of_table_def
thm vs_refs_aux_def

(* ryanb - useful theorem *)
thm valid_table_caps_pdD

lemma "valid_apinv (Assign asid pool_ptr ct_slot) s = X"
apply (clarsimp simp: valid_apinv_def)
oops


definition level_of_walk :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> vm_level"
  where
  "level_of_walk p p' vref s \<equiv>
     GREATEST level. pt_walk max_pt_level level p vref (ptes_of s) = Some (level, p')"

lemma
  "kernel_mappings_only pt s \<Longrightarrow> vs_refs_aux level (PageTable pt) = {}"

apply (clarsimp simp: vs_refs_aux_def)
oops


thm has_kernel_mappingsD
thm set_asid_pool_def


lemma store_asid_pool_entry_state_vrefs:
  "\<lbrace>\<lambda>s. P (\<lambda>x. if x = pool_ptr
               then vs_refs_aux asid_pool_level (ASIDPool (\<lambda>a. if a = asid_low_bits_of asid
                                                               then Some pt_base
                                                               else (the (asid_pools_of s pool_ptr)) a))
               else if x = pt_base
               then vs_refs_aux max_pt_level (the (aobjs_of s x))
               else state_vrefs s x) \<and>
        pool_for_asid asid s = Some pool_ptr \<and>
        (\<forall>pool. ako_at (ASIDPool pool) pool_ptr s \<longrightarrow> pool (asid_low_bits_of asid) = None) \<and>
        (\<forall>level. \<not>\<exists>\<rhd> (level, pt_base) s) \<and>
        (\<exists>pt. pts_of s pt_base = Some pt \<and> kernel_mappings_only pt s) \<and>
        pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s\<rbrace>
\<comment> \<open>
         pt_cap <- get_cap ct_slot;
         pt_base <- return $ acap_obj (the_arch_cap pt_cap);
\<close>
   store_asid_pool_entry pool_ptr asid (Some pt_base)
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
apply clarsimp
unfolding store_asid_pool_entry_def set_asid_pool_def
apply (wpsimp wp: set_object_wp get_cap_wp)
apply (erule rsubst[where P=P])
apply (rule all_ext)
apply (clarsimp split del: if_split)


apply (prop_tac "is_aligned pt_base pt_bits")
apply (fastforce elim: pspace_aligned_pts_ofD dest: invs_psp_aligned)

apply safe

apply (clarsimp split: if_splits)

(* x = pool_ptr *)
apply (clarsimp simp: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
prefer 2
apply (assumption)
apply (rule exI)
apply (rule exI)
apply (rule conjI, rule refl)
apply (rule_tac x=asid_pool_level in exI)
apply (rule exI)+
apply (rule conjI)
apply (clarsimp simp: fun_upd_def)
thm asid_pool_map.vs_lookup_table[simplified fun_upd_def]
apply (subst asid_pool_map.vs_lookup_table[simplified fun_upd_def])
thm asid_pool_map_def
apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at obj_at_def valid_apinv_def asid_low_bits_of_def
pts_of_Some aobjs_of_Some)
apply fastforce
apply clarsimp
apply (fastforce simp: vs_lookup_table_def obind_def split: option.splits)
apply clarsimp
apply (clarsimp simp: ako_asid_pools_of)
(* x = acap_obj acap *)
apply (clarsimp simp: obj_at_def)

apply (clarsimp simp: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
prefer 2
apply (assumption)
apply (rule exI)
apply (rule exI)
apply (rule conjI, rule refl)
apply (rule_tac x=max_pt_level in exI)
apply (rule_tac x=asid in exI)
apply (rule_tac x=0 in exI)
apply (rule conjI)
apply (clarsimp simp: fun_upd_def)
thm asid_pool_map.vs_lookup_table[simplified fun_upd_def]
thm asid_pool_map.vs_lookup_table
apply (subst asid_pool_map.vs_lookup_table[simplified fun_upd_def])
apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at obj_at_def valid_apinv_def asid_low_bits_of_def
pts_of_Some aobjs_of_Some)
apply clarsimp
apply clarsimp
apply clarsimp
apply (clarsimp simp: pts_of_Some)

(* x is none of the above *)

apply (clarsimp simp: obj_at_def)

apply (clarsimp simp: state_vrefs_def)
apply (rule exI)
apply (rule conjI)
prefer 2
apply (assumption)
apply (rule exI)
apply (rule exI)
apply (rule conjI, rule refl)
apply (frule vs_lookup_level)
apply (rule_tac x=lvl in exI)
apply (rule_tac x=asida in exI)
apply (rule_tac x=vref in exI)
apply (rule conjI)
apply (clarsimp simp: fun_upd_def)
thm asid_pool_map.vs_lookup_table[simplified fun_upd_def]
thm asid_pool_map.vs_lookup_table
apply (subst asid_pool_map.vs_lookup_table[simplified fun_upd_def])
apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at obj_at_def valid_apinv_def asid_low_bits_of_def
pts_of_Some aobjs_of_Some)
apply clarsimp
apply clarsimp
apply (clarsimp simp: vs_lookup_table_def obind_def vspace_for_pool_def asid_pools_of_ko_at
obj_at_def
split: if_splits option.splits)
apply clarsimp


(* second direction *)

supply if_split[split del]
apply (subst (asm) state_vrefs_def)
apply clarsimp
apply (clarsimp simp: fun_upd_def)
apply (subst (asm) asid_pool_map.vs_lookup_table[simplified fun_upd_def])
apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at obj_at_def valid_apinv_def asid_low_bits_of_def
pts_of_Some aobjs_of_Some)
apply clarsimp
apply (case_tac "x = pool_ptr")
apply clarsimp
apply (prop_tac "asid_pools_of s pool_ptr = Some pool")
apply (clarsimp simp:  asid_pools_of_ko_at obj_at_def)
apply (clarsimp simp: vs_refs_aux_def)

apply clarsimp

apply (case_tac "asida = asid \<and> bot \<le> max_pt_level")
apply clarsimp

apply clarsimp

apply (case_tac "x = pt_base")
apply clarsimp
apply (fastforce dest: vs_lookup_level)
apply clarsimp
apply (fastforce simp: state_vrefs_def)
done

crunches store_asid_pool_entry
  for irq_map_wellformed[wp]: "\<lambda>s. P (irq_map_wellformed aag s)"
  and tcb_domain_map_wellformed[wp]: "\<lambda>s. P (tcb_domain_map_wellformed aag s)"
  and state_irqs_to_policy[wp]: "\<lambda>s. P (state_irqs_to_policy aag s)"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and asid_table[wp]: "\<lambda>s. P (asid_table s)"
  and cdt[wp]: "\<lambda>s. P (cdt s)"
  and thread_states[wp]: "\<lambda>s. P (thread_states s)"
  and thread_bound_ntfns[wp]: "\<lambda>s. P (thread_bound_ntfns s)"


thm authorised_asid_pool_inv_def
lemma store_asid_pool_entry_pas_refined:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and>
        pool_for_asid asid s = Some pool_ptr \<and>
        (\<forall>level. \<not>\<exists>\<rhd> (level, pt_base) s) \<and>
        (\<forall>pool. ako_at (ASIDPool pool) pool_ptr s \<longrightarrow> pool (asid_low_bits_of asid) = None) \<and>
        (\<exists>pt. pts_of s pt_base = Some pt \<and> kernel_mappings_only pt s) \<and>
        pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<and>
is_subject aag pool_ptr \<and>
is_subject aag pt_base \<and>
is_subject_asid aag asid
\<rbrace>
\<comment> \<open>
         pt_cap <- get_cap ct_slot;
         pt_base <- return $ acap_obj (the_arch_cap pt_cap);
\<close>
   store_asid_pool_entry pool_ptr asid (Some pt_base)
   \<lbrace>\<lambda>_ s. pas_refined aag s\<rbrace>"
apply (clarsimp simp: pas_refined_def state_objs_to_policy_def)
apply (rule hoare_pre)
apply wpsimp
apply (rule hoare_vcg_conj_lift)
prefer 2
apply (rule hoare_vcg_conj_lift)
prefer 2
apply wpsimp
apply wps
apply (rule store_asid_pool_entry_state_vrefs)
apply wps
apply (rule store_asid_pool_entry_state_vrefs)
apply clarsimp


apply (frule (1) pool_for_asid_validD)
apply clarsimp


apply (rule conjI)


apply (clarsimp simp: auth_graph_map_def)

apply (erule state_bits_to_policy.cases)
apply (fastforce dest: sbta_caps simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_untyped simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_ts simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_bounds simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_cdt simp: state_objs_to_policy_def)
apply (fastforce dest: sbta_cdt_transferable simp: state_objs_to_policy_def)


apply (case_tac "ptr = pool_ptr")
apply clarsimp

apply (clarsimp simp: vs_refs_aux_def)
apply (clarsimp simp: graph_of_def)
apply (clarsimp split: if_splits)

  apply (simp add: aag_wellformed_refl)

apply (erule subsetD)
apply clarsimp
apply (rule_tac x=pool_ptr in exI)
apply clarsimp
apply (rule exI, rule conjI, rule refl)

apply (rule sbta_vref)
apply (clarsimp simp: state_vrefs_def)
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
apply (subst vs_lookup_table_def)
apply (clarsimp simp: obind_def aobjs_of_Some)
apply (fastforce simp: aobjs_of_Some obj_at_def asid_pools_of_ko_at)
apply (fastforce simp: vs_refs_aux_def graph_of_def)

apply (case_tac "ptr = pt_base")
apply clarsimp

apply (clarsimp simp: pts_of_Some)

apply (subgoal_tac "vs_refs_aux max_pt_level (PageTable pt) = {}", clarsimp)
apply_trace (clarsimp simp: vs_refs_aux_def)
apply (clarsimp simp: kernel_mappings_only_def)
apply (clarsimp simp: graph_of_def pte_ref2_def)

apply (simp only: if_False)
apply (drule sbta_vref)
apply fastforce


apply clarsimp

apply (erule state_asids_to_policy_aux.cases)

apply (erule subsetD) back
apply (fastforce dest: sata_asid)





apply (case_tac "poolptr = pool_ptr")
apply clarsimp

apply (clarsimp simp: vs_refs_aux_def)
apply (clarsimp simp: graph_of_def)
apply (clarsimp split: if_splits)

apply (clarsimp simp: pool_for_asid_def)

thm valid_asid_table_def
apply (clarsimp simp: asid_pools_of_ko_at obj_at_def)

apply (clarsimp simp: valid_asid_table_def)
apply (clarsimp simp: inj_on_def)
apply (drule_tac x="asid_high_bits_of asid" in bspec, clarsimp)
apply (drule_tac x="asid_high_bits_of asida" in bspec, clarsimp)
apply clarsimp

apply (prop_tac "asid_low_bits_of asida = asid_low_bits_of asid")

apply (simp add: asid_low_bits_of_mask_eq[symmetric])
apply (clarsimp simp: ucast_ucast_b is_up_def source_size_def target_size_def word_size)

apply (prop_tac "is_up UCAST(9 \<rightarrow> 64)")
apply (clarsimp simp: ucast_ucast_b is_up_def source_size_def target_size_def word_size)
apply (drule inj_ucast[OF refl])
apply (clarsimp simp: inj_def)

apply (drule asid_high_low)
apply clarsimp

  apply (metis aag_wellformed_refl)

apply (erule subsetD) back
apply (rule sata_asid_lookup)
apply fastforce
apply (clarsimp simp: state_vrefs_def)

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
apply (subst vs_lookup_table_def)
apply (clarsimp simp: obind_def aobjs_of_Some)
apply (fastforce simp: aobjs_of_Some obj_at_def asid_pools_of_ko_at)

apply (subst vs_refs_aux_def)
apply (fastforce simp: graph_of_def)
apply clarsimp

apply (case_tac "poolptr = pt_base")
apply (clarsimp simp: vs_refs_aux_def pts_of_Some)

apply (simp only: if_False)
apply (erule subsetD) back
apply (rule sata_asid_lookup[rotated])
apply assumption
apply assumption

apply (erule subsetD) back
apply (fastforce dest: sata_asidpool)
done

crunches copy_global_mappings
  for pspace_aligned[wp]: pspace_aligned
  and valid_asid_table[wp]: valid_asid_table
  (wp: crunch_wps )

lemma store_pte_valid_objs [wp]:
  "\<lbrace>\<lambda>s. valid_caps (caps_of_state s) s\<rbrace> store_pte p pte \<lbrace>\<lambda>_s . valid_caps (caps_of_state s) s\<rbrace>"
  apply (simp add: store_pte_def set_pt_def bind_assoc set_object_def get_object_def)
  apply (wpsimp simp_del: fun_upd_apply)
apply (subst caps_of_state_fun_upd)
apply (clarsimp simp: obj_at_def)
apply (clarsimp simp: valid_caps_def)
apply (subst valid_cap_same_type)
apply fastforce+
apply (clarsimp simp: obj_at_def)
oops


lemma
"copy_global_mappings pt_base
       \<lbrace>\<lambda>s. vs_lookup_table level asid vref s \<noteq> Some (level, pt_base)\<rbrace>"
unfolding copy_global_mappings_def
apply wpsimp
apply (rule hoare_strengthen_post)
apply (rename_tac gpt base pt_size)
apply (rule_tac P="\<lambda>s. (\<forall>x \<in> set [base .e. pt_size - 1]. \<forall>level. \<not> \<exists>\<rhd> (level, table_base (pt_base + (x << pte_bits))) s) \<and>
           vref \<in> user_region \<and>
           vs_lookup_table level asid vref s \<noteq> Some (level, pt_base) \<and>
 pspace_aligned s \<and> valid_objs s \<and> valid_vspace_objs s \<and> valid_asid_table s
\<and> unique_table_refs s \<and> valid_vs_lookup s
"
and S="set [base .e. pt_size - 1]"
in mapM_x_wp)
thm mapM_x_inv_wp
apply (rule hoare_seq_ext)
apply wps
apply_trace (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' store_pte_vs_lookup_table_unreachable
store_pte_valid_vs_lookup_unreachable
store_pte_valid_vspace_objs
)
apply wpsimp
apply auto[1]
apply (clarsimp simp: ptes_of_wellformed_pte)
apply (clarsimp simp: valid_objs_caps)
oops



lemma copy_global_mappings_vs_lookup_table_noteq:
  "\<lbrace> (\<lambda>s. vref \<in> user_region \<and>
vs_lookup_table level asid vref s \<noteq> Some (level, pt_ptr)) and invs and K (is_aligned pt_ptr pt_bits) and
     (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, pt_ptr) s) \<rbrace>
   copy_global_mappings pt_ptr
   \<lbrace>\<lambda>_ s. vs_lookup_table level asid vref s \<noteq> Some (level, pt_ptr)\<rbrace>"
  unfolding copy_global_mappings_def
apply clarsimp
  apply wp
      apply (rule hoare_strengthen_post)
       apply (rule_tac P="(\<lambda>s. vref \<in> user_region \<and> vs_lookup_table level asid vref s \<noteq> Some (level, pt_ptr)) and pspace_aligned and valid_vspace_objs and valid_asid_table and
unique_table_refs and
            valid_vs_lookup and valid_objs and
 (\<lambda>s. is_aligned pt_ptr pt_bits \<and>

 (\<forall>level. \<not> \<exists>\<rhd> (level, table_base (pt_ptr)) s) )" in mapM_x_wp')

apply (wpsimp wp: store_pte_state_vrefs_unreachable store_pte_valid_vspace_objs
hoare_vcg_all_lift hoare_vcg_imp_lift'
store_pte_vs_lookup_table_unreachable
store_pte_valid_vs_lookup_unreachable
)

apply (prop_tac "table_base (pt_ptr + (x << pte_bits)) = pt_ptr")
apply (frule_tac i=x in is_aligned_pte_offset)
      apply (metis mask_2pm1 table_base_plus)

apply (clarsimp simp: valid_objs_caps)
  using ptes_of_wellformed_pte apply blast
apply clarsimp

apply wpsimp
apply clarsimp
apply (intro conjI; fastforce?)
done


lemma copy_global_mappings_valid_vspace_objs:
  "\<lbrace>  invs and K (is_aligned pt_ptr pt_bits) and
     (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, pt_ptr) s)
 \<rbrace>
   copy_global_mappings pt_ptr
   \<lbrace>\<lambda>_ s. valid_vspace_objs s\<rbrace>"
  unfolding copy_global_mappings_def
apply clarsimp
  apply wp
      apply (rule hoare_strengthen_post)
       apply (rule_tac P="
 pspace_aligned and valid_vspace_objs and valid_asid_table and
unique_table_refs and
            valid_vs_lookup and valid_objs and
 (\<lambda>s. is_aligned pt_ptr pt_bits \<and>

 (\<forall>level. \<not> \<exists>\<rhd> (level, table_base (pt_ptr)) s) )" in mapM_x_wp')

apply (wpsimp wp: store_pte_state_vrefs_unreachable store_pte_valid_vspace_objs
hoare_vcg_all_lift hoare_vcg_imp_lift'
store_pte_vs_lookup_table_unreachable
store_pte_valid_vs_lookup_unreachable
)

apply (prop_tac "table_base (pt_ptr + (x << pte_bits)) = pt_ptr")
apply (frule_tac i=x in is_aligned_pte_offset)
      apply (metis mask_2pm1 table_base_plus)

apply (clarsimp simp: valid_objs_caps)
  using ptes_of_wellformed_pte apply blast
apply clarsimp

apply wpsimp
apply clarsimp
apply (intro conjI; fastforce?)
done


lemma perform_asid_pool_invocation_pas_refined [wp]:
  "\<lbrace>pas_refined aag and invs and valid_apinv api and K (authorised_asid_pool_inv aag api)\<rbrace>
   perform_asid_pool_invocation api
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: perform_asid_pool_invocation_def)

apply (wpsimp)
apply (wpsimp wp: store_asid_pool_entry_pas_refined)
apply_trace (wpsimp wp: copy_global_mappings_pas_refined)
apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')
apply (wpsimp wp: copy_global_mappings_vs_lookup_table_noteq)
apply wpsimp
apply (clarsimp simp: ako_asid_pools_of)
apply_trace (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' copy_global_mappings_valid_vspace_objs)
apply wpsimp
apply clarsimp
apply (strengthen invs_psp_aligned invs_valid_asid_table)
apply (clarsimp simp: conj_ac cong: conj_cong imp_cong)
apply (wpsimp wp: arch_update_cap_invs_map set_cap_pas_refined_not_transferable
hoare_vcg_all_lift hoare_vcg_imp_lift'
)
apply (wpsimp wp: get_cap_wp)+
apply (clarsimp simp: conj_ac)
apply (rule conjI, fastforce)+

apply (clarsimp simp: valid_apinv_def)

apply (clarsimp simp: cte_wp_at_caps_of_state)
apply (clarsimp simp: is_PageTableCap_def is_ArchObjectCap_def)
apply (clarsimp split: option.splits)
apply (clarsimp simp: authorised_asid_pool_inv_def)

apply (intro conjI)
  using caps_of_state_aligned_page_table apply blast
apply (fastforce dest: cap_not_in_valid_global_refs)
apply (drule (1) cap_cur_auth_caps_of_state)
apply clarsimp
apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def)
  using pas_refined_Control apply fastforce

apply (drule (1) caps_of_state_valid)
apply (clarsimp simp: update_map_data_def)
apply (clarsimp simp: valid_cap_def cap_aligned_def wellformed_mapdata_def)

apply (drule (1) cap_cur_auth_caps_of_state)
apply clarsimp
apply (clarsimp simp: update_map_data_def)
apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
cap_links_asid_slot_def label_owns_asid_slot_def cap_links_irq_def)
  using pas_refined_refl apply blast

  using invs_valid_table_caps valid_table_caps_def apply blast
  apply (simp add: asid_bits_of_defs(2))


apply (frule (1) caps_of_state_valid)
apply (clarsimp simp: valid_cap_def)
    apply (clarsimp simp: obj_at_def)
apply (rename_tac asid' pool_ptr a b acap_obj level asid vref pt)
   apply (drule (1) vs_lookup_table_valid_cap; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap, simp add: pts_of_Some aobjs_of_Some, fastforce intro: valid_objs_caps)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp)
   apply (clarsimp simp: is_cap_simps)

apply (frule (1) caps_of_state_valid)
apply (clarsimp simp: valid_cap_def)
    apply (clarsimp simp: obj_at_def)
apply (rename_tac asid' pool_ptr a b acap_obj level asid vref pt)
   apply (drule (1) vs_lookup_table_valid_cap; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap, simp add: pts_of_Some aobjs_of_Some, fastforce intro: valid_objs_caps)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp)
   apply (clarsimp simp: is_cap_simps)

apply (clarsimp simp: is_arch_update_def update_map_data_def is_cap_simps cap_master_cap_def)

done



definition authorised_arch_inv :: "'a PAS \<Rightarrow> arch_invocation \<Rightarrow> 's :: state_ext state \<Rightarrow> bool" where
 "authorised_arch_inv aag ai s \<equiv> case ai of
     InvokePageTable pti \<Rightarrow> authorised_page_table_inv aag pti
   | InvokePage pgi \<Rightarrow> authorised_page_inv aag pgi s
   | InvokeASIDControl aci \<Rightarrow> authorised_asid_control_inv aag aci
   | InvokeASIDPool api \<Rightarrow> authorised_asid_pool_inv aag api"

(*
crunch respects [wp]: perform_page_directory_invocation "integrity aag X st"
  (ignore: do_machine_op)

crunch pas_refined [wp]: perform_page_directory_invocation "pas_refined aag"
*)

lemma invoke_arch_respects:
  "\<lbrace>integrity aag X st and authorised_arch_inv aag ai and
    pas_refined aag and invs and valid_arch_inv ai and is_subject aag \<circ> cur_thread\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: arch_perform_invocation_def)
  apply (wpsimp wp: perform_page_table_invocation_respects perform_page_invocation_respects
                    perform_asid_control_invocation_respects perform_asid_pool_invocation_respects)
  apply (auto simp: authorised_arch_inv_def valid_arch_inv_def)
  done





lemma invoke_arch_pas_refined:
  "\<lbrace>pas_refined aag and pas_cur_domain aag and invs and ct_active
                    and valid_arch_inv ai and authorised_arch_inv aag ai\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: arch_perform_invocation_def valid_arch_inv_def)
  apply (rule hoare_pre)
  apply (wp perform_page_table_invocation_pas_refined | wpc)+
apply (auto simp: authorised_arch_inv_def)
done

(*

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
*)


lemma decode_arch_invocation_authorised_helper:
 "pas_refined aag s \<Longrightarrow>
valid_asid_table s \<Longrightarrow>
vspace_for_asid a s = Some xaa \<Longrightarrow>
is_subject_asid aag a \<Longrightarrow>
 is_subject aag xaa"
apply (clarsimp simp: vspace_for_asid_def)
apply (frule (1) pool_for_asid_validD)
apply (clarsimp simp:
vspace_for_pool_def pool_for_asid_def
asid_pools_of_ko_at obj_at_def
)
thm sata_asid_lookup
apply (frule_tac vrefs="state_vrefs s" in sata_asid_lookup)
apply (clarsimp simp: state_vrefs_def)

apply (clarsimp simp: aobjs_of_Some)
apply (rule exI)
apply (rule conjI)
apply (rule_tac x=asid_pool_level in exI)
apply (rule exI)
apply (rule conjI)
apply (rule refl)
apply (rule_tac x=asid_pool_level in exI)
apply (rule_tac x=a in exI)
apply (rule_tac x=0 in exI)
apply (rule conjI)
prefer 2
apply fastforce
apply (clarsimp simp: vs_lookup_table_def obind_def
pool_for_asid_def vspace_for_pool_def asid_pools_of_ko_at obj_at_def split: option.splits)
apply (clarsimp simp: vs_refs_aux_def graph_of_def)

apply (clarsimp simp: image_def)
apply (rule exI)
apply (rule conjI)
apply assumption
apply (rule conjI)
prefer 2
apply (rule refl)

apply (clarsimp simp: asid_low_bits_of_def)
apply (word_eqI)
apply (fastforce simp: asid_low_bits_def)
apply (clarsimp simp: pas_refined_def)
apply (drule subsetD) back
apply assumption
  using aag_wellformed_Control by fastforce


lemma decode_page_table_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                  aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                  is_subject aag (fst slot) \<and>
                  (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)
)
and K (is_PageTableCap cap)\<rbrace> decode_page_table_invocation label msg slot cap excaps
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>,-"
apply (rule hoare_gen_asmE)
apply (clarsimp simp: is_PageTableCap_def)
apply (rename_tac x xa)
unfolding decode_page_table_invocation_def decode_pt_inv_map_def authorised_arch_inv_def
apply (wpsimp simp: Let_def  is_final_cap_def if_fun_split )

thm crunch_wps
  apply (prop_tac "\<forall>y \<in> set [x , x + 2 ^ pte_bits .e. x + 2 ^ pt_bits - 1]. table_base y = x")
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (drule (1) caps_of_state_aligned_page_table)
   apply (simp only: is_aligned_neg_mask_eq')
   apply (clarsimp simp: add_mask_fold)
   apply (drule subsetD[OF upto_enum_step_subset], clarsimp)
   apply (drule neg_mask_mono_le[where n=pt_bits])
   apply (drule neg_mask_mono_le[where n=pt_bits])
   apply (fastforce dest: FIXME_wordAND_wordNOT_mask_plus)

apply safe

prefer 3
apply (clarsimp simp: authorised_page_table_inv_def)
apply (clarsimp simp: cte_wp_at_caps_of_state)
apply (drule caps_of_state_pasObjectAbs_eq)
apply (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def)
apply assumption
apply clarsimp
apply (fastforce simp: obj_refs_def)
apply clarsimp

prefer 2
apply (clarsimp simp: authorised_page_table_inv_def)


apply (clarsimp simp: authorised_page_table_inv_def)

apply (rule conjI)
apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def)
thm pt_walk_is_subject
apply (frule_tac asid=a in pt_walk_is_subject)
apply fastforce
apply fastforce
apply fastforce
apply assumption
apply (drule vspace_for_asid_vs_lookup)
apply (clarsimp simp: vs_lookup_table_def)

apply clarsimp
apply (clarsimp simp: user_region_def)
apply (drule not_le_imp_less)
  using user_vtop_canonical_user apply blast

apply (rule decode_arch_invocation_authorised_helper)
apply assumption
apply fastforce
apply fastforce


apply (erule_tac x="excaps ! 0" in ballE) back
apply (clarsimp)
apply clarsimp


apply (subst pt_slot_offset_id)
apply (erule pt_walk_is_aligned)
apply (erule_tac x="excaps ! 0" in ballE)
apply (fastforce simp: cte_wp_at_caps_of_state dest: caps_of_state_aligned_page_table)
apply clarsimp
apply clarsimp

apply (erule_tac x="excaps ! 0" in ballE; clarsimp)
apply (erule_tac x="excaps ! 0" in ballE)
prefer 2
apply (case_tac excaps; clarsimp)
apply (clarsimp simp: aag_cap_auth_def)
apply (intro conjI)
apply (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def)
apply (clarsimp simp: cap_links_asid_slot_def label_owns_asid_slot_def)
apply (clarsimp simp: cap_links_irq_def)

done




lemma decode_frame_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                  aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                  is_subject aag (fst slot) \<and>
                  (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)
)
and K (is_FrameCap cap)\<rbrace> decode_frame_invocation label msg slot cap excaps
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>,-"
apply (rule hoare_gen_asmE)
apply (clarsimp simp: is_FrameCap_def)
unfolding decode_frame_invocation_def authorised_arch_inv_def decode_fr_inv_map_def
apply (wpsimp wp: check_vp_wpR simp: Let_def)

apply (clarsimp simp: authorised_page_inv_def)


apply (erule_tac x="excaps ! 0" in ballE; clarsimp)
apply (erule_tac x="excaps ! 0" in ballE; clarsimp)
prefer 2
apply (case_tac excaps; clarsimp)

apply (prop_tac "pas_cap_cur_auth aag (ArchObjectCap (FrameCap x31 x32 x33 x34 (Some (a, msg ! 0)))) \<and>
             authorised_slots aag
              (make_user_pte (addrFromPPtr x31) (attribs_from_word (msg ! 2)) (mask_vm_rights x32 (data_to_rights (msg ! Suc 0))), xd)
              s")
apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
cap_links_asid_slot_def cap_links_irq_def)
apply (clarsimp simp: authorised_slots_def)

apply (prop_tac " msg ! 0 \<in> user_region")
apply (clarsimp simp: user_region_def)
apply (drule not_le_imp_less)
apply (subgoal_tac "msg ! 0 \<le> msg ! 0 + mask (pageBitsForSize x33)")
  using user_vtop_canonical_user apply fastforce
apply (clarsimp simp: vmsz_aligned_def)
apply (erule is_aligned_no_overflow_mask)

apply (rule conjI)
prefer 2

apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def)

apply (frule_tac asid=a in pt_walk_is_subject)
apply fastforce
apply fastforce
apply fastforce
apply assumption
apply (drule vspace_for_asid_vs_lookup)
apply (clarsimp simp: vs_lookup_table_def)
apply clarsimp
apply clarsimp

apply (rule decode_arch_invocation_authorised_helper)
apply assumption
apply fastforce
apply fastforce
apply clarsimp

apply (subst pt_slot_offset_id)
apply (erule pt_walk_is_aligned)
apply (fastforce simp: cte_wp_at_caps_of_state dest: caps_of_state_aligned_page_table)
apply clarsimp

apply clarsimp

  apply (frule (1) pt_lookup_slot_vs_lookup_slotI, clarsimp)

apply (drule (1) vs_lookup_slot_unique_level)
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply clarsimp

apply (clarsimp simp: make_user_pte_def split: if_splits, clarsimp simp: pte_ref2_def)

apply (clarsimp simp: pte_ref2_def)


apply (subst (asm) ptrFromPAddr_addr_from_ppn)
apply (clarsimp simp: cte_wp_at_caps_of_state)
apply (frule (1) caps_of_state_valid)
apply (clarsimp simp: valid_cap_def cap_aligned_def)
  apply (metis is_aligned_pageBitsForSize_table_size)

apply (clarsimp simp: cte_wp_at_caps_of_state)
apply (drule_tac x=p in bspec)
apply clarsimp

apply (fastforce simp: vspace_cap_rights_to_auth_def mask_vm_rights_def validate_vm_rights_def
vm_kernel_only_def vm_read_only_def
split: if_splits)

apply clarsimp
done


lemma decode_asid_control_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                  aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                  is_subject aag (fst slot) \<and>
                  (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)
)
and K (cap = ASIDControlCap)\<rbrace> decode_asid_control_invocation label msg slot cap excaps
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>,-"
apply (rule hoare_gen_asmE)
apply (clarsimp simp: authorised_arch_inv_def)
unfolding decode_asid_control_invocation_def authorised_arch_inv_def
lookup_target_slot_def authorised_asid_control_inv_def
apply (wpsimp)

apply safe

apply (clarsimp simp: is_cap_simps)
apply (erule_tac x="excaps ! Suc 0" in ballE) back
apply (fastforce simp: aag_cap_auth_def cap_auth_conferred_def dest: pas_refined_Control)
apply clarsimp

apply (erule_tac x="excaps ! 0" in ballE)
apply (clarsimp simp: cte_wp_at_caps_of_state)
apply (drule (1) caps_of_state_valid) back
apply (clarsimp simp: valid_cap_def cap_aligned_def)
apply (case_tac excaps; clarsimp)

apply (erule_tac x="excaps ! 0" in ballE) back
apply clarsimp
apply (case_tac excaps; clarsimp)


apply clarsimp
apply (erule_tac x="excaps ! 0" in ballE) back
prefer 2
apply (case_tac excaps; clarsimp)
apply clarsimp

apply (clarsimp simp: aag_cap_auth_def)
apply (erule_tac x=xd in ballE)
apply (fastforce dest: pas_refined_Control)
apply clarsimp
done

(*
lemma decode_arch_invocation_authorised_helper:
 "pas_refined aag s \<Longrightarrow>
valid_asid_table s \<Longrightarrow>
pool_for_asid a s = Some xaa \<Longrightarrow>
is_subject_asid aag a \<Longrightarrow>
a \<noteq> 0 \<Longrightarrow>
 is_subject aag xaa"
apply (frule (1) pool_for_asid_validD)
apply (clarsimp simp:
vspace_for_pool_def pool_for_asid_def
asid_pools_of_ko_at obj_at_def
)

apply (frule_tac vrefs="state_vrefs s" in sata_asidpool)
apply (clarsimp simp: )

apply (clarsimp simp: pas_refined_def)
apply (drule subsetD) back
apply assumption
  using aag_wellformed_Control by fastforce
*)


lemma decode_asid_pool_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                  aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                  is_subject aag (fst slot) \<and>
                  (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)
)
and K (is_ASIDPoolCap cap)\<rbrace> decode_asid_pool_invocation label msg slot cap excaps
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>,-"
apply (rule hoare_gen_asmE)
unfolding decode_asid_pool_invocation_def authorised_arch_inv_def
Let_def
apply (wpsimp)
apply (erule swap) back back back


apply (erule_tac x="excaps ! 0" in ballE)
prefer 2
apply (case_tac excaps; clarsimp)

apply (erule_tac x="excaps ! 0" in ballE)
prefer 2
apply (case_tac excaps; clarsimp)

apply clarsimp
apply (clarsimp simp: authorised_asid_pool_inv_def)

apply (clarsimp simp: is_ASIDPoolCap_def)
apply (clarsimp simp: cte_wp_at_caps_of_state)

apply (rule context_conjI)

apply (clarsimp simp: pas_refined_def)
apply (clarsimp simp: state_objs_to_policy_def auth_graph_map_def)
apply (drule subsetD)
apply (drule sbta_caps)
apply (fastforce simp: obj_refs_def)
apply (fastforce simp: cap_auth_conferred_def arch_cap_auth_conferred_def)
apply fastforce
  using aag_wellformed_Control apply fastforce

apply (erule allE, drule mp)
prefer 2
apply assumption
apply clarsimp

apply (prop_tac "is_aligned x12 asid_low_bits")
apply (clarsimp simp: aag_cap_auth_def)
apply (drule (1) caps_of_state_valid)
apply (clarsimp simp: valid_cap_def)


apply (drule int_not_emptyD)
apply clarsimp
apply (erule swap) back back back
apply clarsimp


apply (clarsimp simp: free_asid_pool_select_def)
apply (case_tac "filter (\<lambda>(x, y). UCAST(9 \<rightarrow> 16) x + x12 \<noteq> 0 \<and> y = None) (assocs pool)")
apply (fastforce simp: filter_empty_conv fun_is_in_assocs)
apply (clarsimp simp: filter_eq_Cons_iff)

apply (rule asid_high_bits_of_add_ucast)
apply clarsimp
done


lemma decode_arch_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                  aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                  is_subject aag (fst slot) \<and>
                  (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v))\<rbrace>
   arch_decode_invocation label msg x_slot slot cap excaps
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>,-"
  unfolding arch_decode_invocation_def
apply (wpsimp wp: decode_page_table_invocation_authorised decode_asid_pool_invocation_authorised
decode_asid_control_invocation_authorised decode_frame_invocation_authorised)
apply auto
done

(*

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
*)
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
