import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Product
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Cast
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Distrib
import DeBruijnSSA.BinSyntax.Rewrite.Term.Structural.Distrib
import DeBruijnSSA.BinSyntax.Rewrite.Region.Case

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

open Term.Eqv

theorem Eqv.packed_in_case_split {Γ : Ctx α ε} {R : LCtx α}
  {a : Term.Eqv φ Γ (A.coprod B, e)} {r : Eqv φ ((A, ⊥)::Γ) R} {s : Eqv φ ((B, ⊥)::Γ) R}
  : (case a r s).packed_in (Δ := Δ)
  = case (Term.Eqv.split ;;' _ ⋊' a.packed ;;' Term.Eqv.distl_inv) r.packed_in s.packed_in := by
  rw [Term.Eqv.seq_distl_inv, Term.Eqv.seq_rtimes, Term.Eqv.split]
  simp only [Term.Eqv.nil, wk1_packed, Term.Eqv.let2_pair, wk0_var, zero_add, let1_beta_var0,
    subst_let1, var_succ_subst0, subst_pair, subst_lift_var_succ, var0_subst0, List.length_cons,
    Nat.reduceAdd, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
    wk_res_eff, wk_eff_var, subst_lift_packed, subst0_var0_packed, subst0_wk0, subst_lift_coprod,
    subst_inl, subst_lift_var_zero, subst_inr]
  rw [case_let1, packed_in_case, case_bind]
  congr 1
  simp only [vwk1_let1, wk1_pair, wk1_var_succ, zero_add, wk1_var0, List.length_cons, Fin.zero_eta,
    List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, vwk2_packed_in, Term.Eqv.coprod,
    wk1_inl, Nat.add_zero, Nat.zero_eq, wk1_inr, vwk1_packed_in, case_case, case_inl, case_inr]
  rfl

theorem Eqv.packed_in_coprod_dist {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) L} {r : Eqv φ (⟨B, ⊥⟩::Γ) L}
  : (l.coprod r).packed_in (Δ := Δ) = case (Term.Eqv.distl_inv (e := ⊥)) l.packed_in r.packed_in
  := by
  rw [coprod, packed_in_case_split, packed_var, pi_n_zero', Term.Eqv.pi_r]
  simp only [List.length_cons, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero,
    List.getElem_cons_zero, wk_res_self]
  rw [<-Term.Eqv.pi_r, Term.Eqv.split_rtimes_pi_r_distl_packed]
  conv => rhs; rw [case_bind, <-coprod]
  rw [case_bind, <-coprod, Term.Eqv.seq, let1_let1]
  apply congrArg
  simp [
    Term.Eqv.sum, Term.Eqv.coprod, let1_case, coprod, let1_beta, Term.Eqv.wk1_seq,
    Term.Eqv.wk2_seq, Term.Eqv.seq_inj_l, Term.Eqv.seq_inj_r, case_case, case_inl, case_inr
  ]
  congr 1 <;> {
    simp [packed_in, vsubst_vsubst, vwk1, <-vsubst_fromWk]
    congr; ext k; cases k using Fin.cases with
    | zero =>
      simp only [List.get_eq_getElem, List.length_cons, Fin.val_zero, List.getElem_cons_zero,
        Term.Subst.Eqv.get_comp, Term.Subst.Eqv.get_fromWk, Fin.zero_eta, Set.mem_setOf_eq,
        Ctx.InS.coe_wk1, Nat.liftWk_zero, subst_var, id_eq, Term.Subst.Eqv.get_unpack, wk_res_self]
      rw [<-let1_beta_pure, <-wk1_pi_n, <-Term.Eqv.seq, Term.Eqv.wk1_wk2]
      simp only [List.get_eq_getElem, List.length_cons, Fin.val_zero, List.getElem_cons_zero, split,
        Term.Eqv.ltimes, pair_tensor_pure, Term.Eqv.nil_seq, Term.Eqv.seq_nil, wk1_rtimes, wk1_pair,
        wk1_inj_l, wk1_nil]
      simp only [Term.Eqv.rtimes, tensor, wk1_nil, wk1_pair, wk1_inj_l, seq_assoc_inv,
        reassoc_inv_let2, reassoc_inv_beta, seq_let2, wk1_pi_n, pi_n_zero, Term.Eqv.pi_r, pr]
      congr
      exact Term.Eqv.pair_pi_r_pure _ _
    | succ k =>
      simp only [List.get_eq_getElem, List.length_cons, Fin.val_succ, List.getElem_cons_succ, split,
        pair_ltimes_pure, Term.Eqv.nil_seq, wk1_wk2, Term.Subst.Eqv.get_comp,
        Term.Subst.Eqv.get_fromWk, Set.mem_setOf_eq, Ctx.InS.coe_wk1, Nat.liftWk_succ,
        Nat.succ_eq_add_one, subst_var, id_eq, Term.Subst.Eqv.get_unpack, wk_res_self]
      simp only [wk1_rtimes, wk1_pair, wk1_inj_l, wk1_nil]
      simp only [Term.Eqv.rtimes, tensor, Term.Eqv.nil, wk1_var0, List.length_cons, Fin.zero_eta,
        List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, wk0_var, zero_add, wk1_pair,
        wk1_inj_l, seq_assoc_inv, reassoc_inv_let2, reassoc_inv_beta]
      rw [pi_n_succ2']
      conv => lhs; rhs; rw [<-Term.Eqv.seq_assoc, Term.Eqv.seq]
      simp only [List.get_eq_getElem, wk1_seq, wk1_pi_l, wk1_pi_n, subst_let1, subst_lift_seq,
        subst_lift_pi_l, subst_lift_pi_n]
      conv => lhs; lhs; rw [Term.Eqv.pi_l]
      simp only [subst_pl, nil_subst0, wk_eff_let2, wk_eff_var, wk_eff_pair, wk_eff_inj_l, pl_let2]
      rw [Term.Eqv.Pure.pl_pair (hb := by exact ⟨var 0 Ctx.Var.shead, rfl⟩)]
      rw [
        <-Term.Eqv.wk1_pi_l, <-Term.Eqv.wk1_pi_n, <-Term.Eqv.wk1_seq, <-Term.Eqv.seq,
        Term.Eqv.seq_assoc, Term.Eqv.seq_let2
      ]
      simp only [wk1_inj_r, wk_eff_inj_r, wk1_pi_l, Term.Eqv.Pure.inj_r, pair_pi_l, pi_n_succ,
        Term.Eqv.Pure.inj_l, List.get_eq_getElem]
      rfl
  }

theorem Eqv.packed_in_coprod_arr {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)} {r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (l.coprod r).packed_in (Δ := Δ)
  = distl_inv ;; coprod l.packed_in r.packed_in
  := by
  rw [packed_in_coprod_dist, coprod, distl_inv_eq_ret, ret_seq]
  simp
  congr <;> exact vsubst_lift_packed_in.symm

theorem Eqv.packed_in_pack_coprod_arr {Γ : Ctx α ε} {R L : LCtx α}
  {G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (A::L)}
  : (pack_coprod G).packed_in (Δ := Δ)
  = ret (distl_pack (X := Γ.pack))
    ;; pack_coprod (λi => acast R.get_dist ;; (G (i.cast R.length_dist)).packed_in)
  := by induction R generalizing Γ Δ with
  | nil => simp [pack_coprod_empty, packed_in, ret_seq, vwk1]
  | cons B R I =>
    rw [
      pack_coprod_cons, packed_in_coprod_arr, I, Term.Eqv.distl_pack, ret_of_seq,
      distl_inv_eq_ret, seq_assoc, ret_of_coprod, coprod_seq, ret_of_seq,
      seq_assoc
    ]
    congr 3
    · rw [<-inj_l_eq_ret, pack_coprod_cons, inj_l_coprod]; rfl
    · rw [<-inj_r_eq_ret, pack_coprod_cons, inj_r_coprod]; simp

theorem Eqv.packed_out_binary_rtimes {Γ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ ((A, ⊥)::Γ) [B, C]}
  : (D ⋊ r).packed_out (L := L) = D ⋊ r.packed_out ;; distl_inv ;; sum pi_r nil := by
  simp only [LCtx.pack.eq_2, LCtx.pack.eq_1, rtimes, packed_out_let2, packed_out_binary_ret_seq,
    let2_seq, vwk1_distl_inv, vwk1_sum, vwk1_pi_r, nil_vwk1, vwk1_packed_out, seq_assoc]
  congr 2
  simp [<-seq_assoc, ret_seq, distl_inv_eq_ret, pi_r, vwk1_sum, vwk1_let2, vwk3, Nat.liftnWk]
