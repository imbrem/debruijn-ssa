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
  rw [coprod, packed_in_case_split]
  sorry

theorem Eqv.packed_in_coprod_arr {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)} {r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (l.coprod r).packed_in (Δ := Δ)
  = distl_inv ;; coprod l.packed_in r.packed_in
  := by
  rw [coprod, packed_in_case_split, coprod]
  sorry

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
