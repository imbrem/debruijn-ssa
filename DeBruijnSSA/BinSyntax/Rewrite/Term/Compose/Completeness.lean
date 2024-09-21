import DeBruijnSSA.BinSyntax.Rewrite.Term.Structural.Product
import DeBruijnSSA.BinSyntax.Rewrite.Term.Structural.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Distrib

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

theorem Eqv.packed_let1_den {Γ : Ctx α ε} {A B : Ty α}
  {a : Eqv φ Γ (A, e)} {b : Eqv φ ((A, ⊥)::Γ) (B, e)}
  : (let1 a b).packed (Δ := Δ) = Eqv.split ;;' (_ ⋊' a.packed) ;;' b.packed := by
  rw [packed_let1, seq_rtimes, split, let2_pair, nil]
  simp only [wk0_var, zero_add, wk1_packed, let1_beta_var0, subst_let1, var_succ_subst0, subst_pair,
    subst_lift_var_succ, var0_subst0]
  conv => rhs; rw [pair_bind, seq]
  simp [let1_beta_var0, let1_let1]

theorem Eqv.packed_let2_den {Γ : Ctx α ε} {A B C : Ty α}
  {a : Eqv φ Γ (A.prod B, e)} {b : Eqv φ ((B, ⊥)::(A, ⊥)::Γ) (C, e)}
  : (let2 a b).packed (Δ := Δ) = Eqv.split ;;' (_ ⋊' a.packed) ;;' assoc_inv ;;' b.packed := by
  rw [packed_let2, seq_rtimes, split, let2_pair, nil]
  simp only [wk0_var, zero_add, let1_beta_var0, subst_let1, var_succ_subst0, subst_pair,
    subst_lift_var_succ, var0_subst0, List.length_cons, Nat.reduceAdd, Fin.zero_eta,
    List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, wk_res_eff, wk_eff_var]
  rw [seq_assoc_inv, reassoc_inv, let2_pair]
  simp only [seq, let1_beta_var0, subst_let1, subst0_wk0, subst_let2, subst_lift_var_zero,
    subst_pair, subst_liftn₂_var_add_2, subst_lift_var_succ, var0_subst0, List.length_cons,
    Nat.reduceAdd, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
    wk_res_eff, wk_eff_var, wk0_var, zero_add, subst_liftn₂_var_one, ge_iff_le, Prod.mk_le_mk,
    le_refl, bot_le, and_self, subst_liftn₂_var_zero, let1_let1, let1_let2]
  rw [let2_bind]
  simp only [wk2, wk_let1, wk_pair, wk_var, Set.mem_setOf_eq, Ctx.InS.coe_wk2, Nat.liftnWk,
    lt_self_iff_false, ↓reduceIte, le_refl, tsub_eq_zero_of_le, Nat.succ_eq_add_one, zero_add,
    Nat.reduceAdd, Nat.one_lt_ofNat, zero_lt_two, wk1_packed, subst_lift_packed, subst0_var0_packed]
  congr
  exact wk_lift_packed

theorem Eqv.packed_case_den {Γ : Ctx α ε} {A B : Ty α}
  {a : Eqv φ Γ (A.coprod B, e)} {l : Eqv φ ((A, ⊥)::Γ) (C, e)} {r : Eqv φ ((B, ⊥)::Γ) (C, e)}
  : (case a l r).packed (Δ := Δ)
  = Eqv.split ;;' (_ ⋊' a.packed) ;;' distl_inv ;;' coprod l.packed r.packed := by
  rw [packed_case, seq_rtimes, split, let2_pair, nil]
  simp only [wk0_var, zero_add, wk1_packed, let1_beta_var0, subst_let1, var_succ_subst0, subst_pair,
    subst_lift_var_succ, var0_subst0, List.length_cons, Nat.reduceAdd, Fin.zero_eta,
    List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, wk_res_eff, wk_eff_var,
    subst_lift_packed, subst0_var0_packed]
  conv => rhs; rw [distl_inv, seq, seq, let1_pair]
  simp only [let1_beta_let2_eta, nil, coprod, wk1_inl, wk1_pair, wk1_var_succ, zero_add, wk1_var0,
    List.length_cons, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
    wk1_inr, wk1_let2, wk_case, wk_var, Set.mem_setOf_eq, Ctx.InS.coe_liftn₂, Nat.liftnWk,
    zero_lt_two, ↓reduceIte, wk_inl, wk_pair, Ctx.InS.coe_lift, Ctx.InS.coe_wk1, Nat.liftWk_succ,
    Nat.one_lt_ofNat, Nat.reduceAdd, Nat.liftWk_zero, wk_inr, subst_let2, var0_subst0, wk_res_eff,
    wk_eff_pair, wk_eff_var, subst_case, ge_iff_le, Prod.mk_le_mk, le_refl, bot_le, and_self,
    subst_liftn₂_var_zero, subst_inl, subst_pair, subst_lift_var_succ, subst_liftn₂_var_one,
    wk0_var, subst_lift_var_zero, subst_inr, let2_pair, let1_beta_var1, var_succ_subst0,
    ↓dreduceIte, Nat.succ_eq_add_one, Nat.reduceSub, let1_beta_var0, subst_let1, subst0_wk0,
    wk1_packed, wk1_case, wk2_packed, let1_let1, let1_case]
  rw [case_bind]
  congr
  · rw [let1_beta' (a' := (pair (var 2 (by simp)) (var 0 (by simp))).inl) (h := by simp)]
    simp only [subst_case, var0_subst0, List.length_cons, Fin.zero_eta, List.get_eq_getElem,
      Fin.val_zero, List.getElem_cons_zero, wk_res_eff, wk_eff_inl, wk_eff_pair, wk_eff_var,
      case_inl]
    rw [let1_beta' (a' := (pair (var 2 (by simp)) (var 0 (by simp)))) (h := by simp)]
    induction l using Quotient.inductionOn
    apply eq_of_term_eq
    simp only [Set.mem_setOf_eq, InS.coe_wk, Ctx.InS.coe_wk1, InS.coe_subst, InS.coe_subst0,
      InS.coe_pair, InS.coe_var, Subst.InS.coe_unpack, Term.subst_subst, ← Term.subst_fromWk,
      Subst.InS.coe_lift, InS.coe_inl]
    congr
    funext k; simp only [Subst.comp, Term.subst_lift_pi_n, Subst.pi_n, Term.subst_subst]
    apply subst_eqOn_fvi
    intro x
    rw [fvi_pi_n]
    simp only [Set.mem_Iio, Nat.lt_one_iff]
    intro h; cases h; rfl
  · rw [let1_beta' (a' := (pair (var 2 (by simp)) (var 0 (by simp))).inr) (h := by simp)]
    simp only [subst_case, var0_subst0, List.length_cons, Fin.zero_eta, List.get_eq_getElem,
      Fin.val_zero, List.getElem_cons_zero, wk_res_eff, wk_eff_inr, wk_eff_pair, wk_eff_var,
      case_inr]
    rw [let1_beta' (a' := (pair (var 2 (by simp)) (var 0 (by simp)))) (h := by simp)]
    induction r using Quotient.inductionOn
    apply eq_of_term_eq
    simp only [Set.mem_setOf_eq, InS.coe_wk, Ctx.InS.coe_wk1, InS.coe_subst, InS.coe_subst0,
      InS.coe_pair, InS.coe_var, Subst.InS.coe_unpack, Term.subst_subst, ← Term.subst_fromWk,
      Subst.InS.coe_lift, InS.coe_inl]
    congr
    funext k; simp only [Subst.comp, Term.subst_lift_pi_n, Subst.pi_n, Term.subst_subst]
    apply subst_eqOn_fvi
    intro x
    rw [fvi_pi_n]
    simp only [Set.mem_Iio, Nat.lt_one_iff]
    intro h; cases h; rfl

@[simp]
theorem Eqv.packed_inl_den {Γ : Ctx α ε} {A B : Ty α} {a : Eqv φ Γ (A, e)}
  : (inl (B := B) a).packed (Δ := Δ) = a.packed ;;' inj_l := by rw [seq_inj_l, packed_inl]

@[simp]
theorem Eqv.packed_inr_den {Γ : Ctx α ε} {A B : Ty α} {a : Eqv φ Γ (B, e)}
  : (inr (A := A) a).packed (Δ := Δ) = a.packed ;;' inj_r := by rw [seq_inj_r, packed_inr]

@[simp]
theorem Eqv.packed_abort_den {Γ : Ctx α ε} {A : Ty α} {a : Eqv φ Γ (Ty.empty, e)}
  : (abort a A).packed (Δ := Δ) = a.packed ;;' zero := by rw [seq_zero, packed_abort]
