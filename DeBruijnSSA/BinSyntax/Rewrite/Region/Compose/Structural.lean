import DeBruijnSSA.BinSyntax.Rewrite.Region.LSubst
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Seq
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Completeness
import DeBruijnSSA.BinSyntax.Typing.Region.Structural

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

def Eqv.unpack {Γ : Ctx α ε} {R : LCtx α} : Eqv φ ((R.pack, ⊥)::Γ) R :=
  match R with
  | [] => loop
  | _::_ => coprod nil unpack.lwk0

theorem Eqv.unpack_def {Γ : Ctx α ε} {R : LCtx α}
  : Eqv.unpack (φ := φ) (Γ := Γ) (R := R) = ⟦InS.unpack (Γ := Γ) (R := R)⟧ := by induction R with
  | nil => rw [unpack, loop_def]; rfl
  | cons _ _ I =>
    rw [unpack, nil, I, lwk0_quot]
    apply Eqv.eq_of_reg_eq
    simp [
      Region.unpack, Region.nil, Region.ret, Region.lwk0, Region.vwk_lwk, Region.vwk_lift_unpack]

@[simp]
theorem Eqv.vwk_lift_unpack {Γ Δ : Ctx α ε} {R : LCtx α} (ρ : Γ.InS Δ)
  : Eqv.vwk (ρ.lift (le_refl _)) (Eqv.unpack (φ := φ) (R := R)) = unpack := by
  rw [unpack_def, vwk_quot, unpack_def]
  apply Eqv.eq_of_reg_eq
  simp

@[simp]
theorem Eqv.vwk1_unpack {Γ : Ctx α ε} {R : LCtx α}
  : (Eqv.unpack (φ := φ) (Γ := Γ) (R := R)).vwk1 (inserted := inserted) = unpack := by
  rw [vwk1, <-Ctx.InS.lift_wk0, vwk_lift_unpack]

@[simp]
theorem Eqv.vsubst_lift_unpack {Γ Δ : Ctx α ε} {R : LCtx α} (σ : Term.Subst.Eqv φ Γ Δ)
  : Eqv.vsubst (σ.lift (le_refl _)) (Eqv.unpack (φ := φ) (R := R)) = Eqv.unpack := by
  induction σ using Quotient.inductionOn
  rw [unpack_def, Term.Subst.Eqv.lift_quot, vsubst_quot, unpack_def]
  apply Eqv.eq_of_reg_eq
  simp

def Subst.Eqv.unpack {Γ : Ctx α ε} {R : LCtx α} : Subst.Eqv φ Γ [R.pack] R
  := Region.Eqv.unpack.csubst

theorem Subst.Eqv.unpack_def {Γ : Ctx α ε} {R : LCtx α}
  : Subst.Eqv.unpack (φ := φ) (Γ := Γ) (R := R) = ⟦InS.unpack (Γ := Γ) (R := R)⟧
  := by rw [unpack, Region.Eqv.unpack_def]; rfl

def Subst.Eqv.pack {Γ : Ctx α ε} {R : LCtx α} : Subst.Eqv φ Γ R [R.pack] := ⟦Subst.InS.pack⟧

@[simp]
theorem Subst.Eqv.pack_get {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : (Subst.Eqv.pack (φ := φ) (Γ := Γ) (R := R)).get i
  = Eqv.br 0 (Term.Eqv.pack_sum R i) LCtx.Trg.shead := by rw [pack, Term.Eqv.pack_sum_def]; rfl

@[simp]
theorem Subst.Eqv.vlift_pack {Γ : Ctx α ε} {R : LCtx α}
  : (pack (φ := φ) (Γ := Γ) (R := R)).vlift (head := head) = pack
  := by simp only [pack, vlift_quot, Subst.InS.vlift_pack]

theorem Eqv.vsubst0_pack_unpack {Γ : Ctx α ε} {R : LCtx α} {ℓ : Fin R.length}
  : (unpack (φ := φ) (Γ := _::Γ) (R := R)).vsubst (Term.Eqv.pack_sum R ℓ).subst0
  = br ℓ (Term.Eqv.var 0 Ctx.Var.shead) (by simp) := by
  induction R with
  | nil => exact ℓ.elim0
  | cons _ _ I =>
    cases ℓ using Fin.cases with
    | zero =>
      simp only [Term.Eqv.pack_sum, Fin.val_succ, Fin.cases_zero, unpack, coprod, vsubst_case,
        Term.Eqv.var0_subst0, Term.Eqv.wk_res_self, case_inl, let1_beta]
      rfl
    | succ ℓ =>
      simp only [
        List.get_eq_getElem, List.length_cons, Fin.val_succ, List.getElem_cons_succ, unpack,
        LCtx.pack.eq_2, Term.Eqv.pack_sum, Fin.val_zero, List.getElem_cons_zero, Fin.cases_succ,
        coprod, vwk1_quot, InS.nil_vwk1, vwk1_lwk0, vwk1_unpack, vsubst_case, Term.Eqv.var0_subst0,
        Fin.zero_eta, Term.Eqv.wk_res_self, vsubst_lwk0, vsubst_lift_unpack, case_inr, let1_beta, I]
      rfl

theorem Subst.Eqv.unpack_comp_pack {Γ : Ctx α ε} {R : LCtx α}
  : Subst.Eqv.unpack.comp Subst.Eqv.pack = Subst.Eqv.id (φ := φ) (Γ := Γ) (L := R)
  := by ext ℓ; simp [get_comp, pack_get, get_id, unpack, Eqv.csubst_get, Eqv.vsubst0_pack_unpack]

-- theorem Eqv.lsubst_pack_unpack {Γ : Ctx α ε} {R : LCtx α}
--   : (unpack (φ := φ) (Γ := Γ) (R := R)).lsubst Subst.Eqv.pack
--   = nil := by
--   induction R with
--   | nil =>
--     apply Eqv.initial
--     sorry -- TODO: context containing empty is trivially initial, add simp lemmas...
--   | cons A R I =>
--     simp only [LCtx.pack.eq_2, unpack, coprod, vwk1_quot, InS.nil_vwk1, vwk1_lwk0, vwk1_unpack,
--       lsubst_case, Subst.Eqv.vlift_pack]
--     apply Eq.trans _ Eqv.sum_nil
--     simp only [sum, coprod]
--     congr
--     -- TODO: lsubst pack lwk0 is lsubst pack ;; inj_r; then follows by induction
--     sorry

-- theorem Subst.Eqv.pack_comp_unpack {Γ : Ctx α ε} {R : LCtx α}
--   : Subst.Eqv.pack.comp Subst.Eqv.unpack = Subst.Eqv.id (φ := φ) (Γ := Γ) (L := [R.pack]) := by
--   ext ℓ
--   induction ℓ using Fin.elim1
--   simp only [unpack, get_comp, vlift_pack, Eqv.csubst_get, Eqv.cast_rfl, Eqv.lsubst_pack_unpack,
--     get_id, Fin.coe_fin_one]
--   rfl

def Eqv.unpacked {Γ : Ctx α ε} {R : LCtx α} (h : Eqv φ Γ [R.pack]) : Eqv φ Γ R
  := h.lsubst Subst.Eqv.unpack

def Eqv.packed {Γ : Ctx α ε} {R : LCtx α} (h : Eqv φ Γ R) : Eqv φ Γ [R.pack]
  := h.lsubst Subst.Eqv.pack

-- theorem Eqv.unpacked_packed {Γ : Ctx α ε} {R : LCtx α} (h : Eqv φ Γ R)
--   : h.packed.unpacked = h := by
--   rw [Eqv.unpacked, packed, lsubst_lsubst, Subst.Eqv.unpack_comp_pack]
--   sorry

end Region

end BinSyntax
