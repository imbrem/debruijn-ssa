import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Sum
import DeBruijnSSA.BinSyntax.Typing.Term.Structural


namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

set_option linter.unusedVariables false in
def Eqv.inj
  {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} (a : Eqv φ Γ (R.get i, e)) : Eqv φ Γ (R.pack, e)
  := match R with
  | [] => i.elim0
  | _::R => by cases i using Fin.cases with | zero => exact a.inr | succ i => exact inl (inj a)

@[simp]
theorem Eqv.inj_quot {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {a : InS φ Γ (R.get i, e)}
  : Eqv.inj ⟦a⟧ = ⟦Term.InS.inj a⟧ := by
  induction R generalizing Γ with
  | nil => exact i.elim0
  | cons _ _ I =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      simp only [inj, I, inl_quot, Fin.cases_succ]
      apply congrArg
      ext
      simp [Term.inj, Term.Wf.inj, -Function.iterate_succ, Function.iterate_succ']

@[simp]
theorem Eqv.wk_inj {Γ Δ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  {a : Eqv φ Δ (R.get i, e)} {ρ : Γ.InS Δ}
  : a.inj.wk ρ = (a.wk ρ).inj := by
  induction a using Quotient.inductionOn
  simp only [inj_quot, wk_quot]
  congr; ext; simp

@[simp]
theorem Eqv.wk0_inj {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  {a : Eqv φ Γ (R.get i, e)} : a.inj.wk0 (head := head) = (a.wk0).inj := wk_inj

@[simp]
theorem Eqv.wk1_inj {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  {a : Eqv φ (V::Γ) (R.get i, e)} : a.inj.wk1 (inserted := inserted) = (a.wk1).inj := wk_inj

@[simp]
theorem Eqv.subst_inj {Γ Δ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  {a : Eqv φ Δ (R.get i, e)} {σ : Subst.Eqv φ Γ Δ}
  : a.inj.subst σ = (a.subst σ).inj := by
  induction a using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  simp only [inj_quot, subst_quot]
  congr; ext; simp

@[simp]
theorem Eqv.inj_zero {Γ : Ctx α ε} {R : LCtx α}
  {a : Eqv φ Γ (List.get (A::R) (0 : Fin (R.length + 1)), e)}
  : a.inj = a.inr := rfl

theorem Eqv.inj_succ {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  {a : Eqv φ Γ (List.get (A::R) i.succ, e)}
  : a.inj = (a.inj (R := R)).inl := rfl

def Eqv.inj_n {Γ : Ctx α ε} (R : LCtx α) (i : Fin R.length) : Eqv φ ((R.get i, ⊥)::Γ) (R.pack, e)
  := match R with
  | [] => i.elim0
  | _::R => i.cases (inr nil) (λi => inl (inj_n R i))

theorem Eqv.inj_n_def {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : Eqv.inj_n (φ := φ) (Γ := Γ) (e := e) R i = ⟦Term.InS.inj_n R i⟧ := by
  induction R generalizing Γ with
  | nil => exact i.elim0
  | cons _ _ I =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      simp only [inj_n, I, inl_quot, Fin.cases_succ]
      apply congrArg
      ext
      simp [Term.inj_n, Term.inj, Term.Wf.inj_n, -Function.iterate_succ, Function.iterate_succ']

theorem Eqv.inj_n_def' {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : Eqv.inj_n (φ := φ) (Γ := Γ) (e := e) R i = nil.inj := by rw [inj_n_def, nil, var, inj_quot]; rfl

-- def Eqv.pack_case {Γ : Ctx α ε} {R : LCtx α}
--   (d : Eqv φ Γ (R.pack, e)) (G : ∀i : Fin R.length, Eqv φ ((R.get i, ⊥)::Γ) (A, e))
--   : Eqv φ Γ (C, e) := sorry

-- def Eqv.pack_app_inl {Γ : Ctx α ε} {L R : LCtx α} : Eqv φ ((L.pack, ⊥)::Γ) ((L ++ R).pack, e)
--   := sorry

-- def Eqv.pack_app_inr {Γ : Ctx α ε} {L R : LCtx α} : Eqv φ ((R.pack, ⊥)::Γ) ((L ++ R).pack, e)
--   := sorry

-- def Eqv.pack_app {Γ : Ctx α ε} {L R : LCtx α}
--   : Eqv φ (((L ++ R).pack, ⊥)::Γ) (L.pack.coprod R.pack, e)
--   := sorry

-- TODO: pack_app

-- TODO: pack_app_pack_case => pack_case

end Term
