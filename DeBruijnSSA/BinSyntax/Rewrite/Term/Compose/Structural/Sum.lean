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

-- TODO: pack_inj is just inj (nil)

def Eqv.inj_n {Γ : Ctx α ε} (R : LCtx α) (i : Fin R.length) : Eqv φ ((R.get i, ⊥)::Γ) (R.pack, e)
  := match R with
  | [] => i.elim0
  | _::R => i.cases (inr nil) (λi => inl (inj_n R i))

theorem Eqv.inj_n_def {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : Eqv.inj_n (φ := φ) (Γ := Γ) R i = ⟦Term.InS.inj_n R i⟧ := by
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
