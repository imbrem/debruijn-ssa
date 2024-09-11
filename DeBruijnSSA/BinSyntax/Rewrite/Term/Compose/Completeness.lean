import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Seq
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Sum
import DeBruijnSSA.BinSyntax.Typing.Region.Structural


namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

def Eqv.pack_sum {Γ : Ctx α ε} (R : LCtx α) (i : Fin R.length) : Eqv φ ((R.get i, ⊥)::Γ) (R.pack, ⊥)
  := match R with
  | [] => i.elim0
  | _::R => i.cases (inl nil) (λi => inr (pack_sum R i))

theorem Eqv.pack_sum_def {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : Eqv.pack_sum (φ := φ) (Γ := Γ) R i = ⟦Term.InS.pack0 R i⟧ := by
  induction R generalizing Γ with
  | nil => exact i.elim0
  | cons _ _ I =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      simp only [pack_sum, I, inr_quot, Fin.cases_succ]
      apply congrArg
      ext
      simp [Term.pack0, Term.Wf.pack0, -Function.iterate_succ, Function.iterate_succ']

def Eqv.pack {Γ : Ctx α ε} : Eqv φ Γ (Γ.pack, Γ.sup_effect) := match Γ with
  | [] => unit ⊥
  | V::Γ => pair (var 0 (by cases V; simp)) ((pack (Γ := Γ)).wk0.wk_eff (by simp))

def _root_.BinSyntax.Ctx.Pure.packE {Γ : Ctx α ε} (h : Γ.Pure) : Eqv φ Γ (Γ.pack, ⊥) := match Γ with
  | [] => Eqv.unit ⊥
  | V::Γ => Eqv.pair (Eqv.var 0 (by cases V; convert h.head; simp)) h.tail.packE.wk0

def Eqv.unpack {Γ Δ : Ctx α ε} (i : Fin Γ.length) : Eqv φ ((Γ.pack, ⊥)::Δ) ((Γ.get i).1, e)
  := match Γ with
  | [] => i.elim0
  | V::Γ => let2
    (var (V := (V.1.prod (Ctx.pack Γ), e)) 0 (by simp [Ctx.pack]))
    (i.cases (var 1 (by simp)) (λi => unpack i))

-- TODO: wk lift unpack

-- TODO: let1 pack (unpack i) = var i

-- TODO: need InS version for this... :(

-- def Subst.Eqv.unpacked {Γ Δ : Ctx α ε} (i : Fin Γ.length) : Subst.Eqv φ ((Γ.pack, ⊥)::Δ) Γ
--   := sorry

end Term
