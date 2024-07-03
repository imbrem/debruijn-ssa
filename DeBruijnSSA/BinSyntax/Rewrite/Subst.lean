import DeBruijnSSA.BinSyntax.Rewrite.Definitions

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

instance Subst.InS.instSetoid {Γ : Ctx α ε} {L K : LCtx α}
  : Setoid (Subst.InS φ Γ L K) where
  r σ τ := ∀i, σ.get i ≈ τ.get i
  iseqv := {
    refl := (λ_ _ => Setoid.refl _)
    symm := (λh i => (h i).symm)
    trans := (λhl hr i => Setoid.trans (hl i) (hr i))
  }

theorem InS.lsubst_congr {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.InS φ Γ L K)
  {r r' : InS φ Γ L} (h : r ≈ r') : r.lsubst σ ≈ r'.lsubst σ := sorry

theorem InS.lsubst_equiv {Γ : Ctx α ε} {L K : LCtx α} {σ τ : Subst.InS φ Γ L K}
  (h : σ ≈ τ)  (r : InS φ Γ L) : r.lsubst σ ≈ r.lsubst τ := sorry

abbrev Subst.Eqv (φ) [EffInstSet φ (Ty α) ε] (Γ : Ctx α ε) (L K : LCtx α)
  := Quotient (α := Subst.InS φ Γ L K) inferInstance

def Eqv.lsubst {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.Eqv φ Γ L K) (r : Eqv φ Γ L)
  : Eqv φ Γ K
  := Quotient.liftOn₂ σ r
    (λσ r => (r.lsubst σ).q)
    sorry

@[simp]
theorem InS.lsubst_q {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K} {r : InS φ Γ L}
   : (r.q).lsubst ⟦σ⟧ = (r.lsubst σ).q := rfl

@[simp]
theorem Eqv.lsubst_quot {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K} {r : InS φ Γ L}
   : lsubst ⟦σ⟧ ⟦r⟧ = ⟦r.lsubst σ⟧ := rfl

end Region
