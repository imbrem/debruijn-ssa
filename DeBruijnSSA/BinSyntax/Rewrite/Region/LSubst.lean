import DeBruijnSSA.BinSyntax.Rewrite.Region.Eqv

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

theorem InS.lsubst_congr_subst {Γ : Ctx α ε} {L K : LCtx α} {σ τ : Subst.InS φ Γ L K}
  (h : σ ≈ τ) (r : InS φ Γ L) : r.lsubst σ ≈ r.lsubst τ := sorry

theorem InS.lsubst_congr_right {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.InS φ Γ L K)
  {r r' : InS φ Γ L} (h : r ≈ r') : r.lsubst σ ≈ r'.lsubst σ := sorry

theorem InS.lsubst_congr {Γ : Ctx α ε} {L K : LCtx α} {σ σ' : Subst.InS φ Γ L K}
  {r r' : InS φ Γ L} (hσ : σ ≈ σ') (hr : r ≈ r') : r.lsubst σ ≈ r'.lsubst σ'
  := Setoid.trans (lsubst_congr_subst hσ r) (lsubst_congr_right σ' hr)

abbrev Subst.Eqv (φ) [EffInstSet φ (Ty α) ε] (Γ : Ctx α ε) (L K : LCtx α)
  := Quotient (α := Subst.InS φ Γ L K) inferInstance

def Eqv.lsubst {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.Eqv φ Γ L K) (r : Eqv φ Γ L)
  : Eqv φ Γ K
  := Quotient.liftOn₂ σ r
    (λσ r => (r.lsubst σ).q)
    sorry

def Subst.Eqv.vlift {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.Eqv φ Γ L K)
  : Subst.Eqv φ (head::Γ) L K
  := Quotient.liftOn σ
    (λσ => ⟦σ.vlift⟧)
    sorry

@[simp]
theorem Subst.Eqv.vlift_quot {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K}
  : vlift (head := head) ⟦σ⟧ = ⟦σ.vlift⟧ := rfl

def Subst.Eqv.vliftn₂ {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.Eqv φ Γ L K)
  : Subst.Eqv φ (left::right::Γ) L K
  := Quotient.liftOn σ
    (λσ => ⟦σ.vliftn₂⟧)
    sorry

@[simp]
theorem Subst.Eqv.vliftn₂_quot {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K}
  : vliftn₂ (left := left) (right := right) ⟦σ⟧ = ⟦σ.vliftn₂⟧ := rfl

theorem Subst.Eqv.vliftn₂_eq_vlift_vlift {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.Eqv φ Γ L K)
  : σ.vliftn₂ (left := left) (right := right) = σ.vlift.vlift := by
  induction σ using Quotient.inductionOn;
  simp [Subst.InS.vliftn₂_eq_vlift_vlift]

@[simp]
theorem InS.lsubst_q {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K} {r : InS φ Γ L}
   : (r.q).lsubst ⟦σ⟧ = (r.lsubst σ).q := rfl

@[simp]
theorem Eqv.lsubst_quot {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K} {r : InS φ Γ L}
   : lsubst ⟦σ⟧ ⟦r⟧ = ⟦r.lsubst σ⟧ := rfl

@[simp]
theorem Eqv.lsubst_let1 {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.Eqv φ Γ L K}
  {a : Term.Eqv φ Γ ⟨A, e⟩} {r : Eqv φ (⟨A, ⊥⟩::Γ) L}
  : (let1 a r).lsubst σ = let1 a (r.lsubst σ.vlift) := by
  induction a using Quotient.inductionOn
  induction r using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.lsubst_let2 {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.Eqv φ Γ L K}
  {a : Term.Eqv φ Γ ⟨A.prod B, e⟩} {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  : (let2 a r).lsubst σ = let2 a (r.lsubst σ.vliftn₂) := by
  induction a using Quotient.inductionOn
  induction r using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.lsubst_case {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.Eqv φ Γ L K}
  {a : Term.Eqv φ Γ ⟨A.coprod B, e⟩} {r : Eqv φ (⟨A, ⊥⟩::Γ) L} {s : Eqv φ (⟨B, ⊥⟩::Γ) L}
  : (case a r s).lsubst σ = case a (r.lsubst σ.vlift) (s.lsubst σ.vlift) := by
  induction a using Quotient.inductionOn
  induction r using Quotient.inductionOn
  induction s using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  rfl

-- TODO: lsubst_cfg

def Subst.Eqv.vsubst {Γ Δ : Ctx α ε} {L K : LCtx α}
  (ρ : Term.Subst.Eqv φ Γ Δ) (σ : Subst.Eqv φ Δ L K) : Subst.Eqv φ Γ L K
  := Quotient.liftOn₂ ρ σ (λρ σ => ⟦σ.vsubst ρ⟧) sorry

@[simp]
theorem Subst.Eqv.vsubst_quot {Γ Δ : Ctx α ε} {L K : LCtx α}
  {ρ : Term.Subst.InS φ Γ Δ} {σ : Subst.InS φ Δ L K}
  : vsubst ⟦ρ⟧ ⟦σ⟧ = ⟦σ.vsubst ρ⟧ := rfl

theorem Eqv.vsubst_lsubst {Γ Δ : Ctx α ε}
  {L K : LCtx α} {σ : Subst.Eqv φ Δ L K} {ρ : Term.Subst.Eqv φ Γ Δ}
  {r : Eqv φ Δ L}
  : (r.lsubst σ).vsubst ρ = (r.vsubst ρ).lsubst (σ.vsubst ρ)
  := by
  induction σ using Quotient.inductionOn
  induction ρ using Quotient.inductionOn
  induction r using Quotient.inductionOn
  simp [InS.vsubst_lsubst]

end Region
