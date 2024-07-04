import DeBruijnSSA.BinSyntax.Typing.Region.Basic
import DeBruijnSSA.BinSyntax.Typing.Term.Subst

namespace BinSyntax

section Subst

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]
  {Γ Δ : Ctx α ε} {σ : Term.Subst φ}

def Region.WfD.vsubst {Γ Δ : Ctx α ε} {σ} {r : Region φ} (hσ : σ.WfD Γ Δ)
  : r.WfD Δ L → (r.vsubst σ).WfD Γ L
  | br hL ha => br hL (ha.subst hσ)
  | case he hs ht => case (he.subst hσ) (hs.vsubst hσ.slift) (ht.vsubst hσ.slift)
  | let1 da dt => let1 (da.subst hσ) (dt.vsubst hσ.slift)
  | let2 da dt => let2 (da.subst hσ) (dt.vsubst hσ.sliftn₂)
  | cfg n R hR hr hG => cfg n R hR (hr.vsubst hσ) (λi => (hG i).vsubst hσ.slift)

theorem Region.Wf.vsubst {Γ Δ : Ctx α ε} {σ} {r : Region φ} (hσ : σ.Wf Γ Δ) (h : r.Wf Δ L)
  : (r.vsubst σ).Wf Γ L
  := let ⟨d⟩ := h.nonempty; let ⟨hσ⟩ := hσ.nonempty; (d.vsubst hσ).toWf

def Region.InS.vsubst {Γ Δ : Ctx α ε} (σ : Term.Subst.InS φ Γ Δ) (r : InS φ Δ L) : InS φ Γ L
  := ⟨(r : Region φ).vsubst σ, r.prop.vsubst σ.prop⟩

@[simp]
theorem Region.InS.coe_vsubst {Γ Δ : Ctx α ε} {σ : Term.Subst.InS φ Γ Δ} {r : InS φ Δ L}
  : (r.vsubst σ : Region φ) = (r : Region φ).vsubst σ
  := rfl

theorem Region.InS.vsubst_vsubst {Γ Δ Ξ : Ctx α ε}
  {σ : Term.Subst.InS φ Γ Δ} {τ : Term.Subst.InS φ Δ Ξ}
  (r : InS φ Ξ L) : (r.vsubst τ).vsubst σ = r.vsubst (σ.comp τ)
  := by ext; simp [Region.vsubst_vsubst]

theorem Region.InS.vsubst_equiv {Γ Δ : Ctx α ε} {σ τ : Term.Subst.InS φ Γ Δ}
  (r : InS φ Δ L) (h : σ ≈ τ) : r.vsubst σ = r.vsubst τ
  := sorry
