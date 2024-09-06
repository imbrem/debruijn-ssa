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

@[simp]
theorem Region.InS.vsubst_br {Γ Δ : Ctx α ε} {L : LCtx α}
  {σ : Term.Subst.InS φ Γ Δ} {ℓ} {a : Term.InS φ Δ (A, ⊥)} {hℓ : L.Trg ℓ A}
  : (br ℓ a hℓ).vsubst σ = br ℓ (a.subst σ) hℓ
  := rfl

@[simp]
theorem Region.InS.vsubst_let1 {Γ Δ : Ctx α ε} {L : LCtx α}
  {σ : Term.Subst.InS φ Γ Δ} {a : Term.InS φ Δ ⟨A, e⟩} {r : InS φ (⟨A, ⊥⟩::Δ) L}
  : (let1 a r).vsubst σ = let1 (a.subst σ) (r.vsubst (σ.lift (le_refl _)))
  := rfl

@[simp]
theorem Region.InS.vsubst_let2 {Γ Δ : Ctx α ε} {L : LCtx α}
  {σ : Term.Subst.InS φ Γ Δ} {a : Term.InS φ Δ ⟨Ty.prod A B, e⟩} {r : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Δ) L}
  : (let2 a r).vsubst σ = let2 (a.subst σ) (r.vsubst (σ.liftn₂ (le_refl _) (le_refl _)))
  := rfl

@[simp]
theorem Region.InS.vsubst_case {Γ Δ : Ctx α ε} {L : LCtx α}
  {σ : Term.Subst.InS φ Γ Δ} {e : Term.InS φ Δ ⟨Ty.coprod A B, e⟩}
  {r : InS φ (⟨A, ⊥⟩::Δ) L} {s : InS φ (⟨B, ⊥⟩::Δ) L}
  : (case e r s).vsubst σ = case (e.subst σ)
    (r.vsubst (σ.lift (le_refl _))) (s.vsubst (σ.lift (le_refl _)))
  := rfl

@[simp]
theorem Region.InS.vsubst_cfg {Γ Δ : Ctx α ε} {L : LCtx α}
  {σ : Term.Subst.InS φ Γ Δ} {R : LCtx α} {β : InS φ Δ (R ++ L)}
  {G : (i : Fin R.length) → InS φ ((R[i], ⊥)::Δ) (R ++ L)}
  : (cfg R β G).vsubst σ = cfg R (β.vsubst σ) (λi => (G i).vsubst (σ.lift (le_refl _)))
  := rfl

theorem Region.InS.vsubst_vsubst {Γ Δ Ξ : Ctx α ε}
  {σ : Term.Subst.InS φ Γ Δ} {τ : Term.Subst.InS φ Δ Ξ}
  (r : InS φ Ξ L) : (r.vsubst τ).vsubst σ = r.vsubst (σ.comp τ)
  := by ext; simp [Region.vsubst_vsubst]

theorem Region.InS.vsubst_toSubst {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ} {L} {r : InS φ Δ L}
  : r.vsubst ρ.toSubst = r.vwk ρ := by ext; simp [Region.vsubst_fromWk]

@[simp]
theorem Region.InS.vsubst0_vwk0 {Γ : Ctx α ε} {L} {r : InS φ Γ L} {a : Term.InS φ Γ V}
  : r.vwk0.vsubst a.subst0 = r := by ext; simp [vwk0, <-Region.vsubst_fromWk, Region.vsubst_vsubst]
