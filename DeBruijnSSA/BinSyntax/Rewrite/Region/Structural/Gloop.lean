import DeBruijnSSA.BinSyntax.Rewrite.Region.LSubst

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

def Eqv.gloop {Γ : Ctx α ε} {L : LCtx α}
  (A : Ty α) (β : Eqv φ Γ (A::L)) (G : Eqv φ ((A, ⊥)::Γ) (A::L)) : Eqv φ Γ L
  := Eqv.cfg [A] β (Fin.elim1 G)

theorem Eqv.cfg_eq_gloop {Γ : Ctx α ε} {L : LCtx α} {A : Ty α} {β : Eqv φ Γ (A::L)} {G}
  : Eqv.cfg [A] β G = β.gloop A (G (0 : Fin 1)) := rfl

@[simp]
theorem Eqv.vwk_gloop {Γ Δ : Ctx α ε} {L : LCtx α}
  {A : Ty α} {β : Eqv φ Δ (A::L)} {G : Eqv φ ((A, ⊥)::Δ) (A::L)} {ρ : Γ.InS Δ}
  : (β.gloop A G).vwk ρ = (β.vwk ρ).gloop A (G.vwk ρ.slift)
  := by rw [gloop, vwk_cfg]; rfl

@[simp]
theorem Eqv.vsubst_gloop {Γ Δ : Ctx α ε} {L : LCtx α}
  {A : Ty α} {β : Eqv φ Δ (A::L)} {G : Eqv φ ((A, ⊥)::Δ) (A::L)} {σ : Term.Subst.Eqv φ Γ Δ}
  : (β.gloop A G).vsubst σ = (β.vsubst σ).gloop A (G.vsubst (σ.lift (le_refl _)))
  := by rw [gloop, vsubst_cfg]; rfl

@[simp]
theorem Eqv.lwk_gloop {Γ : Ctx α ε} {L K : LCtx α}
  {A : Ty α} {β : Eqv φ Γ (A::L)} {G : Eqv φ ((A, ⊥)::Γ) (A::L)} {ρ : L.InS K}
  : (β.gloop A G).lwk ρ = (β.lwk ρ.slift).gloop A (G.lwk ρ.slift) := by
  rw [gloop, lwk_cfg]
  congr
  · ext k; simp [Nat.liftnWk_one]
  · ext i; cases i using Fin.elim1
    simp only [Fin.elim1_zero]
    congr; ext k; simp [Nat.liftnWk_one]

@[simp]
theorem Eqv.lsubst_gloop {Γ : Ctx α ε} {L K : LCtx α}
  {A : Ty α} {β : Eqv φ Γ (A::L)} {G : Eqv φ ((A, ⊥)::Γ) (A::L)} {σ : Subst.Eqv φ Γ L K}
  : (β.gloop A G).lsubst σ = (β.lsubst σ.slift).gloop A (G.lsubst σ.slift.vlift)
  := by rw [gloop, lsubst_cfg, Subst.Eqv.liftn_append_singleton]; rfl

theorem Eqv.dinaturality_from_gloop {Γ : Ctx α ε} {R L : LCtx α}
  {σ : Subst.Eqv φ Γ R ([B] ++ L)} {β : Eqv φ Γ (R ++ L)}
  {G : Eqv φ (⟨B, ⊥⟩::Γ) (R ++ L)}
  : gloop B (β.lsubst σ.extend_in) (G.lsubst σ.extend_in.vlift)
  = cfg R β (λi => (σ.get i).lsubst (Subst.Eqv.fromFCFG_append (L := [B]) (Fin.elim1 G)).vlift)
  := dinaturality (Γ := Γ) (R := R) (R' := [B]) (L := L) (σ := σ) (β := β) (G := Fin.elim1 G)

theorem Eqv.dinaturality_from_gloop_rec {Γ : Ctx α ε} {R L : LCtx α}
  {σ : Subst.Eqv φ Γ R [B]} {β : Eqv φ Γ (R ++ L)}
  {G : Eqv φ (⟨B, ⊥⟩::Γ) (R ++ L)}
  : gloop B (β.lsubst σ.extend) (G.lsubst σ.extend.vlift)
  = cfg R β (λi => (σ.get i).lsubst (Subst.Eqv.fromFCFG (Fin.elim1 G)).vlift)
  := dinaturality_rec (Γ := Γ) (R := R) (R' := [B]) (L := L) (σ := σ) (β := β) (G := Fin.elim1 G)

theorem Eqv.dinaturality_to_gloop {Γ : Ctx α ε} {R' L : LCtx α}
  {σ : Subst.Eqv φ Γ [A] (R' ++ L)} {β : Eqv φ Γ (A::L)}
  {G : (i : Fin R'.length) → Eqv φ (⟨R'.get i, ⊥⟩::Γ) ([A] ++ L)}
  : cfg R' (β.lsubst σ.extend_in) (λi => (G i).lsubst σ.extend_in.vlift)
  = gloop A β ((σ.get (0 : Fin 1)).lsubst (Subst.Eqv.fromFCFG_append G).vlift)
  := dinaturality (Γ := Γ) (R := [A]) (R' := R') (L := L) (σ := σ) (β := β) (G := G)

theorem Eqv.dinaturality_to_gloop_rec {Γ : Ctx α ε} {R' L : LCtx α}
  {σ : Subst.Eqv φ Γ [A] R'} {β : Eqv φ Γ (A::L)}
  {G : (i : Fin R'.length) → Eqv φ (⟨R'.get i, ⊥⟩::Γ) ([A] ++ L)}
  : cfg R' (β.lsubst σ.extend) (λi => (G i).lsubst σ.extend.vlift)
  = gloop A β ((σ.get (0 : Fin 1)).lsubst (Subst.Eqv.fromFCFG G).vlift)
  := dinaturality_rec (Γ := Γ) (R := [A]) (R' := R') (L := L) (σ := σ) (β := β) (G := G)

theorem Eqv.dinaturality_gloop {Γ : Ctx α ε} {L : LCtx α}
  {σ : Subst.Eqv φ Γ [A] ([B] ++ L)} {β : Eqv φ Γ (A::L)}
  {G : Eqv φ (⟨B, ⊥⟩::Γ) (A::L)}
  : gloop B (β.lsubst σ.extend_in) (G.lsubst σ.extend_in.vlift)
  = gloop A β ((σ.get (0 : Fin 1)).lsubst
    (Subst.Eqv.fromFCFG_append (K := [A]) (Fin.elim1 G)).vlift)
  := dinaturality (Γ := Γ) (R := [A]) (R' := [B]) (L := L) (σ := σ) (β := β) (G := Fin.elim1 G)
