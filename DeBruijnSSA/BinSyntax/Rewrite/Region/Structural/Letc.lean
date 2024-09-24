import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Seq

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

def Eqv.letc {Γ : Ctx α ε} {L : LCtx α}
  (A : Ty α) (β : Eqv φ Γ (A::L)) (G : Eqv φ ((A, ⊥)::Γ) (A::L)) : Eqv φ Γ L
  := Eqv.cfg [A] β (Fin.elim1 G)

theorem Eqv.cfg_eq_letc {Γ : Ctx α ε} {L : LCtx α} {A : Ty α} {β : Eqv φ Γ (A::L)} {G}
  : Eqv.cfg [A] β G = β.letc A (G (0 : Fin 1)) := rfl

@[simp]
theorem Eqv.vwk_letc {Γ Δ : Ctx α ε} {L : LCtx α}
  {A : Ty α} {β : Eqv φ Δ (A::L)} {G : Eqv φ ((A, ⊥)::Δ) (A::L)} {ρ : Γ.InS Δ}
  : (β.letc A G).vwk ρ = (β.vwk ρ).letc A (G.vwk ρ.slift)
  := by rw [letc, vwk_cfg]; rfl

@[simp]
theorem Eqv.vsubst_letc {Γ Δ : Ctx α ε} {L : LCtx α}
  {A : Ty α} {β : Eqv φ Δ (A::L)} {G : Eqv φ ((A, ⊥)::Δ) (A::L)} {σ : Term.Subst.Eqv φ Γ Δ}
  : (β.letc A G).vsubst σ = (β.vsubst σ).letc A (G.vsubst (σ.lift (le_refl _)))
  := by rw [letc, vsubst_cfg]; rfl

@[simp]
theorem Eqv.lwk_letc {Γ : Ctx α ε} {L K : LCtx α}
  {A : Ty α} {β : Eqv φ Γ (A::L)} {G : Eqv φ ((A, ⊥)::Γ) (A::L)} {ρ : L.InS K}
  : (β.letc A G).lwk ρ = (β.lwk ρ.slift).letc A (G.lwk ρ.slift) := by
  rw [letc, lwk_cfg]
  congr
  · ext k; simp [Nat.liftnWk_one]
  · ext i; cases i using Fin.elim1
    simp only [Fin.elim1_zero]
    congr; ext k; simp [Nat.liftnWk_one]

@[simp]
theorem Eqv.lsubst_letc {Γ : Ctx α ε} {L K : LCtx α}
  {A : Ty α} {β : Eqv φ Γ (A::L)} {G : Eqv φ ((A, ⊥)::Γ) (A::L)} {σ : Subst.Eqv φ Γ L K}
  : (β.letc A G).lsubst σ = (β.lsubst σ.slift).letc A (G.lsubst σ.slift.vlift)
  := by rw [letc, lsubst_cfg, Subst.Eqv.liftn_append_singleton]; rfl

theorem Eqv.dinaturality_from_letc {Γ : Ctx α ε} {R L : LCtx α}
  {σ : Subst.Eqv φ Γ R ([B] ++ L)} {β : Eqv φ Γ (R ++ L)}
  {G : Eqv φ (⟨B, ⊥⟩::Γ) (R ++ L)}
  : letc B (β.lsubst σ.extend_in) (G.lsubst σ.extend_in.vlift)
  = cfg R β (λi => (σ.get i).lsubst (Subst.Eqv.fromFCFG_append (L := [B]) (Fin.elim1 G)).vlift)
  := dinaturality (Γ := Γ) (R := R) (R' := [B]) (L := L) (σ := σ) (β := β) (G := Fin.elim1 G)

theorem Eqv.dinaturality_from_letc_rec {Γ : Ctx α ε} {R L : LCtx α}
  {σ : Subst.Eqv φ Γ R [B]} {β : Eqv φ Γ (R ++ L)}
  {G : Eqv φ (⟨B, ⊥⟩::Γ) (R ++ L)}
  : letc B (β.lsubst σ.extend) (G.lsubst σ.extend.vlift)
  = cfg R β (λi => (σ.get i).lsubst (Subst.Eqv.fromFCFG (Fin.elim1 G)).vlift)
  := dinaturality_rec (Γ := Γ) (R := R) (R' := [B]) (L := L) (σ := σ) (β := β) (G := Fin.elim1 G)

theorem Eqv.dinaturality_to_letc {Γ : Ctx α ε} {R' L : LCtx α}
  {σ : Subst.Eqv φ Γ [A] (R' ++ L)} {β : Eqv φ Γ (A::L)}
  {G : (i : Fin R'.length) → Eqv φ (⟨R'.get i, ⊥⟩::Γ) ([A] ++ L)}
  : cfg R' (β.lsubst σ.extend_in) (λi => (G i).lsubst σ.extend_in.vlift)
  = letc A β ((σ.get (0 : Fin 1)).lsubst (Subst.Eqv.fromFCFG_append G).vlift)
  := dinaturality (Γ := Γ) (R := [A]) (R' := R') (L := L) (σ := σ) (β := β) (G := G)

theorem Eqv.dinaturality_to_letc_rec {Γ : Ctx α ε} {R' L : LCtx α}
  {σ : Subst.Eqv φ Γ [A] R'} {β : Eqv φ Γ (A::L)}
  {G : (i : Fin R'.length) → Eqv φ (⟨R'.get i, ⊥⟩::Γ) ([A] ++ L)}
  : cfg R' (β.lsubst σ.extend) (λi => (G i).lsubst σ.extend.vlift)
  = letc A β ((σ.get (0 : Fin 1)).lsubst (Subst.Eqv.fromFCFG G).vlift)
  := dinaturality_rec (Γ := Γ) (R := [A]) (R' := R') (L := L) (σ := σ) (β := β) (G := G)

theorem Eqv.dinaturality_letc {Γ : Ctx α ε} {L : LCtx α}
  {σ : Subst.Eqv φ Γ [A] ([B] ++ L)} {β : Eqv φ Γ (A::L)}
  {G : Eqv φ (⟨B, ⊥⟩::Γ) (A::L)}
  : letc B (β.lsubst σ.extend_in) (G.lsubst σ.extend_in.vlift)
  = letc A β ((σ.get (0 : Fin 1)).lsubst
    (Subst.Eqv.fromFCFG_append (K := [A]) (Fin.elim1 G)).vlift)
  := dinaturality (Γ := Γ) (R := [A]) (R' := [B]) (L := L) (σ := σ) (β := β) (G := Fin.elim1 G)

theorem Eqv.uniform_letc {Γ : Ctx α ε} {L : LCtx α}
  {β : Eqv φ Γ (A::L)} {e : Term.Eqv φ ((A, ⊥)::Γ) (B, ⊥)}
  {r : Eqv φ ((B, ⊥)::Γ) (B::L)} {s : Eqv φ ((A, ⊥)::Γ) (A::L)}
  (hrs : (ret e) ;; r = s ;; (ret e)) : letc B (β.wrseq (ret e)) r = letc A β s := Eqv.uniform hrs

theorem Eqv.wrseq_letc_vwk1 {B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Eqv φ Γ (B::L)} {g : Eqv φ (⟨B, ⊥⟩::Γ) (C::D::L)}
  {h : Eqv φ (⟨C, ⊥⟩::Γ) (C::D::L)}
  : f.wrseq (letc C g h.vwk1) = letc C (f.lwk1.wrseq g) h
  := wrseq_cont f g h

theorem Eqv.seq_letc_vwk1 {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)} {g : Eqv φ (⟨B, ⊥⟩::Γ) (C::D::L)}
  {h : Eqv φ (⟨C, ⊥⟩::Γ) (C::D::L)}
  : f ;; letc C g h.vwk1 = letc C (f.lwk1 ;; g) h.vwk1
  := seq_cont f g h

theorem Eqv.seq_ret_letc_vwk1 {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Term.Eqv φ (⟨A, ⊥⟩::Γ) (B, ⊥)} {g : Eqv φ (⟨B, ⊥⟩::Γ) (C::D::L)}
  {h : Eqv φ (⟨C, ⊥⟩::Γ) (C::D::L)}
  : ret f ;; letc C g h.vwk1 = letc C (ret f ;; g) h.vwk1
  := by rw [seq_letc_vwk1, lwk1_ret]
