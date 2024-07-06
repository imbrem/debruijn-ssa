import DeBruijnSSA.BinSyntax.Typing.Region
import DeBruijnSSA.BinSyntax.Rewrite.Region.Cong
import DeBruijnSSA.BinSyntax.Rewrite.Region.Step
import DeBruijnSSA.BinSyntax.Rewrite.Region.Uniform
import DeBruijnSSA.BinSyntax.Rewrite.Region.Setoid

import Discretion.Utils.Quotient

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

-- TODO: rewrite to use subst.cons...

-- def Term.WfD.subst₂ {Γ : Ctx α ε} {a b : Term φ}
--   (ha : a.WfD Γ ⟨A, e⟩) (hb : b.WfD Γ ⟨B, e'⟩)
--   : (a.subst₂ b).WfD Γ (⟨A, e⟩::⟨B, e'⟩::Γ)
--   | ⟨0, _⟩ => ha
--   | ⟨1, _⟩ => hb
--   | ⟨n + 2, h⟩ => var ⟨by simp at h; exact h, le_refl _⟩

namespace Region

def Eqv (φ) [EffInstSet φ (Ty α) ε] (Γ : Ctx α ε) (L : LCtx α) := Quotient (InS.Setoid φ Γ L)

def Eqv.cast {Γ : Ctx α ε} {L : LCtx α} (hΓ : Γ = Γ') (hL : L = L') (r : Eqv φ Γ L)
  : Eqv φ Γ' L' := hΓ ▸ hL ▸ r

def InS.q (a : InS φ Γ L) : Eqv φ Γ L := Quotient.mk _ a

theorem Eqv.inductionOn {Γ : Ctx α ε} {L : LCtx α} {motive : Eqv φ Γ L → Prop}
  (r : Eqv φ Γ L) (h : ∀a : InS φ Γ L, motive a.q) : motive r := Quotient.inductionOn r h

theorem Eqv.sound {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ Γ L}
  (h : r ≈ r') : r.q = r'.q := Quotient.sound h

theorem Eqv.eq {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ Γ L}
  : r.q = r'.q ↔ r ≈ r' := Quotient.eq

def Eqv.let1 (a : Term.InS φ Γ ⟨A, e⟩) (r : Eqv φ (⟨A, ⊥⟩::Γ) L) : Eqv φ Γ L
  := Quotient.liftOn r (λr => InS.q (r.let1 a)) (λ_ _ h => Quotient.sound (InS.let1_congr a h))

theorem Eqv.quot_def {Γ : Ctx α ε} {L : LCtx α} {r : InS φ Γ L}
  : ⟦r⟧ = r.q := rfl

@[simp]
theorem InS.let1_q {a : Term.InS φ Γ ⟨A, e⟩} {r : InS φ (⟨A, ⊥⟩::Γ) L}
  : r.q.let1 a = (r.let1 a).q := rfl

@[simp]
theorem Eqv.let1_quot {a : Term.InS φ Γ ⟨A, e⟩} {r : InS φ (⟨A, ⊥⟩::Γ) L}
  : let1 a ⟦r⟧ = ⟦r.let1 a⟧ := rfl

def Eqv.let2 (a : Term.InS φ Γ ⟨Ty.prod A B, e⟩) (r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L) : Eqv φ Γ L
  := Quotient.liftOn r (λr => InS.q (r.let2 a)) (λ_ _ h => Quotient.sound (InS.let2_congr a h))

@[simp]
theorem InS.let2_q {a : Term.InS φ Γ ⟨Ty.prod A B, e⟩} {r : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  : r.q.let2 a = (r.let2 a).q := rfl

@[simp]
theorem Eqv.let2_quot {a : Term.InS φ Γ ⟨Ty.prod A B, e⟩} {r : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  : let2 a ⟦r⟧ = ⟦r.let2 a⟧ := rfl

def Eqv.case
  (e : Term.InS φ Γ ⟨Ty.coprod A B, e⟩) (r : Eqv φ (⟨A, ⊥⟩::Γ) L) (s : Eqv φ (⟨B, ⊥⟩::Γ) L)
  : Eqv φ Γ L := Quotient.liftOn₂ r s (λr s => InS.q (InS.case e r s))
    (λ_ _ _ _ h1 h2 => Quotient.sound (InS.case_congr h1 h2))

@[simp]
theorem InS.case_q {e : Term.InS φ Γ ⟨Ty.coprod A B, e⟩}
  {r : InS φ (⟨A, ⊥⟩::Γ) L} {s : InS φ (⟨B, ⊥⟩::Γ) L}
  : (r.q).case e s.q = (r.case e s).q := rfl

@[simp]
theorem Eqv.case_quot {e : Term.InS φ Γ ⟨Ty.coprod A B, e⟩}
  {r : InS φ (⟨A, ⊥⟩::Γ) L} {s : InS φ (⟨B, ⊥⟩::Γ) L}
  : case e ⟦r⟧ ⟦s⟧ = ⟦r.case e s⟧ := rfl

def Eqv.cfg_inner
  (R : LCtx α)
  (β : Eqv φ Γ (R ++ L)) (G : Quotient (α := ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)) inferInstance)
  : Eqv φ Γ L := Quotient.liftOn₂ β G
    (λβ G => InS.q (InS.cfg R β G)) (λ_ _ _ _ h1 h2 => Quotient.sound (InS.cfg_congr R h1 h2))

def Eqv.cfg
  (R : LCtx α)
  (β : Eqv φ Γ (R ++ L)) (G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : Eqv φ Γ L := cfg_inner R β (Quotient.finChoice G)

def Eqv.cfg_inner'
  (n : ℕ) (R : LCtx α) (hR : R.length = n)
  (β : Eqv φ Γ (R ++ L))
  (G : Quotient (α := ∀i : Fin n, InS φ (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) inferInstance)
  : Eqv φ Γ L := Quotient.liftOn₂ β G
    (λβ G => InS.q (InS.cfg' n R hR β G))
    (λ_ _ _ _ h1 h2 => Quotient.sound (InS.cfg_congr' n R hR h1 h2))

def Eqv.cfg'
  (n : ℕ) (R : LCtx α) (hR : R.length = n)
  (β : Eqv φ Γ (R ++ L))
  (G : ∀i : Fin n, Eqv φ (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L))
  : Eqv φ Γ L := cfg_inner' n R hR β (Quotient.finChoice G)

@[simp]
theorem InS.cfg_inner_q
  {R : LCtx α} {β : InS φ Γ (R ++ L)}
  {G : ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : (β.q).cfg_inner R ⟦G⟧ = (β.cfg R G).q
  := by simp [Eqv.cfg_inner, q]

@[simp]
theorem Eqv.cfg_inner_quot
  {R : LCtx α} {β : InS φ Γ (R ++ L)}
  {G : ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : cfg_inner R ⟦β⟧ ⟦G⟧ = ⟦InS.cfg R β G⟧ := rfl

@[simp]
theorem InS.cfg_q {R : LCtx α} {β : InS φ Γ (R ++ L)} {G : ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : (β.q).cfg R (λi => (G i).q) = (β.cfg R G).q
  := by simp [Eqv.cfg, Eqv.cfg_inner, q, Quotient.finChoice_eq]

@[simp]
theorem Eqv.cfg_quot
  {R : LCtx α} {β : InS φ Γ (R ++ L)} {G : ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : cfg R ⟦β⟧ (λi => ⟦G i⟧) = ⟦InS.cfg R β G⟧ := InS.cfg_q

def Eqv.vwk
  {Γ Δ : Ctx α ε} {L : LCtx α} (ρ : Γ.InS Δ) (r : Eqv φ Δ L)
  : Eqv φ Γ L := Quotient.liftOn r
    (λr => InS.q (r.vwk ρ))
    (λ_ _ h => Quotient.sound (InS.vwk_congr ρ h))

def Eqv.vwk_id
  {Γ Δ : Ctx α ε} {L : LCtx α} (hρ : Γ.Wkn Δ id) (r : Eqv φ Δ L)
  : Eqv φ Γ L := Quotient.liftOn r
    (λr => InS.q (r.vwk_id hρ))
    (λ_ _ h => Quotient.sound (by
      have h := InS.vwk_congr ⟨id, hρ⟩ h;
      simp only [InS.vwk, Set.mem_setOf_eq, vwk_of_id, id_eq, InS.vwk_id] at *
      exact h
      ))

def Eqv.lwk {Γ : Ctx α ε} {L K : LCtx α} (ρ : L.InS K) (r : Eqv φ Γ L)
  : Eqv φ Γ K := Quotient.liftOn r
    (λr => InS.q (r.lwk ρ))
    (λ_ _ h => Quotient.sound sorry)

def Eqv.lwk_id {Γ : Ctx α ε} {L K : LCtx α} (hρ : L.Wkn K id) (r : Eqv φ Γ L)
  : Eqv φ Γ K := Quotient.liftOn r
    (λr => InS.q (r.lwk_id hρ))
    (λ_ _ h => Quotient.sound sorry)

def Eqv.vsubst {Γ Δ : Ctx α ε} {L : LCtx α} (σ : Term.Subst.InS φ Γ Δ) (r : Eqv φ Δ L)
  : Eqv φ Γ L := Quotient.liftOn r
    (λr => InS.q (r.vsubst σ))
    (λ_ _ h => Quotient.sound sorry)

@[simp]
theorem InS.vwk_q {Γ Δ : Ctx α ε} {L : LCtx α} {ρ : Γ.InS Δ} {r : InS φ Δ L}
   : (r.q).vwk ρ = (r.vwk ρ).q := rfl

@[simp]
theorem Eqv.vwk_quot {Γ Δ : Ctx α ε} {L : LCtx α} {ρ : Γ.InS Δ} {r : InS φ Δ L}
   : Eqv.vwk ρ ⟦r⟧ = ⟦r.vwk ρ⟧ := rfl

@[simp]
theorem InS.vwk_id_q {Γ Δ : Ctx α ε} {L : LCtx α} {r : InS φ Δ L}
  (hρ : Γ.Wkn Δ id) : (r.q).vwk_id hρ = (r.vwk_id hρ).q := rfl

@[simp]
theorem Eqv.vwk_id_quot {Γ Δ : Ctx α ε} {L : LCtx α} {r : InS φ Δ L}
  (hρ : Γ.Wkn Δ id) : Eqv.vwk_id hρ ⟦r⟧ = ⟦r.vwk_id hρ⟧ := rfl

theorem Eqv.vwk_vwk {Γ Δ Ξ : Ctx α ε} {L : LCtx α} {r : Eqv φ Ξ L}
  (ρ : Γ.InS Δ) (σ : Δ.InS Ξ)
  : Eqv.vwk ρ (Eqv.vwk σ r) = Eqv.vwk (ρ.comp σ) r := by
  induction r using Quotient.inductionOn; simp [InS.vwk_vwk]

@[simp]
theorem Eqv.vwk_let1 {Γ : Ctx α ε} {L : LCtx α}
  {ρ : Γ.InS Δ} {a : Term.InS φ Δ ⟨A, e⟩} {r : Eqv φ (⟨A, ⊥⟩::Δ) L}
  : Eqv.vwk ρ (Eqv.let1 a r) = Eqv.let1 (a.wk ρ) (Eqv.vwk (ρ.lift (le_refl _)) r) := by
  induction r using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.vwk_let2 {Γ : Ctx α ε} {L : LCtx α}
  {ρ : Γ.InS Δ} {a : Term.InS φ Δ ⟨Ty.prod A B, e⟩} {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Δ) L}
  : Eqv.vwk ρ (Eqv.let2 a r)
  = Eqv.let2 (a.wk ρ) (Eqv.vwk (ρ.liftn₂ (le_refl _) (le_refl _)) r) := by
  induction r using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.vwk_case {Γ : Ctx α ε} {L : LCtx α}
  {ρ : Γ.InS Δ} {e : Term.InS φ Δ ⟨Ty.coprod A B, e⟩}
  {r : Eqv φ (⟨A, ⊥⟩::Δ) L} {s : Eqv φ (⟨B, ⊥⟩::Δ) L}
  : Eqv.vwk ρ (Eqv.case e r s)
  = Eqv.case (e.wk ρ) (Eqv.vwk (ρ.lift (le_refl _)) r) (Eqv.vwk (ρ.lift (le_refl _)) s) := by
  induction r using Quotient.inductionOn; induction s using Quotient.inductionOn; rfl

-- @[simp]
-- theorem Eqv.vwk_cfg {Γ : Ctx α ε} {L : LCtx α}
--   {R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
--   {ρ : Γ.InS Δ}
--   : Eqv.vwk ρ (Eqv.cfg R β G)
--   = Eqv.cfg R (Eqv.vwk (ρ.lift (le_refl _)) β) sorry := by
--   stop induction β using Quotient.inductionOn; simp [Eqv.cfg, Eqv.cfg_inner, Quotient.finChoice_eq]

@[simp]
theorem InS.lwk_q {Γ : Ctx α ε} {L K : LCtx α} {ρ : L.InS K} {r : InS φ Γ L}
   : (r.q).lwk ρ = (r.lwk ρ).q := rfl

@[simp]
theorem Eqv.lwk_quot {Γ : Ctx α ε} {L K : LCtx α} {ρ : L.InS K} {r : InS φ Γ L}
   : Eqv.lwk ρ ⟦r⟧ = ⟦r.lwk ρ⟧ := rfl

@[simp]
theorem InS.vsubst_q {Γ Δ : Ctx α ε} {L : LCtx α} {σ : Term.Subst.InS φ Γ Δ} {r : InS φ Δ L}
   : (r.q).vsubst σ = (r.vsubst σ).q := rfl

@[simp]
theorem Eqv.vsubst_quot {Γ Δ : Ctx α ε} {L : LCtx α} {σ : Term.Subst.InS φ Γ Δ} {r : InS φ Δ L}
   : Eqv.vsubst σ ⟦r⟧ = ⟦r.vsubst σ⟧ := rfl

theorem Eqv.vsubst_vsubst {Γ Δ Ξ : Ctx α ε} {L : LCtx α} {r : Eqv φ Ξ L}
  {σ : Term.Subst.InS φ Γ Δ} {τ : Term.Subst.InS φ Δ Ξ}
  : (r.vsubst τ).vsubst σ = r.vsubst (σ.comp τ) := by
  induction r using Quotient.inductionOn;
  simp [InS.vsubst_vsubst]

@[simp]
theorem Eqv.vsubst_let1 {Γ : Ctx α ε} {L : LCtx α}
  {σ : Term.Subst.InS φ Γ Δ} {a : Term.InS φ Δ ⟨A, e⟩} {r : Eqv φ (⟨A, ⊥⟩::Δ) L}
  : Eqv.vsubst σ (Eqv.let1 a r) = Eqv.let1 (a.subst σ) (Eqv.vsubst (σ.lift (le_refl _)) r) := by
  induction r using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.vsubst_let2 {Γ : Ctx α ε} {L : LCtx α}
  {σ : Term.Subst.InS φ Γ Δ} {a : Term.InS φ Δ ⟨Ty.prod A B, e⟩} {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Δ) L}
  : Eqv.vsubst σ (Eqv.let2 a r)
  = Eqv.let2 (a.subst σ) (Eqv.vsubst (σ.liftn₂ (le_refl _) (le_refl _)) r) := by
  induction r using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.vsubst_case {Γ : Ctx α ε} {L : LCtx α}
  {σ : Term.Subst.InS φ Γ Δ} {e : Term.InS φ Δ ⟨Ty.coprod A B, e⟩}
  {r : Eqv φ (⟨A, ⊥⟩::Δ) L} {s : Eqv φ (⟨B, ⊥⟩::Δ) L}
  : Eqv.vsubst σ (Eqv.case e r s)
  = Eqv.case (e.subst σ) (Eqv.vsubst (σ.lift (le_refl _)) r) (Eqv.vsubst (σ.lift (le_refl _)) s)
  := by induction r using Quotient.inductionOn; induction s using Quotient.inductionOn; rfl

@[simp]
theorem InS.lwk_id_q {Γ : Ctx α ε} {L K : LCtx α} {r : InS φ Γ L}
  (hρ : L.Wkn K id) : (r.q).lwk_id hρ = (r.lwk_id hρ).q := rfl

@[simp]
theorem InS.lwk_id_quot {Γ : Ctx α ε} {L K : LCtx α} {r : InS φ Γ L}
  (hρ : L.Wkn K id) : Eqv.lwk_id hρ ⟦r⟧ = ⟦r.lwk_id hρ⟧ := rfl

theorem Eqv.lwk_lwk {Γ : Ctx α ε} {L K J : LCtx α}
  {ρ : L.InS K} {σ : K.InS J}
  {r : Eqv φ Γ L}
  : (r.lwk ρ).lwk σ = r.lwk (σ.comp ρ) := by
  induction r using Quotient.inductionOn; simp [InS.lwk_lwk]

theorem Eqv.lwk_vwk {Γ Δ : Ctx α ε} {L K : LCtx α}
  {ρ : L.InS K} {σ : Γ.InS Δ}
  {r : Eqv φ Δ L}
  : (r.vwk σ).lwk ρ = (r.lwk ρ).vwk σ := by
  induction r using Quotient.inductionOn; simp [InS.lwk_vwk]

theorem Eqv.vwk_lwk {Γ Δ : Ctx α ε} {L K : LCtx α}
  {ρ : L.InS K} {σ : Γ.InS Δ}
  {r : Eqv φ Δ L}
  : (r.lwk ρ).vwk σ = (r.vwk σ).lwk ρ := by
  induction r using Quotient.inductionOn; simp [InS.vwk_lwk]

def Eqv.vwk0
  {Γ : Ctx α ε} {L : LCtx α} (r : Eqv φ Γ L)
  : Eqv φ (head::Γ) L := Eqv.vwk ⟨Nat.succ, by simp⟩ r

@[simp]
theorem InS.vwk0_q {Γ : Ctx α ε} {L : LCtx α} {r : InS φ Γ L}
  : (r.q).vwk0 (head := head) = (r.vwk0).q := rfl

@[simp]
theorem Eqv.vwk0_quot {Γ : Ctx α ε} {L : LCtx α} {r : InS φ Γ L}
  : Eqv.vwk0 (head := head) ⟦r⟧ = ⟦r.vwk0⟧ := rfl

def Eqv.vwk1
  {Γ : Ctx α ε} {L : LCtx α} (r : Eqv φ (head::Γ) L)
  : Eqv φ (head::inserted::Γ) L := Eqv.vwk ⟨Nat.liftWk Nat.succ, by simp⟩ r

@[simp]
theorem InS.vwk1_q {Γ : Ctx α ε} {L : LCtx α} {r : InS φ (head::Γ) L}
  : (r.q).vwk1 (inserted := inserted) = (r.vwk1).q := rfl

@[simp]
theorem Eqv.vwk1_quot {Γ : Ctx α ε} {L : LCtx α} {r : InS φ (head::Γ) L}
  : Eqv.vwk1 (inserted := inserted) ⟦r⟧ = ⟦r.vwk1⟧ := rfl

theorem Eqv.lwk_vwk1 {Γ : Ctx α ε} {L K : LCtx α} {ρ : L.InS K}
  {r : Eqv φ (head::Γ) L}
  : (r.vwk1 (inserted := inserted)).lwk ρ = (r.lwk ρ).vwk1 := by
  induction r using Quotient.inductionOn; simp [InS.lwk_vwk1]

theorem Eqv.vwk1_lwk {Γ : Ctx α ε} {L K : LCtx α} {ρ : L.InS K}
  {r : Eqv φ (head::Γ) L}
  : (r.lwk ρ).vwk1 = (r.vwk1 (inserted := inserted)).lwk ρ := by
  induction r using Quotient.inductionOn; simp [InS.vwk1_lwk]

theorem Eqv.let1_op {Γ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨B, ⊥⟩::Γ) L}
  (f : φ) (hf : Φ.EFn f A B e)
  (a : Term.InS φ Γ ⟨A, e⟩)
    : Eqv.let1 (a.op f hf) r = (r.vwk1.let1 ((Term.InS.var 0 (by simp)).op f hf)).let1 a
  := by induction r using Quotient.inductionOn with
  | h r =>
    simp only [let1_quot, vwk1_quot]
    apply Eqv.sound
    apply InS.let1_op

theorem Eqv.let1_let1 {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
  {r : Eqv φ (⟨B, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩) (b : Term.InS φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩)
    : Eqv.let1 (a.let1 b) r = (let1 a $ let1 b $ r.vwk1)
  := by induction r using Quotient.inductionOn with
  | h r =>
    simp only [let1_quot, vwk1_quot]
    apply Eqv.sound
    apply InS.let1_let1

theorem Eqv.let1_pair {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α} (e' := ⊥)
  {r : Eqv φ (⟨Ty.prod A B, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩) (b : Term.InS φ Γ ⟨B, e⟩)
    : Eqv.let1 (a.pair b) r = (
      let1 a $
      let1 (b.wk ⟨Nat.succ, (by simp)⟩) $
      let1 ((Term.InS.var 1 (by simp)).pair (e := e') (Term.InS.var 0 (by simp))) $
      r.vwk1.vwk1)
  := by induction r using Quotient.inductionOn with
  | h r =>
    simp only [let1_quot, vwk1_quot]
    apply Eqv.sound
    apply InS.let1_pair

theorem Eqv.let1_inl {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α} (e' := ⊥)
  {r : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩)
    : Eqv.let1 a.inl r
    = (r.vwk1.let1 ((Term.InS.var 0 (by simp)).inl (e := e'))).let1 a
  := by induction r using Quotient.inductionOn with
  | h r =>
    simp only [let1_quot, vwk1_quot]
    apply Eqv.sound
    apply InS.let1_inl

theorem Eqv.let1_inr {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α} (e' := ⊥)
  {r : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) L}
  (b : Term.InS φ Γ ⟨B, e⟩)
    : Eqv.let1 b.inr r
    = (r.vwk1.let1 ((Term.InS.var 0 (by simp)).inr (e := e'))).let1 b
  := by induction r using Quotient.inductionOn with
  | h r =>
    simp only [let1_quot, vwk1_quot]
    apply Eqv.sound
    apply InS.let1_inr

theorem Eqv.let1_case_t {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
  {s : Eqv φ (⟨C, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨Ty.coprod A B, e⟩)
  (l : Term.InS φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩)
  (r : Term.InS φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩)
    : Eqv.let1 (a.case l r) s = case a (Eqv.let1 l s.vwk1) (Eqv.let1 r s.vwk1)
  := by induction s using Quotient.inductionOn with
  | h s =>
    simp only [let1_quot, vwk1_quot]
    apply Eqv.sound
    apply InS.let1_case_t

theorem Eqv.let1_abort {Γ : Ctx α ε} {L : LCtx α} {A : Ty α} (e' := ⊥)
  {r : Eqv φ (⟨A, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨Ty.empty, e⟩)
    : Eqv.let1 (a.abort _) r
    = (r.vwk1.let1 ((Term.InS.var 0 (by simp)).abort (e := e') _)).let1 a
  := by induction r using Quotient.inductionOn with
  | h r =>
    simp only [let1_quot, vwk1_quot]
    apply Eqv.sound
    apply InS.let1_abort

theorem Eqv.let2_op {Γ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨C, ⊥⟩::⟨B, ⊥⟩::Γ) L}
  (f : φ) (hf : Φ.EFn f A (Ty.prod B C) e)
  (a : Term.InS φ Γ ⟨A, e⟩)
    : Eqv.let2 (a.op f hf) r = (
      let1 a $
      let2 ((Term.InS.var 0 (by simp)).op f hf) $
      r.vwk (ρ := ⟨Nat.liftnWk 2 Nat.succ, by apply Ctx.Wkn.sliftn₂; simp⟩))
  := by induction r using Quotient.inductionOn with
  | h r =>
    simp only [let2_quot, vwk_quot, let1_quot]
    apply Eqv.sound
    apply InS.let2_op

theorem Eqv.let2_pair {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
  {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩)
  (b : Term.InS φ Γ ⟨B, e⟩)
    : Eqv.let2 (a.pair b) r = (
      let1 a $
      let1 (b.wk ⟨Nat.succ, (by simp)⟩) r)
  := by induction r using Quotient.inductionOn with
  | h r =>
    have h : ⟦r⟧ = r.q := rfl
    simp [h]
    apply Eqv.sound
    apply InS.let2_pair

theorem Eqv.let2_abort {Γ : Ctx α ε} {L : LCtx α} {A : Ty α} (e' := ⊥)
  {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨Ty.empty, e⟩)
    : Eqv.let2 (a.abort _) r = (
      let1 a $
      let2 ((Term.InS.var 0 (by simp)).abort (e := e') (A.prod B)) $
      r.vwk ⟨Nat.liftnWk 2 Nat.succ, by apply Ctx.Wkn.sliftn₂; simp⟩)
  := by induction r using Quotient.inductionOn with
  | h r =>
    simp only [let2_quot, vwk_quot, let1_quot]
    apply Eqv.sound
    apply InS.let2_abort

theorem Eqv.case_op {Γ : Ctx α ε} {L : LCtx α}
  (f : φ) (hf : Φ.EFn f A (B.coprod C) e)
  (a : Term.InS φ Γ ⟨A, e⟩) (r : Eqv φ (⟨B, ⊥⟩::Γ) L) (s : Eqv φ (⟨C, ⊥⟩::Γ) L)
  : Eqv.case (a.op f hf) r s =
    (let1 a $ case (Term.InS.op f hf (Term.InS.var 0 (by simp))) r.vwk1 s.vwk1)
  := by induction r using Quotient.inductionOn with
  | h r =>
    induction s using Quotient.inductionOn with
    | h s =>
      simp only [case_quot, vwk1_quot, let1_quot]
      apply Eqv.sound
      apply InS.case_op

theorem Eqv.case_abort {Γ : Ctx α ε} {L : LCtx α} (e' := ⊥)
  (a : Term.InS φ Γ ⟨Ty.empty, e⟩) (r : Eqv φ (⟨A, ⊥⟩::Γ) L) (s : Eqv φ (⟨B, ⊥⟩::Γ) L)
  : Eqv.case (a.abort _) r s =
    (let1 a $ case (Term.InS.abort (e := e') (Term.InS.var 0 (by simp)) (A.coprod B)) r.vwk1 s.vwk1)
  := by induction r using Quotient.inductionOn with
  | h r =>
    induction s using Quotient.inductionOn with
    | h s =>
      simp only [case_quot, vwk1_quot, let1_quot]
      apply Eqv.sound
      apply InS.case_abort

-- TODO: let1_case, let2_case...

theorem Eqv.cfg_br_lt {Γ : Ctx α ε} {L : LCtx α}
  (ℓ) (a : Term.InS φ Γ ⟨A, ⊥⟩)
  (R : LCtx α)  (G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  (hℓ : (R ++ L).Trg ℓ A) (hℓ' : ℓ < R.length)
  : (InS.br ℓ a hℓ).q.cfg R G
  = (let1 a $ (G ⟨ℓ, hℓ'⟩).vwk_id (by simp only [Ctx.Wkn.lift_id_iff,
    Prod.mk_le_mk, le_refl, and_true, Ctx.Wkn.id]; exact List.get_append ℓ hℓ' ▸ hℓ.get)).cfg R G
  := by
  simp only [cfg]
  generalize hG : Quotient.finChoice G = G'
  generalize hg : G ⟨ℓ, hℓ'⟩ = g
  induction G' using Quotient.inductionOn with
  | h G' =>
    induction g using Quotient.inductionOn with
    | h g =>
      have hg : ⟦g⟧ = (G' ⟨ℓ, hℓ'⟩).q := by
        rw [<-hg, InS.q]
        apply Quotient.forall_of_finChoice_eq hG
      simp only [InS.cfg_inner_q, hg, InS.vwk_id_q, InS.let1_q]
      apply Eqv.sound
      apply InS.cfg_br_lt

theorem Eqv.cfg_let1 {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨A, ea⟩)
  (R : LCtx α) (β : Eqv φ (⟨A, ⊥⟩::Γ) (R ++ L))
  (G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
    : (let1 a β).cfg R G = (let1 a $ β.cfg R (λi => (G i).vwk1))
  := by
  simp only [cfg]
  generalize hG : Quotient.finChoice G = G'
  induction β using Quotient.inductionOn with
  | h β =>
    induction G' using Quotient.inductionOn with
    | h G' =>
      have hβ : ⟦β⟧ = β.q := rfl
      simp only [hβ, InS.let1_q, InS.cfg_inner_q]
      apply Eq.trans
      apply Eqv.sound
      apply InS.cfg_let1
      rw [<-InS.let1_q, <-InS.cfg_q]
      congr
      funext i
      rw [<-InS.vwk1_q]
      rw [InS.q]
      congr
      apply Eq.symm
      apply Quotient.forall_of_finChoice_eq hG

theorem Eqv.cfg_let2 {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨Ty.prod A B, ea⟩)
  (R : LCtx α) (β : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) (R ++ L))
  (G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
    : (let2 a β).cfg R G = (let2 a $ β.cfg R (λi => (G i).vwk1.vwk1))
  := by
  simp only [cfg]
  generalize hG : Quotient.finChoice G = G'
  induction β using Quotient.inductionOn with
  | h β =>
    induction G' using Quotient.inductionOn with
    | h G' =>
      have hβ : ⟦β⟧ = β.q := rfl
      simp only [hβ, InS.let2_q, InS.cfg_inner_q]
      apply Eq.trans
      apply Eqv.sound
      apply InS.cfg_let2
      rw [<-InS.let2_q, <-InS.cfg_q]
      congr
      funext i
      simp only [<-InS.vwk1_q]
      rw [InS.q]
      congr
      apply Eq.symm
      apply Quotient.forall_of_finChoice_eq hG

theorem Eqv.cfg_case {Γ : Ctx α ε} {L : LCtx α}
  (e : Term.InS φ Γ ⟨Ty.coprod A B, ea⟩)
  (R : LCtx α)
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (R ++ L))
  (s : Eqv φ (⟨B, ⊥⟩::Γ) (R ++ L))
  (G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
    : (Eqv.case e r s).cfg R G
    = Eqv.case e (r.cfg R (λi => (G i).vwk1)) (s.cfg R (λi => (G i).vwk1))
  := by
  simp only [cfg]
  generalize hG : Quotient.finChoice G = G'
  induction r using Quotient.inductionOn
  induction s using Quotient.inductionOn
  induction G' using Quotient.inductionOn
  case _ r s G =>
    have hr : ⟦r⟧ = r.q := rfl
    have hs : ⟦s⟧ = s.q := rfl
    simp only [hr, hs, InS.case_q, InS.cfg_inner_q]
    apply Eq.trans
    apply Eqv.sound
    apply InS.cfg_case
    rw [<-InS.case_q, <-InS.cfg_q]
    congr
    funext i
    simp only [<-InS.vwk1_q]
    rw [InS.q]
    congr
    apply Eq.symm
    apply Quotient.forall_of_finChoice_eq hG
    rw [<-InS.cfg_q, cfg]
    congr
    funext i
    simp only [<-InS.vwk1_q]
    rw [InS.q]
    congr
    apply Eq.symm
    apply Quotient.forall_of_finChoice_eq hG

-- theorem Eqv.cfg_eqv_cfg' {Γ : Ctx α ε} {L : LCtx α}
--   (R S : LCtx α) (β : Eqv φ Γ (R ++ (S ++ L)))
--   (G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ (S ++ L)))
--   (G' : (i : Fin S.length) → Eqv φ (⟨S.get i, ⊥⟩::Γ) (S ++ L))
--     : (β.cfg R G).cfg S G'
--     = (β.cast rfl (by rw [List.append_assoc])).cfg'
--       (R.length + S.length) (R ++ S) (by rw [List.length_append])
--       (Fin.addCases (λi => (G i).cast (by sorry) (by rw [List.append_assoc]))
--                     (λi => ((G' i).lwk (· + R.length) sorry).cast sorry
--                       (by rw [List.append_assoc]))
--       )
--   := sorry

theorem Eqv.cfg_zero {Γ : Ctx α ε} {L : LCtx α}
  (β : Eqv φ Γ L)
  : β.cfg [] (λi => i.elim0) = β
  := by induction β using Quotient.inductionOn with | h β => exact Eqv.sound $ β.cfg_zero

theorem Eqv.let2_eta {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨Ty.prod A B, ea⟩)
  (r : Eqv φ (⟨A.prod B, ⊥⟩::Γ) L)
    : (let2 a $
        let1 ((Term.InS.var 1 ⟨by simp, le_refl _⟩).pair (Term.InS.var 0 (by simp))) r.vwk1.vwk1)
    = let1 a r
  := by induction r using Quotient.inductionOn with | h r => exact Eqv.sound $ InS.let2_eta a r

theorem Eqv.wk_cfg {Γ : Ctx α ε} {L : LCtx α}
  (R S : LCtx α) (β : Eqv φ Γ (R ++ L))
  (G : (i : Fin S.length) → Eqv φ ((List.get S i, ⊥)::Γ) (R ++ L))
  (ρ : Fin R.length → Fin S.length)
  (hρ : LCtx.Wkn (R ++ L) (S ++ L) (Fin.toNatWk ρ))
  : cfg S (β.lwk ⟨Fin.toNatWk ρ, hρ⟩) (λi => (G i).lwk ⟨Fin.toNatWk ρ, hρ⟩)
  = cfg R β (λi => (G (ρ i)).vwk_id (Ctx.Wkn.id.toFinWk_id hρ i))
  := by
  induction β using Quotient.inductionOn with
  | h β =>
    simp only [cfg]
    generalize hG : Quotient.finChoice G = G'
    induction G' using Quotient.inductionOn with
    | h G' =>
      have hG := Quotient.forall_of_finChoice_eq hG
      simp only [Set.mem_setOf_eq, lwk_quot, List.get_eq_getElem, hG, Fin.getElem_fin, vwk_id_quot,
        Quotient.finChoice_eq, Eqv.cfg_inner_quot]
      apply Eqv.sound
      apply InS.wk_cfg

theorem Eqv.case_inl {Γ : Ctx α ε} {L : LCtx α}
  (e : Term.InS φ Γ ⟨A, ea⟩)
  (r : Eqv φ (⟨A, ⊥⟩::Γ) L)
  (s : Eqv φ (⟨B, ⊥⟩::Γ) L)
    : case e.inl r s = let1 e r
  := by
  induction r using Quotient.inductionOn
  induction s using Quotient.inductionOn
  case _ r s =>
  exact Eqv.sound (InS.case_inl e r s)

theorem Eqv.case_inr {Γ : Ctx α ε} {L : LCtx α}
  (e : Term.InS φ Γ ⟨B, ea⟩)
  (r : Eqv φ (⟨A, ⊥⟩::Γ) L)
  (s : Eqv φ (⟨B, ⊥⟩::Γ) L)
    : case e.inr r s = let1 e s
  := by
  induction r using Quotient.inductionOn
  induction s using Quotient.inductionOn
  case _ r s =>
  exact Eqv.sound (InS.case_inr e r s)

theorem InS.dead_cfg_left {Γ : Ctx α ε} {L : LCtx α}
  (R S : LCtx α) (β : InS φ Γ (S ++ L))
  (G : (i : Fin R.length) → InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ S ++ L))
  (G' : (i : Fin S.length) → InS φ (⟨S.get i, ⊥⟩::Γ) (S ++ L))
  : (β.lwk ((LCtx.InS.add_left_append (S ++ L) R).cast rfl (by rw [List.append_assoc]))).cfg'
    (R.length + S.length) (R ++ S) (by rw [List.length_append])
      (Fin.addCases
        (λi => (G i).cast sorry rfl)
        (λi => ((G' i).cast sorry rfl).lwk
          ((LCtx.InS.add_left_append (S ++ L) R).cast rfl (by rw [List.append_assoc]))))
    ≈ β.cfg S G'
  := sorry

-- TODO: Eqv.dead_cfg_left; after Eqv.lwk

theorem Eqv.let1_beta {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨A, ⊥⟩)
  (r : Eqv φ (⟨A, ⊥⟩::Γ) L)
    : let1 a r = r.vsubst a.subst0
  := by
  induction r using Quotient.inductionOn
  exact Eqv.sound (InS.let1_beta a _)

theorem Eqv.initial {Γ : Ctx α ε} {L : LCtx α} (hi : Γ.IsInitial) (r r' : Eqv φ Γ L) : r = r'
  := by
  induction r using Quotient.inductionOn
  induction r' using Quotient.inductionOn
  exact Eqv.sound (InS.initial hi _ _)

theorem Eqv.terminal {Γ : Ctx α ε} {L : LCtx α}
  (e e' : Term.InS φ Γ ⟨Ty.unit, ⊥⟩) (r : Eqv φ (⟨Ty.unit, ⊥⟩::Γ) L)
  : let1 e r = let1 e' r
  := by
  induction r using Quotient.inductionOn
  exact Eqv.sound (InS.terminal e e' _)

end Region

end BinSyntax
