import Discretion.Wk.Order

import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.InstSet

namespace BinSyntax

section Definitions

variable [Φ : EffectSet φ ε] [Bot ε] [Sup ε]

/-- Infer the effect of a term -/
def Term.effect (Γ : ℕ → ε) : Term φ → ε
  | var n => Γ n
  | op f e => Φ.effect f ⊔ e.effect Γ
  | pair a b => a.effect Γ ⊔ b.effect Γ
  | inl a => a.effect Γ
  | inr b => b.effect Γ
  | abort e => e.effect Γ
  | unit => ⊥

/-- Infer the effect of a body -/
def Body.effect (Γ : ℕ → ε) : Body φ → ε
  | nil => ⊥
  | let1 e b => e.effect Γ ⊔ b.effect (Nat.liftBot Γ)
  | let2 e b => e.effect Γ ⊔ b.effect (Nat.liftnBot 2 Γ)

/-- Infer the effect of a terminator -/
def Terminator.effect (Γ : ℕ → ε) : Terminator φ → ε
  | br _ e => e.effect Γ
  | case e s t => e.effect Γ ⊔ s.effect (Nat.liftBot Γ) ⊔ t.effect (Nat.liftBot Γ)

/-- Infer the effect of a basic block -/
def Block.effect (Γ : ℕ → ε) (b : Block φ)
  := b.body.effect Γ ⊔ b.terminator.effect (Nat.liftnBot b.body.num_defs Γ)

/-- Infer whether a block has any effects in a special position -/
def Block.special_effect (Γ : ℕ → ε) (b : Block φ)
  := b.terminator.effect (Nat.liftnBot b.body.num_defs Γ)

/-- Infer the effect of a `BBRegion`, _without_ taking control-flow into account -/
def BBRegion.effect (Γ : ℕ → ε) : BBRegion φ → ε
  | cfg β _ G => β.effect Γ ⊔ Fin.sup (λi => (G i).effect (Nat.liftnBot β.body.num_defs Γ))

/-- Infer the special effect of a `TRegion`, _without_ taking control-flow into account -/
def BBRegion.special_effect (Γ : ℕ → ε) : BBRegion φ → ε
  | cfg β _ G => β.special_effect Γ
    ⊔ Fin.sup (λi => (G i).special_effect (Nat.liftnBot β.body.num_defs Γ))

/-- Infer the effect of a `TRegion`, _without_ taking control-flow into account -/
def TRegion.effect (Γ : ℕ → ε) : TRegion φ → ε
  | let1 e r => e.effect Γ ⊔ r.effect (Nat.liftBot Γ)
  | let2 e r => e.effect Γ ⊔ r.effect (Nat.liftnBot 2 Γ)
  | cfg β _ G => β.effect Γ ⊔ Fin.sup (λi => (G i).effect Γ)

/-- Infer the special effect of a `TRegion`, _without_ taking control-flow into account -/
def TRegion.special_effect (Γ : ℕ → ε) : TRegion φ → ε
  | let1 _ r => r.special_effect (Nat.liftBot Γ)
  | let2 _ r => r.special_effect (Nat.liftnBot 2 Γ)
  | cfg β _ G => β.effect Γ ⊔ Fin.sup (λi => (G i).special_effect Γ)

/-- Infer the effect of a `Region`, _without_ taking control-flow into account -/
def Region.effect (Γ : ℕ → ε) : Region φ → ε
  | br _ e => e.effect Γ
  | let1 e r => e.effect Γ ⊔ r.effect (Nat.liftBot Γ)
  | let2 e r => e.effect Γ ⊔ r.effect (Nat.liftnBot 2 Γ)
  | case e s t => e.effect Γ ⊔ s.effect (Nat.liftBot Γ) ⊔ t.effect (Nat.liftBot Γ)
  | cfg β _ G => β.effect Γ ⊔ Fin.sup (λi => (G i).effect Γ)

/-- Infer the special effect of a `Region`, _without_ taking control-flow into account -/
def Region.special_effect (Γ : ℕ → ε) : Region φ → ε
  | br _ e => e.effect Γ
  | let1 _ r => r.special_effect (Nat.liftBot Γ)
  | let2 _ r => r.special_effect (Nat.liftnBot 2 Γ)
  | case e s t => e.effect Γ ⊔ s.special_effect (Nat.liftBot Γ) ⊔ t.special_effect (Nat.liftBot Γ)
  | cfg β _ G => β.special_effect Γ ⊔ Fin.sup (λi => (G i).special_effect Γ)

end Definitions

section Monotone

variable [Φ : EffectSet φ ε] [Bot ε] [SemilatticeSup ε]

theorem Term.effect_mono {Γ : ℕ → ε} {e : Term φ} {Δ : ℕ → ε}
  (H : Γ ≤ Δ) : e.effect Γ ≤ e.effect Δ := by
  induction e with
  | var => exact H _
  | op f e I => exact sup_le_sup_left I _
  | pair a b Ia Ib => exact sup_le_sup Ia Ib
  | inl _ I => exact I
  | inr _ I => exact I
  | abort _ I => exact I
  | _ => exact le_refl _

theorem Body.effect_mono {Γ : ℕ → ε} {b : Body φ} {Δ : ℕ → ε}
  (H : Γ ≤ Δ) : b.effect Γ ≤ b.effect Δ := by
  induction b generalizing Γ Δ with
  | nil => exact le_refl _
  | let1 e b I => exact sup_le_sup (e.effect_mono H) (I (Nat.liftBot_mono H))
  | let2 e b I => exact sup_le_sup (e.effect_mono H) (I (Nat.liftnBot_mono _ H))

theorem Terminator.effect_mono {Γ : ℕ → ε} {t : Terminator φ} {Δ : ℕ → ε}
  (H : Γ ≤ Δ) : t.effect Γ ≤ t.effect Δ := by
  induction t generalizing Γ Δ with
  | br _ e => exact e.effect_mono H
  | case e s t Is It =>
    exact sup_le_sup
      (sup_le_sup (e.effect_mono H) (Is (Nat.liftBot_mono H)))
      (It (Nat.liftBot_mono H))

theorem Block.effect_mono {Γ : ℕ → ε} {b : Block φ} {Δ : ℕ → ε}
  (H : Γ ≤ Δ) : b.effect Γ ≤ b.effect Δ := sup_le_sup
    (b.body.effect_mono H)
    (b.terminator.effect_mono (Nat.liftnBot_mono _ H))

theorem Block.special_effect_mono {Γ : ℕ → ε} {b : Block φ} {Δ : ℕ → ε}
  (H : Γ ≤ Δ) : b.special_effect Γ ≤ b.special_effect Δ :=
  b.terminator.effect_mono (Nat.liftnBot_mono _ H)

theorem BBRegion.effect_mono {Γ : ℕ → ε} {r : BBRegion φ} {Δ : ℕ → ε}
  (H : Γ ≤ Δ) : r.effect Γ ≤ r.effect Δ := by
  induction r generalizing Γ Δ with
  | cfg β n G IG =>
    apply sup_le_sup (β.effect_mono H)
    -- TODO: Fin.sup_le_sup not working here for some reason...
    induction n with
    | zero => rfl
    | succ n I =>
      rw [Fin.sup_succ, Fin.sup_succ]
      apply sup_le_sup
      apply IG 0 (Nat.liftnBot_mono _ H)
      apply I
      intro k Γ' Δ' H'
      apply IG k.succ H'

theorem BBRegion.special_effect_mono {Γ : ℕ → ε} {r : BBRegion φ} {Δ : ℕ → ε}
  (H : Γ ≤ Δ) : r.special_effect Γ ≤ r.special_effect Δ := by
  induction r generalizing Γ Δ with
  | cfg β n G IG =>
    apply sup_le_sup (β.special_effect_mono H)
    -- TODO: Fin.sup_le_sup not working here for some reason...
    induction n with
    | zero => rfl
    | succ n I =>
      rw [Fin.sup_succ, Fin.sup_succ]
      apply sup_le_sup
      apply IG 0 (Nat.liftnBot_mono _ H)
      apply I
      intro k Γ' Δ' H'
      apply IG k.succ H'

theorem TRegion.effect_mono {Γ : ℕ → ε} {r : TRegion φ} {Δ : ℕ → ε}
  (H : Γ ≤ Δ) : r.effect Γ ≤ r.effect Δ := by
  induction r generalizing Γ Δ with
  | let1 e r I => exact sup_le_sup (e.effect_mono H) (I (Nat.liftBot_mono H))
  | let2 e r I => exact sup_le_sup (e.effect_mono H) (I (Nat.liftnBot_mono _ H))
  | cfg β n G IG =>
    apply sup_le_sup (β.effect_mono H)
    -- TODO: Fin.sup_le_sup not working here for some reason...
    induction n with
    | zero => rfl
    | succ n I =>
      rw [Fin.sup_succ, Fin.sup_succ]
      apply sup_le_sup
      apply IG 0 H
      apply I
      intro k Γ' Δ' H'
      apply IG k.succ H'

theorem TRegion.special_effect_mono {Γ : ℕ → ε} {r : TRegion φ} {Δ : ℕ → ε}
  (H : Γ ≤ Δ) : r.special_effect Γ ≤ r.special_effect Δ := by
  induction r generalizing Γ Δ with
  | let1 _ _ I => exact I (Nat.liftBot_mono H)
  | let2 _ _ I => exact I (Nat.liftnBot_mono _ H)
  | cfg β n G IG =>
    apply sup_le_sup (β.effect_mono H)
    -- TODO: Fin.sup_le_sup not working here for some reason...
    induction n with
    | zero => rfl
    | succ n I =>
      rw [Fin.sup_succ, Fin.sup_succ]
      apply sup_le_sup
      apply IG 0 H
      apply I
      intro k Γ' Δ' H'
      apply IG k.succ H'

theorem Region.effect_mono {Γ : ℕ → ε} {r : Region φ} {Δ : ℕ → ε}
  (H : Γ ≤ Δ) : r.effect Γ ≤ r.effect Δ := by
  induction r generalizing Γ Δ with
  | br _ e => exact e.effect_mono H
  | let1 e r I => exact sup_le_sup (e.effect_mono H) (I (Nat.liftBot_mono H))
  | let2 e r I => exact sup_le_sup (e.effect_mono H) (I (Nat.liftnBot_mono _ H))
  | case e s t Is It =>
    exact sup_le_sup
      (sup_le_sup (e.effect_mono H) (Is (Nat.liftBot_mono H)))
      (It (Nat.liftBot_mono H))
  | cfg β n G Iβ IG =>
    apply sup_le_sup (Iβ H)
    -- TODO: Fin.sup_le_sup not working here for some reason...
    induction n with
    | zero => rfl
    | succ n I =>
      rw [Fin.sup_succ, Fin.sup_succ]
      apply sup_le_sup
      apply IG 0 H
      apply I
      intro k Γ' Δ' H'
      apply IG k.succ H'

theorem Region.special_effect_mono {Γ : ℕ → ε} {r : Region φ} {Δ : ℕ → ε}
  (H : Γ ≤ Δ) : r.special_effect Γ ≤ r.special_effect Δ := by
  induction r generalizing Γ Δ with
  | br _ e => exact e.effect_mono H
  | let1 _ _ I => exact I (Nat.liftBot_mono H)
  | let2 _ _ I => exact I (Nat.liftnBot_mono _ H)
  | case e s t Is It =>
    exact sup_le_sup
      (sup_le_sup (e.effect_mono H) (Is (Nat.liftBot_mono H)))
      (It (Nat.liftBot_mono H))
  | cfg β n G Iβ IG =>
    apply sup_le_sup (Iβ H)
    -- TODO: Fin.sup_le_sup not working here for some reason...
    induction n with
    | zero => rfl
    | succ n I =>
      rw [Fin.sup_succ, Fin.sup_succ]
      apply sup_le_sup
      apply IG 0 H
      apply I
      intro k Γ' Δ' H'
      apply IG k.succ H'

end Monotone

section OrderBot

variable [Φ : EffectSet φ ε] [SemilatticeSup ε] [OrderBot ε]

theorem Block.special_effect_le_effect {Γ : ℕ → ε} {b : Block φ}
  : b.special_effect Γ ≤ b.effect Γ
  := by simp [special_effect, effect]

theorem BBRegion.special_effect_le_effect {Γ : ℕ → ε} {r : BBRegion φ}
  : r.special_effect Γ ≤ r.effect Γ
  := by induction r generalizing Γ with
  | cfg β n G IH =>
    simp only [special_effect, effect]
    apply sup_le_sup β.special_effect_le_effect
    apply Fin.sup_le_sup
    intro i
    apply IH

theorem TRegion.special_effect_le_effect {Γ : ℕ → ε} {r : TRegion φ}
  : r.special_effect Γ ≤ r.effect Γ
  := by induction r generalizing Γ with
  | let1 _ _ IH => exact le_sup_of_le_right IH
  | let2 _ _ IH => exact le_sup_of_le_right IH
  | cfg β n G IH =>
    simp only [special_effect, effect]
    apply sup_le_sup (le_refl _)
    apply Fin.sup_le_sup
    intro i
    apply IH

theorem Region.special_effect_le_effect {Γ : ℕ → ε} {r : Region φ}
  : r.special_effect Γ ≤ r.effect Γ
  := by induction r generalizing Γ with
  | br _ e => exact le_refl _
  | let1 _ _ IH => exact le_sup_of_le_right IH
  | let2 _ _ IH => exact le_sup_of_le_right IH
  | case _ _ _ Is It => exact sup_le_sup (sup_le_sup (le_refl _) Is) It
  | cfg β n G Iβ IG =>
    simp only [special_effect, effect]
    apply sup_le_sup Iβ
    apply Fin.sup_le_sup
    intro i
    apply IG

end OrderBot

end BinSyntax
