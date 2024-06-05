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

/-- Infer the control effect of a terminator -/
def Terminator.control_effect (Γ : ℕ → ε) : Terminator φ → ε
  := Terminator.effect Γ

/-- Infer the jump effect of a terminator -/
def Terminator.jump_effect (Γ : ℕ → ε) : Terminator φ → ε
  | br _ e => e.effect Γ
  | case _ s t => s.jump_effect (Nat.liftBot Γ) ⊔ t.jump_effect (Nat.liftBot Γ)

/-- Infer the effect of a basic block -/
def Block.effect (Γ : ℕ → ε) (b : Block φ)
  := b.body.effect Γ ⊔ b.terminator.effect (Nat.liftnBot b.body.num_defs Γ)

/-- Infer the control effect of a block -/
def Block.control_effect (Γ : ℕ → ε) (b : Block φ)
  := b.terminator.control_effect (Nat.liftnBot b.body.num_defs Γ)

/-- Infer the jump effect of a block -/
def Block.jump_effect (Γ : ℕ → ε) (b : Block φ)
  := b.terminator.jump_effect (Nat.liftnBot b.body.num_defs Γ)

/-- Infer the effect of a `BBRegion`, _without_ taking control-flow into account -/
def BBRegion.effect (Γ : ℕ → ε) : BBRegion φ → ε
  | cfg β _ G => β.effect Γ ⊔ Fin.sup (λi => (G i).effect (Nat.liftnBot β.body.num_defs Γ))

/-- Infer the control effect of a `TRegion`, _without_ taking control-flow into account -/
def BBRegion.control_effect (Γ : ℕ → ε) : BBRegion φ → ε
  | cfg β _ G => β.control_effect Γ
    ⊔ Fin.sup (λi => (G i).control_effect (Nat.liftnBot β.body.num_defs Γ))

/-- Infer the jump effect of a `BBRegion`, _without_ taking control-flow into account -/
def BBRegion.jump_effect (Γ : ℕ → ε) : BBRegion φ → ε
  | cfg β _ G => β.jump_effect Γ ⊔ Fin.sup (λi => (G i).jump_effect (Nat.liftnBot β.body.num_defs Γ))

/-- Infer the effect of a `TRegion`, _without_ taking control-flow into account -/
def TRegion.effect (Γ : ℕ → ε) : TRegion φ → ε
  | let1 e r => e.effect Γ ⊔ r.effect (Nat.liftBot Γ)
  | let2 e r => e.effect Γ ⊔ r.effect (Nat.liftnBot 2 Γ)
  | cfg β _ G => β.effect Γ ⊔ Fin.sup (λi => (G i).effect Γ)

/-- Infer the control effect of a `TRegion`, _without_ taking control-flow into account -/
def TRegion.control_effect (Γ : ℕ → ε) : TRegion φ → ε
  | let1 _ r => r.control_effect (Nat.liftBot Γ)
  | let2 _ r => r.control_effect (Nat.liftnBot 2 Γ)
  | cfg β _ G => β.control_effect Γ ⊔ Fin.sup (λi => (G i).control_effect Γ)

/-- Infer the jump effect of a `TRegion`, _without_ taking control-flow into account -/
def TRegion.jump_effect (Γ : ℕ → ε) : TRegion φ → ε
  | let1 _ r => r.jump_effect (Nat.liftBot Γ)
  | let2 _ r => r.jump_effect (Nat.liftnBot 2 Γ)
  | cfg β _ G => β.jump_effect Γ ⊔ Fin.sup (λi => (G i).jump_effect Γ)

/-- Infer the effect of a `Region`, _without_ taking control-flow into account -/
def Region.effect (Γ : ℕ → ε) : Region φ → ε
  | br _ e => e.effect Γ
  | let1 e r => e.effect Γ ⊔ r.effect (Nat.liftBot Γ)
  | let2 e r => e.effect Γ ⊔ r.effect (Nat.liftnBot 2 Γ)
  | case e s t => e.effect Γ ⊔ s.effect (Nat.liftBot Γ) ⊔ t.effect (Nat.liftBot Γ)
  | cfg β _ G => β.effect Γ ⊔ Fin.sup (λi => (G i).effect Γ)

/-- Infer the control effect of a `Region`, _without_ taking control-flow into account -/
def Region.control_effect (Γ : ℕ → ε) : Region φ → ε
  | br _ e => e.effect Γ
  | let1 _ r => r.control_effect (Nat.liftBot Γ)
  | let2 _ r => r.control_effect (Nat.liftnBot 2 Γ)
  | case e s t => e.effect Γ ⊔ s.control_effect (Nat.liftBot Γ) ⊔ t.control_effect (Nat.liftBot Γ)
  | cfg β _ G => β.control_effect Γ ⊔ Fin.sup (λi => (G i).control_effect Γ)

/-- Infer the jump effect of a `Region`, _without_ taking control-flow into account -/
def Region.jump_effect (Γ : ℕ → ε) : Region φ → ε
  | br _ e => e.effect Γ
  | let1 _ r => r.jump_effect (Nat.liftBot Γ)
  | let2 _ r => r.jump_effect (Nat.liftnBot 2 Γ)
  | case _ s t => s.jump_effect (Nat.liftBot Γ) ⊔ t.jump_effect (Nat.liftBot Γ)
  | cfg β _ G => β.jump_effect Γ ⊔ Fin.sup (λi => (G i).jump_effect Γ)

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

theorem Block.control_effect_mono {Γ : ℕ → ε} {b : Block φ} {Δ : ℕ → ε}
  (H : Γ ≤ Δ) : b.control_effect Γ ≤ b.control_effect Δ :=
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

theorem BBRegion.control_effect_mono {Γ : ℕ → ε} {r : BBRegion φ} {Δ : ℕ → ε}
  (H : Γ ≤ Δ) : r.control_effect Γ ≤ r.control_effect Δ := by
  induction r generalizing Γ Δ with
  | cfg β n G IG =>
    apply sup_le_sup (β.control_effect_mono H)
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

theorem TRegion.control_effect_mono {Γ : ℕ → ε} {r : TRegion φ} {Δ : ℕ → ε}
  (H : Γ ≤ Δ) : r.control_effect Γ ≤ r.control_effect Δ := by
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

theorem Region.control_effect_mono {Γ : ℕ → ε} {r : Region φ} {Δ : ℕ → ε}
  (H : Γ ≤ Δ) : r.control_effect Γ ≤ r.control_effect Δ := by
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

theorem Terminator.control_effect_le_effect {Γ : ℕ → ε} {t : Terminator φ}
  : t.control_effect Γ ≤ t.effect Γ
  := le_refl _

theorem Terminator.jump_effect_le_control_effect {Γ : ℕ → ε} {t : Terminator φ}
  : t.jump_effect Γ ≤ t.control_effect Γ
  := by induction t generalizing Γ with
  | br _ e => exact le_refl _
  | case _ s t Is It =>
    rw [jump_effect, control_effect, effect, sup_assoc]
    exact le_sup_of_le_right $ sup_le_sup Is It

theorem Terminator.jump_effect_le_effect {Γ : ℕ → ε} {t : Terminator φ}
  : t.jump_effect Γ ≤ t.effect Γ
  := le_trans t.jump_effect_le_control_effect t.control_effect_le_effect

theorem Block.control_effect_le_effect {Γ : ℕ → ε} {b : Block φ}
  : b.control_effect Γ ≤ b.effect Γ
  := by simp [control_effect, effect, Terminator.control_effect]

theorem Block.jump_effect_le_control_effect {Γ : ℕ → ε} {b : Block φ}
  : b.jump_effect Γ ≤ b.control_effect Γ
  := by simp [control_effect, jump_effect, Terminator.jump_effect_le_control_effect]

theorem Block.jump_effect_le_effect {Γ : ℕ → ε} {b : Block φ}
  : b.jump_effect Γ ≤ b.effect Γ
  := le_trans b.jump_effect_le_control_effect b.control_effect_le_effect

theorem BBRegion.control_effect_le_effect {Γ : ℕ → ε} {r : BBRegion φ}
  : r.control_effect Γ ≤ r.effect Γ
  := by induction r generalizing Γ with
  | cfg β n G IH =>
    simp only [control_effect, effect]
    apply sup_le_sup β.control_effect_le_effect
    apply Fin.sup_le_sup
    intro i
    apply IH

theorem BBRegion.jump_effect_le_control_effect {Γ : ℕ → ε} {r : BBRegion φ}
  : r.jump_effect Γ ≤ r.control_effect Γ
  := by induction r generalizing Γ with
  | cfg β n G IH =>
    simp only [control_effect, jump_effect]
    apply sup_le_sup β.jump_effect_le_control_effect
    apply Fin.sup_le_sup
    intro i
    apply IH

theorem BBRegion.jump_effect_le_effect {Γ : ℕ → ε} {r : BBRegion φ}
  : r.jump_effect Γ ≤ r.effect Γ
  := le_trans r.jump_effect_le_control_effect r.control_effect_le_effect

theorem TRegion.control_effect_le_effect {Γ : ℕ → ε} {r : TRegion φ}
  : r.control_effect Γ ≤ r.effect Γ
  := by induction r generalizing Γ with
  | let1 _ _ IH => exact le_sup_of_le_right IH
  | let2 _ _ IH => exact le_sup_of_le_right IH
  | cfg β n G IH =>
    simp only [control_effect, effect]
    apply sup_le_sup (le_refl _)
    apply Fin.sup_le_sup
    intro i
    apply IH

theorem TRegion.jump_effect_le_control_effect {Γ : ℕ → ε} {r : TRegion φ}
  : r.jump_effect Γ ≤ r.control_effect Γ
  := by induction r generalizing Γ with
  | let1 _ _ IH => exact IH
  | let2 _ _ IH => exact IH
  | cfg β n G IH =>
    simp only [control_effect, jump_effect]
    apply sup_le_sup β.jump_effect_le_control_effect
    apply Fin.sup_le_sup
    intro i
    apply IH

theorem TRegion.jump_effect_le_effect {Γ : ℕ → ε} {r : TRegion φ}
  : r.jump_effect Γ ≤ r.effect Γ
  := le_trans r.jump_effect_le_control_effect r.control_effect_le_effect

theorem Region.control_effect_le_effect {Γ : ℕ → ε} {r : Region φ}
  : r.control_effect Γ ≤ r.effect Γ
  := by induction r generalizing Γ with
  | br _ e => exact le_refl _
  | let1 _ _ IH => exact le_sup_of_le_right IH
  | let2 _ _ IH => exact le_sup_of_le_right IH
  | case _ _ _ Is It => exact sup_le_sup (sup_le_sup (le_refl _) Is) It
  | cfg β n G Iβ IG =>
    simp only [control_effect, effect]
    apply sup_le_sup Iβ
    apply Fin.sup_le_sup
    intro i
    apply IG

theorem Region.jump_effect_le_control_effect {Γ : ℕ → ε} {r : Region φ}
  : r.jump_effect Γ ≤ r.control_effect Γ
  := by induction r generalizing Γ with
  | br _ e => exact le_refl _
  | let1 _ _ IH => exact IH
  | let2 _ _ IH => exact IH
  | case _ _ _ Is It =>
    rw [jump_effect, control_effect, sup_assoc]
    exact le_sup_of_le_right $ sup_le_sup Is It
  | cfg β n G Iβ IG =>
    simp only [control_effect, jump_effect]
    apply sup_le_sup Iβ
    apply Fin.sup_le_sup
    intro i
    apply IG

end OrderBot

end BinSyntax
