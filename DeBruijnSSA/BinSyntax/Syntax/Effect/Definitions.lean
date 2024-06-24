import Discretion.Wk.Order
import Discretion.Wk.Multiset

import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.InstSet

namespace BinSyntax

section Definitions

variable [Φ : EffectSet φ ε] [Bot ε] [Sup ε]

/-- Infer the effect of a term -/
@[simp]
def Term.effect (Γ : ℕ → ε) : Term φ → ε
  | var n => Γ n
  | op f e => Φ.effect f ⊔ e.effect Γ
  | pair a b => a.effect Γ ⊔ b.effect Γ
  | inl a => a.effect Γ
  | inr b => b.effect Γ
  -- | abort e => e.effect Γ
  | unit => ⊥

theorem Term.effect_wk (ρ : ℕ → ℕ) (Γ : ℕ → ε) (e : Term φ)
  : (e.wk ρ).effect Γ = e.effect (Γ ∘ ρ)
  := by induction e <;> simp [*]

theorem Term.effect_liftBot_wk_liftWk (Γ : ℕ → ε) (e : Term φ)
  : (e.wk (Nat.liftWk ρ)).effect (Nat.liftBot Γ) = e.effect (Nat.liftBot (Γ ∘ ρ))
  := by rw [effect_wk, Nat.liftBot_comp_liftWk]

theorem Term.effect_liftnBot_wk_liftnWk (Γ : ℕ → ε) (e : Term φ)
  : (e.wk (Nat.liftnWk n ρ)).effect (Nat.liftnBot n Γ) = e.effect (Nat.liftnBot n (Γ ∘ ρ))
  := by rw [effect_wk, Nat.liftnBot_comp_liftnWk]

@[simp]
theorem Term.effect_liftBot_wk_succ (Γ : ℕ → ε) (e : Term φ)
  : (e.wk Nat.succ).effect (Nat.liftBot Γ) = e.effect Γ
  := by rw [effect_wk]; rfl

@[simp]
theorem Term.effect_liftnBot_wk_add (Γ : ℕ → ε) (e : Term φ)
  : (e.wk (· + n)).effect (Nat.liftnBot n Γ) = e.effect Γ
  := by rw [effect_wk, Nat.liftnBot_comp_add]

@[simp]
theorem Term.effect_liftBot2_wk1 (Γ : ℕ → ε) (e : Term φ)
  : (e.wk1).effect (Nat.liftBot (Nat.liftBot Γ)) = e.effect (Nat.liftBot Γ)
  := by rw [wk1, effect_wk, Nat.liftBot_comp_liftWk]; rfl

@[simp]
theorem Term.effect_liftnBot2_wk1 (Γ : ℕ → ε) (e : Term φ)
  : (e.wk1).effect (Nat.liftnBot 2 Γ) = e.effect (Nat.liftBot Γ)
  := by rw [Nat.liftnBot_iterate, <-Term.effect_liftBot2_wk1]; rfl

/-- Infer the effect of a body -/
@[simp]
def Body.effect (Γ : ℕ → ε) : Body φ → ε
  | nil => ⊥
  | let1 e b => e.effect Γ ⊔ b.effect (Nat.liftBot Γ)
  | let2 e b => e.effect Γ ⊔ b.effect (Nat.liftnBot 2 Γ)

theorem Body.effect_wk (ρ : ℕ → ℕ) (Γ : ℕ → ε) (b : Body φ)
  : (b.wk ρ).effect Γ = b.effect (Γ ∘ ρ)
  := by induction b generalizing Γ ρ
    <;> simp [Term.effect_wk, Nat.liftBot_comp_liftWk, Nat.liftnBot_comp_liftnWk, *]

/-- Infer the effect of a terminator -/
@[simp]
def Terminator.effect (Γ : ℕ → ε) : Terminator φ → ε
  | br _ e => e.effect Γ
  | case e s t => e.effect Γ ⊔ s.effect (Nat.liftBot Γ) ⊔ t.effect (Nat.liftBot Γ)

theorem Terminator.effect_vwk (ρ : ℕ → ℕ) (Γ : ℕ → ε) (t : Terminator φ)
  : (t.vwk ρ).effect Γ = t.effect (Γ ∘ ρ)
  := by induction t generalizing Γ ρ
    <;> simp [Term.effect_wk, Nat.liftBot_comp_liftWk, *]

theorem Terminator.effect_lwk (ρ : ℕ → ℕ) (Γ : ℕ → ε) (t : Terminator φ)
  : (t.lwk ρ).effect Γ = t.effect Γ
  := by induction t generalizing Γ ρ
    <;> simp [Term.effect_wk, Nat.liftBot_comp_liftWk, *]

/-- Infer the control effect of a terminator -/
@[simp]
def Terminator.control_effect (Γ : ℕ → ε) : Terminator φ → ε
  := Terminator.effect Γ

/-- Infer the jump effect of a terminator -/
@[simp]
def Terminator.jump_effect (Γ : ℕ → ε) : Terminator φ → ε
  | br _ e => e.effect Γ
  | case _ s t => s.jump_effect (Nat.liftBot Γ) ⊔ t.jump_effect (Nat.liftBot Γ)

theorem Terminator.jump_effect_vwk (ρ : ℕ → ℕ) (Γ : ℕ → ε) (t : Terminator φ)
  : (t.vwk ρ).jump_effect Γ = t.jump_effect (Γ ∘ ρ)
  := by induction t generalizing Γ ρ
    <;> simp [Term.effect_wk, Nat.liftBot_comp_liftWk, *]

theorem Terminator.jump_effect_lwk (ρ : ℕ → ℕ) (Γ : ℕ → ε) (t : Terminator φ)
  : (t.lwk ρ).jump_effect Γ = t.jump_effect Γ
  := by induction t generalizing Γ ρ
    <;> simp [Term.effect_wk, Nat.liftBot_comp_liftWk, *]

/-- Infer the branch effect of a terminator to a of target -/
@[simp]
def Terminator.trg_effect (target : ℕ) (Γ : ℕ → ε) : Terminator φ → ε
  | br ℓ e => if ℓ = target then e.effect Γ else ⊥
  | case _ s t => s.trg_effect target (Nat.liftBot Γ) ⊔ t.trg_effect target (Nat.liftBot Γ)

/-- Infer the branch effect of a terminator to a set of targets -/
@[simp]
def Terminator.trg_set_effect (targets : Multiset ℕ) (Γ : ℕ → ε) : Terminator φ → ε
  | br ℓ e => if ℓ ∈ targets then e.effect Γ else ⊥
  | case _ s t =>
    s.trg_set_effect targets (Nat.liftBot Γ) ⊔ t.trg_set_effect targets (Nat.liftBot Γ)

/-- Infer the effect of a basic block -/
@[simp]
def Block.effect (Γ : ℕ → ε) (b : Block φ)
  := b.body.effect Γ ⊔ b.terminator.effect (Nat.liftnBot b.body.num_defs Γ)

/-- Infer the control effect of a block -/
@[simp]
def Block.control_effect (Γ : ℕ → ε) (b : Block φ)
  := b.terminator.control_effect (Nat.liftnBot b.body.num_defs Γ)

/-- Infer the jump effect of a block -/
@[simp]
def Block.jump_effect (Γ : ℕ → ε) (b : Block φ)
  := b.terminator.jump_effect (Nat.liftnBot b.body.num_defs Γ)

/-- Infer the branch effect of a block to a targets -/
@[simp]
def Block.trg_effect (target : ℕ) (Γ : ℕ → ε) (b : Block φ)
  := b.terminator.trg_effect target (Nat.liftnBot b.body.num_defs Γ)

/-- Infer the branch effect of a block to a set of targets -/
@[simp]
def Block.trg_set_effect (targets : Multiset ℕ) (Γ : ℕ → ε) (b : Block φ)
  := b.terminator.trg_set_effect targets (Nat.liftnBot b.body.num_defs Γ)

/-- Infer the effect of a `BBRegion`, _without_ taking control-flow into account -/
@[simp]
def BBRegion.effect (Γ : ℕ → ε) : BBRegion φ → ε
  | cfg β _ G => β.effect Γ
    ⊔ Fin.sup (λi => (G i).effect (Nat.liftnBot (β.body.num_defs + 1) Γ))

/-- Infer the control effect of a `TRegion`, _without_ taking control-flow into account -/
@[simp]
def BBRegion.control_effect (Γ : ℕ → ε) : BBRegion φ → ε
  | cfg β _ G => β.control_effect Γ
    ⊔ Fin.sup (λi => (G i).control_effect (Nat.liftnBot (β.body.num_defs + 1) Γ))

/-- Infer the jump effect of a `BBRegion`, _without_ taking control-flow into account -/
@[simp]
def BBRegion.jump_effect (Γ : ℕ → ε) : BBRegion φ → ε
  | cfg β _ G => β.jump_effect Γ
    ⊔ Fin.sup (λi => (G i).jump_effect (Nat.liftnBot (β.body.num_defs + 1) Γ))

/-- Infer the branch effect of a block to a target -/
@[simp]
def BBRegion.trg_effect (target : ℕ) (Γ : ℕ → ε) : BBRegion φ → ε
  | cfg β n G => β.trg_effect target Γ
    ⊔ Fin.sup (λi => (G i).trg_effect (target + n) (Nat.liftnBot (β.body.num_defs + 1) Γ))

/-- Infer the branch effect of a block to a set of targets -/
@[simp]
def BBRegion.trg_set_effect (targets : Multiset ℕ) (Γ : ℕ → ε) : BBRegion φ → ε
  | cfg β n G
  => β.trg_set_effect targets Γ
    ⊔ Fin.sup (λi =>
      (G i).trg_set_effect (targets.liftnFv n) (Nat.liftnBot (β.body.num_defs + 1) Γ))

/-- Infer the effect of a `TRegion`, _without_ taking control-flow into account -/
@[simp]
def TRegion.effect (Γ : ℕ → ε) : TRegion φ → ε
  | let1 e r => e.effect Γ ⊔ r.effect (Nat.liftBot Γ)
  | let2 e r => e.effect Γ ⊔ r.effect (Nat.liftnBot 2 Γ)
  | cfg β _ G => β.effect Γ ⊔ Fin.sup (λi => (G i).effect (Nat.liftBot Γ))

/-- Infer the control effect of a `TRegion`, _without_ taking control-flow into account -/
@[simp]
def TRegion.control_effect (Γ : ℕ → ε) : TRegion φ → ε
  | let1 _ r => r.control_effect (Nat.liftBot Γ)
  | let2 _ r => r.control_effect (Nat.liftnBot 2 Γ)
  | cfg β _ G => β.control_effect Γ ⊔ Fin.sup (λi => (G i).control_effect (Nat.liftBot Γ))

/-- Infer the jump effect of a `TRegion`, _without_ taking control-flow into account -/
@[simp]
def TRegion.jump_effect (Γ : ℕ → ε) : TRegion φ → ε
  | let1 _ r => r.jump_effect (Nat.liftBot Γ)
  | let2 _ r => r.jump_effect (Nat.liftnBot 2 Γ)
  | cfg β _ G => β.jump_effect Γ ⊔ Fin.sup (λi => (G i).jump_effect (Nat.liftBot Γ))

/-- Infer the branch effect of a `TRegion` to a target -/
@[simp]
def TRegion.trg_effect (target : ℕ) (Γ : ℕ → ε) : TRegion φ → ε
  | let1 _ r => r.trg_effect target (Nat.liftBot Γ)
  | let2 _ r => r.trg_effect target (Nat.liftnBot 2 Γ)
  | cfg β n G => β.trg_effect (target + n) Γ
    ⊔ Fin.sup (λi => (G i).trg_effect (target + n) (Nat.liftBot Γ))

/-- Infer the branch effect of a `TRegion` to a set of targets -/
@[simp]
def TRegion.trg_set_effect (targets : Multiset ℕ) (Γ : ℕ → ε) : TRegion φ → ε
  | let1 _ r => r.trg_set_effect targets (Nat.liftBot Γ)
  | let2 _ r => r.trg_set_effect targets (Nat.liftnBot 2 Γ)
  | cfg β n G => β.trg_set_effect (targets.liftnFv n) Γ
    ⊔ Fin.sup (λi => (G i).trg_set_effect (targets.liftnFv n) (Nat.liftBot Γ))

/-- Infer the effect of a `Region`, _without_ taking control-flow into account -/
@[simp]
def Region.effect (Γ : ℕ → ε) : Region φ → ε
  | br _ e => e.effect Γ
  | let1 e r => e.effect Γ ⊔ r.effect (Nat.liftBot Γ)
  | let2 e r => e.effect Γ ⊔ r.effect (Nat.liftnBot 2 Γ)
  | case e s t => e.effect Γ ⊔ s.effect (Nat.liftBot Γ) ⊔ t.effect (Nat.liftBot Γ)
  | cfg β _ G => β.effect Γ ⊔ Fin.sup (λi => (G i).effect (Nat.liftBot Γ))

theorem Region.effect_cfg {Γ : ℕ → ε} {β : Region φ} {n G}
  : (β.cfg n G).effect Γ = β.effect Γ ⊔ Fin.sup (effect (Nat.liftBot Γ) ∘ G)
  := rfl

theorem Region.effect_vwk (ρ : ℕ → ℕ) (Γ : ℕ → ε) (r : Region φ)
  : (r.vwk ρ).effect Γ = r.effect (Γ ∘ ρ)
  := by induction r generalizing Γ ρ
    <;> simp [Term.effect_wk, Nat.liftBot_comp_liftWk, Nat.liftnBot_comp_liftnWk, *]

theorem Region.effect_liftBot_vwk_liftWk (Γ : ℕ → ε) (e : Region φ)
  : (e.vwk (Nat.liftWk ρ)).effect (Nat.liftBot Γ) = e.effect (Nat.liftBot (Γ ∘ ρ))
  := by rw [effect_vwk, Nat.liftBot_comp_liftWk]

theorem Region.effect_liftnBot_vwk_liftnWk (Γ : ℕ → ε) (e : Region φ)
  : (e.vwk (Nat.liftnWk n ρ)).effect (Nat.liftnBot n Γ) = e.effect (Nat.liftnBot n (Γ ∘ ρ))
  := by rw [effect_vwk, Nat.liftnBot_comp_liftnWk]

@[simp]
theorem Region.effect_liftBot2_vwk1 (Γ : ℕ → ε) (e : Region φ)
  : (e.vwk1).effect (Nat.liftBot (Nat.liftBot Γ)) = e.effect (Nat.liftBot Γ)
  := by rw [vwk1, effect_vwk, Nat.liftBot_comp_liftWk]; rfl

@[simp]
theorem Region.effect_liftnBot2_vwk1 (Γ : ℕ → ε) (e : Region φ)
  : (e.vwk1).effect (Nat.liftnBot 2 Γ) = e.effect (Nat.liftBot Γ)
  := by rw [Nat.liftnBot_iterate, <-Region.effect_liftBot2_vwk1]; rfl

-- @[simp]
-- theorem Region.effect_liftnBot_liftBot_vwk2 (Γ : ℕ → ε) (e : Region φ)
--   : (e.vwk (Nat.liftWk (· + 2))).effect (Nat.liftnBot 2 (Nat.liftBot Γ)) = e.effect (Nat.liftBot Γ)
--   := by rw [Nat.liftnBot_iterate, <-Region.effect_liftBot2_vwk1]; rfl

@[simp]
theorem Region.effect_liftBot_vwk_succ (Γ : ℕ → ε) (e : Region φ)
  : (e.vwk Nat.succ).effect (Nat.liftBot Γ) = e.effect Γ
  := by rw [effect_vwk]; rfl

@[simp]
theorem Region.effect_liftnBot_vwk_add (Γ : ℕ → ε) (e : Region φ)
  : (e.vwk (· + n)).effect (Nat.liftnBot n Γ) = e.effect Γ
  := by rw [effect_vwk, Nat.liftnBot_comp_add]

theorem Region.effect_lwk (ρ : ℕ → ℕ) (Γ : ℕ → ε) (r : Region φ)
  : (r.lwk ρ).effect Γ = r.effect Γ
  := by induction r generalizing Γ ρ
    <;> simp [Term.effect_wk, Nat.liftBot_comp_liftWk, *]

@[simp]
theorem Region.effect_comp_lwk (ρ : ℕ → ℕ) (Γ : ℕ → ε)
  : effect Γ ∘ @lwk φ ρ = effect Γ
  := by funext i; simp [effect_lwk]

/-- Infer the control effect of a `Region`, _without_ taking control-flow into account -/
@[simp]
def Region.control_effect (Γ : ℕ → ε) : Region φ → ε
  | br _ e => e.effect Γ
  | let1 _ r => r.control_effect (Nat.liftBot Γ)
  | let2 _ r => r.control_effect (Nat.liftnBot 2 Γ)
  | case e s t => e.effect Γ ⊔ s.control_effect (Nat.liftBot Γ) ⊔ t.control_effect (Nat.liftBot Γ)
  | cfg β _ G => β.control_effect Γ ⊔ Fin.sup (λi => (G i).control_effect (Nat.liftBot Γ))

theorem Region.control_effect_vwk (ρ : ℕ → ℕ) (Γ : ℕ → ε) (r : Region φ)
  : (r.vwk ρ).control_effect Γ = r.control_effect (Γ ∘ ρ)
  := by induction r generalizing Γ ρ
    <;> simp [Term.effect_wk, Nat.liftBot_comp_liftWk, Nat.liftnBot_comp_liftnWk, *]

theorem Region.control_effect_lwk (ρ : ℕ → ℕ) (Γ : ℕ → ε) (r : Region φ)
  : (r.lwk ρ).control_effect Γ = r.control_effect Γ
  := by induction r generalizing Γ ρ
    <;> simp [Term.effect_wk, Nat.liftBot_comp_liftWk, *]

/-- Infer the jump effect of a `Region`, _without_ taking control-flow into account -/
@[simp]
def Region.jump_effect (Γ : ℕ → ε) : Region φ → ε
  | br _ e => e.effect Γ
  | let1 _ r => r.jump_effect (Nat.liftBot Γ)
  | let2 _ r => r.jump_effect (Nat.liftnBot 2 Γ)
  | case _ s t => s.jump_effect (Nat.liftBot Γ) ⊔ t.jump_effect (Nat.liftBot Γ)
  | cfg β _ G => β.jump_effect Γ ⊔ Fin.sup (λi => (G i).jump_effect (Nat.liftBot Γ))

theorem Region.jump_effect_vwk (ρ : ℕ → ℕ) (Γ : ℕ → ε) (r : Region φ)
  : (r.vwk ρ).jump_effect Γ = r.jump_effect (Γ ∘ ρ)
  := by induction r generalizing Γ ρ
    <;> simp [Term.effect_wk, Nat.liftBot_comp_liftWk, Nat.liftnBot_comp_liftnWk, *]

theorem Region.jump_effect_lwk (ρ : ℕ → ℕ) (Γ : ℕ → ε) (r : Region φ)
  : (r.lwk ρ).jump_effect Γ = r.jump_effect Γ
  := by induction r generalizing Γ ρ
    <;> simp [Term.effect_wk, Nat.liftBot_comp_liftWk, *]

/-- Infer the branch effect of a `Region` to a target -/
@[simp]
def Region.trg_effect (target : ℕ) (Γ : ℕ → ε) : Region φ → ε
  | br ℓ e => if ℓ = target then e.effect Γ else ⊥
  | let1 _ r => r.trg_effect target (Nat.liftBot Γ)
  | let2 _ r => r.trg_effect target (Nat.liftnBot 2 Γ)
  | case _ s t => s.trg_effect target (Nat.liftBot Γ) ⊔ t.trg_effect target (Nat.liftBot Γ)
  | cfg β n G => β.trg_effect target Γ
    ⊔ Fin.sup (λi => (G i).trg_effect (target + n) (Nat.liftBot Γ))

/-- Infer the branch effect of a `Region` to a set of targets -/
@[simp]
def Region.trg_set_effect (targets : Multiset ℕ) (Γ : ℕ → ε) : Region φ → ε
  | br ℓ e => if ℓ ∈ targets then e.effect Γ else ⊥
  | let1 _ r => r.trg_set_effect targets (Nat.liftBot Γ)
  | let2 _ r => r.trg_set_effect targets (Nat.liftnBot 2 Γ)
  | case _ s t => s.trg_set_effect targets (Nat.liftBot Γ) ⊔ t.trg_set_effect targets (Nat.liftBot Γ)
  | cfg β n G => β.trg_set_effect targets Γ
    ⊔ Fin.sup (λi => (G i).trg_set_effect (targets.liftnFv n) (Nat.liftBot Γ))

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
  -- | abort _ I => exact I
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
    | zero => simp
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
    | zero => simp
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
    | zero => simp
    | succ n I =>
      rw [Fin.sup_succ, Fin.sup_succ]
      apply sup_le_sup
      apply IG 0 (Nat.liftBot_mono H)
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
    | zero => simp
    | succ n I =>
      rw [Fin.sup_succ, Fin.sup_succ]
      apply sup_le_sup
      apply IG 0 (Nat.liftBot_mono H)
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
    | zero => simp
    | succ n I =>
      rw [Fin.sup_succ, Fin.sup_succ]
      apply sup_le_sup
      apply IG 0 (Nat.liftBot_mono H)
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
    | zero => simp
    | succ n I =>
      rw [Fin.sup_succ, Fin.sup_succ]
      apply sup_le_sup
      apply IG 0 (Nat.liftBot_mono H)
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
  := by simp only [jump_effect, control_effect, Terminator.jump_effect_le_control_effect]

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
