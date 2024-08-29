import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.CategoryTheory.PathCategory
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Discretion.Correspondence.Definitions

import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Effect.Subst
import DeBruijnSSA.BinSyntax.Syntax.Fv

import DeBruijnSSA.BinSyntax.Syntax.Rewrite.Region.Rewrite
import DeBruijnSSA.BinSyntax.Syntax.Rewrite.Region.Equiv
import DeBruijnSSA.BinSyntax.Syntax.Rewrite.Region.Reduce

import DeBruijnSSA.BinSyntax.Syntax.Rewrite.Region.Cong

namespace BinSyntax

variable {φ : Type u} {ε : Type v} [Φ: EffectSet φ ε] [SemilatticeSup ε] [OrderBot ε]

-- -- TODO: define as Subst.cons or smt...
-- def Term.subst₂ (a b: Term φ) : Subst φ
--   | 0 => a
--   | 1 => b
--   | n + 2 => Term.var n

namespace Region

open Term

inductive StepD (Γ : ℕ → ε) : Region φ → Region φ → Type _
  | let1_beta (e r) : e.effect Γ = ⊥ → StepD Γ (let1 e r) (r.vsubst e.subst0)
  | reduce {r r'} : ReduceD r r' → StepD Γ r r'
  | rw {r r'} : RewriteD r r' → StepD Γ r r'
  | rw_op {r r'} : RewriteD r r' → StepD Γ r' r

-- TODO: separate beta relation? Then step is just the inf...

inductive Step (Γ : ℕ → ε) : Region φ → Region φ → Prop
  | let1_beta (e r) : e.effect Γ = ⊥ → Step Γ (let1 e r) (r.vsubst e.subst0)
  | reduce {r r'} : Reduce r r' → Step Γ r r'
  | rw {r r'} : Rewrite r r' → Step Γ r r'
  | rw_op {r r'} : Rewrite r r' → Step Γ r' r

theorem StepD.step {Γ : ℕ → ε} {r r' : Region φ} : StepD Γ r r' → Step Γ r r'
  | let1_beta e r he => Step.let1_beta e r he
  | reduce p => Step.reduce p.reduce
  | rw p => Step.rw p.rewrite
  | rw_op p => Step.rw_op p.rewrite

theorem Step.nonempty {Γ : ℕ → ε} {r r' : Region φ} : Step Γ r r' → Nonempty (StepD Γ r r')
  | let1_beta e r he => ⟨StepD.let1_beta e r he⟩
  | reduce p => let ⟨d⟩ := p.nonempty; ⟨StepD.reduce d⟩
  | rw p => let ⟨d⟩ := p.nonempty; ⟨StepD.rw d⟩
  | rw_op p => let ⟨d⟩ := p.nonempty; ⟨StepD.rw_op d⟩

theorem Step.nonempty_iff {Γ : ℕ → ε} {r r' : Region φ} : Step Γ r r' ↔ Nonempty (StepD Γ r r')
  := ⟨Step.nonempty, λ⟨d⟩ => d.step⟩

def StepD.vwk {Γ : ℕ → ε} {r r' : Region φ} (ρ : ℕ → ℕ)
  : StepD (Γ ∘ ρ) r r' → StepD Γ (r.vwk ρ) (r'.vwk ρ)
  | let1_beta e r he => by
    simp only [Region.vwk, vsubst_subst0_vwk]
    apply let1_beta
    rw [Term.effect_wk]
    assumption
  | reduce p => reduce $ p.vwk ρ
  | rw p => rw $ p.vwk ρ
  | rw_op p => rw_op $ p.vwk ρ

theorem Step.vwk {Γ : ℕ → ε} {r r' : Region φ} (ρ : ℕ → ℕ) (p : Step (Γ ∘ ρ) r r')
  : Step Γ (r.vwk ρ) (r'.vwk ρ) := let ⟨d⟩ := p.nonempty; (d.vwk ρ).step

inductive FStepD (Γ : ℕ → ε) : Region φ → Region φ → Type _
  | let1_beta (e r) : e.effect Γ = ⊥ → FStepD Γ (let1 e r) (r.vsubst e.subst0)
  | reduce {r r'} : ReduceD r r' → FStepD Γ r r'
  | rw {r r'} : RewriteD r r' → FStepD Γ r r'

inductive FStep (Γ : ℕ → ε) : Region φ → Region φ → Prop
  | let1_beta (e r) : e.effect Γ = ⊥ → FStep Γ (let1 e r) (r.vsubst e.subst0)
  | reduce {r r'} : Reduce r r' → FStep Γ r r'
  | rw {r r'} : Rewrite r r' → FStep Γ r r'

theorem FStepD.step {Γ : ℕ → ε} {r r' : Region φ} : FStepD Γ r r' → FStep Γ r r'
  | let1_beta e r he => FStep.let1_beta e r he
  | reduce p => FStep.reduce p.reduce
  | rw p => FStep.rw p.rewrite

theorem FStep.nonempty {Γ : ℕ → ε} {r r' : Region φ} : FStep Γ r r' → Nonempty (FStepD Γ r r')
  | let1_beta e r he => ⟨FStepD.let1_beta e r he⟩
  | reduce p => let ⟨d⟩ := p.nonempty; ⟨FStepD.reduce d⟩
  | rw p => let ⟨d⟩ := p.nonempty; ⟨FStepD.rw d⟩

theorem FStep.nonempty_iff {Γ : ℕ → ε} {r r' : Region φ} : FStep Γ r r' ↔ Nonempty (FStepD Γ r r')
  := ⟨FStep.nonempty, λ⟨d⟩ => d.step⟩

-- theorem FStep.fvs_le {Γ : ℕ → ε} {r r' : Region φ} (p : FStep Γ r r')
--   : r'.fvs ⊆ r.fvs := by cases p with
--   | let1_beta e r he => apply fvs_vsubst0_le
--   | reduce p => exact p.fvs_le
--   | rw p => rw [p.fvs_eq]

def FStepD.vwk {Γ : ℕ → ε} {r r' : Region φ} (ρ : ℕ → ℕ)
  : FStepD (Γ ∘ ρ) r r' → FStepD Γ (r.vwk ρ) (r'.vwk ρ)
  | let1_beta e r he => by
    simp only [Region.vwk, vsubst_subst0_vwk]
    apply let1_beta
    rw [Term.effect_wk]
    assumption
  | reduce p => reduce $ p.vwk ρ
  | rw p => rw $ p.vwk ρ

theorem FStep.vwk {Γ : ℕ → ε} {r r' : Region φ} (ρ : ℕ → ℕ) (p : FStep (Γ ∘ ρ) r r')
  : FStep Γ (r.vwk ρ) (r'.vwk ρ) := let ⟨d⟩ := p.nonempty; (d.vwk ρ).step

def FStepD.wk_eff {Γ Δ : ℕ → ε} {r r' : Region φ}
  (h : ∀i ∈ r.fvs, Γ i ≤ Δ i) : FStepD Δ r r' → FStepD Γ r r'
  | let1_beta e r he => let1_beta e r (by
    have he' := e.effect_le (λi hi => h i (Or.inl hi));
    rw [he] at he'
    simp only [le_bot_iff] at he'
    exact he')
  | reduce p => reduce p
  | rw p => rw p

theorem FStep.wk_eff {Γ Δ : ℕ → ε} {r r' : Region φ}
  (h : ∀i ∈ r.fvs, Γ i ≤ Δ i) (p : FStep Δ r r') : FStep Γ r r'
  := let ⟨d⟩ := p.nonempty; (d.wk_eff h).step

def FStepD.lwk {Γ : ℕ → ε} {r r' : Region φ} (ρ : ℕ → ℕ)
  : FStepD Γ r r' → FStepD Γ (r.lwk ρ) (r'.lwk ρ)
  | let1_beta e r he => by
    rw [lwk_vsubst]
    apply let1_beta
    exact he
  | reduce p => reduce $ p.lwk ρ
  | rw p => rw $ p.lwk ρ

theorem FStep.lwk {Γ : ℕ → ε} {r r' : Region φ} (ρ : ℕ → ℕ) (p : FStep Γ r r')
  : FStep Γ (r.lwk ρ) (r'.lwk ρ) := let ⟨d⟩ := p.nonempty; (d.lwk ρ).step

@[match_pattern]
def StepD.case_inl {Γ : ℕ → ε} (e : Term φ) (r s)
  : StepD Γ (case (inl e) r s) (let1 e r)
  := StepD.reduce (ReduceD.case_inl e r s)

@[match_pattern]
def StepD.case_inr {Γ : ℕ → ε} (e : Term φ) (r s)
  : StepD Γ (case (inr e) r s) (let1 e s)
  := StepD.reduce (ReduceD.case_inr e r s)

@[match_pattern]
def StepD.wk_cfg {Γ : ℕ → ε} (β : Region φ) (n G k) (ρ : Fin k → Fin n)
  : StepD Γ (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
    (cfg β k (G ∘ ρ))
  := StepD.reduce (ReduceD.wk_cfg β n G k ρ)

@[match_pattern]
def StepD.dead_cfg_left {Γ : ℕ → ε} (β : Region φ) (n G m G')
  : StepD Γ (cfg (β.lwk (· + n)) (n + m) (Fin.addCases G (lwk (· + n) ∘ G')))
    (cfg β m G')
  := StepD.reduce (ReduceD.dead_cfg_left β n G m G')

@[match_pattern]
def StepD.let1_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : StepD Γ (let1 (op f e) r) (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := StepD.rw $ RewriteD.let1_op f e r

@[match_pattern]
def StepD.let1_op_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : StepD Γ (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (op f e) r)
  := StepD.rw_op $ RewriteD.let1_op f e r

@[match_pattern]
def StepD.let1_pair {Γ : ℕ → ε} (a b) (r : Region φ)
  : StepD Γ (let1 (pair a b) r)
    (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) r.vwk1.vwk1)
  := StepD.rw $ RewriteD.let1_pair a b r

@[match_pattern]
def StepD.let1_pair_op {Γ : ℕ → ε} (a b) (r : Region φ)
  : StepD Γ (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) r.vwk1.vwk1)
    (let1 (pair a b) r)
  := StepD.rw_op $ RewriteD.let1_pair a b r

@[match_pattern]
def StepD.let1_inl {Γ : ℕ → ε} (e) (r : Region φ)
  : StepD Γ (let1 (inl e) r) (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := StepD.rw $ RewriteD.let1_inl e r

@[match_pattern]
def StepD.let1_inl_op {Γ : ℕ → ε} (e) (r : Region φ)
  : StepD Γ (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (inl e) r)
  := StepD.rw_op $ RewriteD.let1_inl e r

@[match_pattern]
def StepD.let1_inr {Γ : ℕ → ε} (e) (r : Region φ)
  : StepD Γ (let1 (inr e) r) (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := StepD.rw $ RewriteD.let1_inr e r

@[match_pattern]
def StepD.let1_inr_op {Γ : ℕ → ε} (e) (r : Region φ)
  : StepD Γ (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (inr e) r)
  := StepD.rw_op $ RewriteD.let1_inr e r

@[match_pattern]
def StepD.let1_abort {Γ : ℕ → ε} (e) (r : Region φ)
  : StepD Γ (let1 (abort e) r) (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := StepD.rw $ RewriteD.let1_abort e r

@[match_pattern]
def StepD.let1_abort_op {Γ : ℕ → ε} (e) (r : Region φ)
  : StepD Γ (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (abort e) r)
  := StepD.rw_op $ RewriteD.let1_abort e r

@[match_pattern]
def StepD.cfg_br_lt {Γ : ℕ → ε} (ℓ) (e : Term φ) (n G) (h : ℓ < n)
  : StepD Γ (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).let1 e) n G)
  := StepD.rw $ RewriteD.cfg_br_lt ℓ e n G h

@[match_pattern]
def StepD.cfg_br_lt_op {Γ : ℕ → ε} (ℓ) (e : Term φ) (n G) (h : ℓ < n)
  : StepD Γ (cfg ((G ⟨ℓ, h⟩).let1 e) n G) (cfg (br ℓ e) n G)
  := StepD.rw_op $ RewriteD.cfg_br_lt ℓ e n G h

@[match_pattern]
def StepD.cfg_let1 {Γ : ℕ → ε} (a : Term φ) (β n G)
  : StepD Γ (cfg (let1 a β) n G) (let1 a $ cfg β n (vwk1 ∘ G))
  := StepD.rw $ RewriteD.cfg_let1 a β n G

@[match_pattern]
def StepD.cfg_let1_op {Γ : ℕ → ε} (a : Term φ) (β n G)
  : StepD Γ (let1 a $ cfg β n (vwk1 ∘ G))
    (cfg (let1 a β) n G)
  := StepD.rw_op $ RewriteD.cfg_let1 a β n G

@[match_pattern]
def StepD.cfg_let2 {Γ : ℕ → ε} (a : Term φ) (β n G)
  : StepD Γ (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk1 ∘ vwk1 ∘ G))
  := StepD.rw $ RewriteD.cfg_let2 a β n G

@[match_pattern]
def StepD.cfg_let2_op {Γ : ℕ → ε} (a : Term φ) (β n G)
  : StepD Γ (let2 a $ cfg β n (vwk1 ∘ vwk1 ∘ G))
    (cfg (let2 a β) n G)
  := StepD.rw_op $ RewriteD.cfg_let2 a β n G

@[match_pattern]
def StepD.cfg_case {Γ : ℕ → ε} (e : Term φ) (r s n G)
  : StepD Γ (cfg (case e r s) n G)
    (case e (cfg r n (vwk1 ∘ G)) (cfg s n (vwk1 ∘ G))
  )
  := StepD.rw $ RewriteD.cfg_case e r s n G

@[match_pattern]
def StepD.cfg_case_op {Γ : ℕ → ε} (e : Term φ) (r s n G)
  : StepD Γ (case e (cfg r n (vwk1 ∘ G)) (cfg s n (vwk1 ∘ G)))
    (cfg (case e r s) n G)
  := StepD.rw_op $ RewriteD.cfg_case e r s n G

@[match_pattern]
def StepD.cfg_cfg {Γ : ℕ → ε} (β : Region φ) (n G n' G')
  : StepD Γ (cfg (cfg β n G) n' G') (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
  := StepD.rw $ RewriteD.cfg_cfg β n G n' G'

@[match_pattern]
def StepD.cfg_cfg_op {Γ : ℕ → ε} (β : Region φ) (n G n' G')
  : StepD Γ (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
    (cfg (cfg β n G) n' G')
  := StepD.rw_op $ RewriteD.cfg_cfg β n G n' G'

@[match_pattern]
def StepD.cfg_zero {Γ : ℕ → ε} (β : Region φ) (G)
  : StepD Γ (cfg β 0 G) β := StepD.rw $ RewriteD.cfg_zero β G

@[match_pattern]
def StepD.cfg_zero_op {Γ : ℕ → ε} (β : Region φ) (G)
  : StepD Γ β (cfg β 0 G) := StepD.rw_op $ RewriteD.cfg_zero β G

@[match_pattern]
def StepD.let2_eta {Γ : ℕ → ε} (e) (r : Region φ)
  : StepD Γ (let2 e (let1 ((var 1).pair (var 0)) r.vwk1.vwk1)) (let1 e r)
  := StepD.rw $ RewriteD.let2_eta e r

@[match_pattern]
def StepD.let2_eta_op {Γ : ℕ → ε} (r : Region φ)
  : StepD Γ (let1 e r) (let2 e (let1 ((var 1).pair (var 0)) r.vwk1.vwk1))
  := StepD.rw_op $ RewriteD.let2_eta e r

-- @[match_pattern]
-- def StepD.let1_eta {Γ : ℕ → ε} (r : Region φ)
--   : StepD Γ (let1 (var 0) r.vwk1) r
--   := StepD.rw $ RewriteD.let1_eta r

-- @[match_pattern]
-- def StepD.let1_eta_op {Γ : ℕ → ε} (r : Region φ)
--   : StepD Γ r (let1 (var 0) r.vwk1)
--   := StepD.rw_op $ RewriteD.let1_eta r

def StepD.cast_trg {Γ : ℕ → ε} {r₀ r₁ r₁' : Region φ} (p : StepD Γ r₀ r₁) (h : r₁ = r₁')
  : StepD Γ r₀ r₁' := h ▸ p

def StepD.cast_src {Γ : ℕ → ε} {r₀ r₀' r₁ : Region φ} (h : r₀' = r₀) (p : StepD Γ r₀ r₁)
  : StepD Γ r₀' r₁ := h ▸ p

def StepD.cast {Γ : ℕ → ε} {r₀ r₀' r₁ r₁' : Region φ} (h₀ : r₀ = r₀') (h₁ : r₁ = r₁')
  (p : StepD Γ r₀ r₁) : StepD Γ r₀' r₁' := h₁ ▸ h₀ ▸ p

-- theorem StepD.effect_le {Γ : ℕ → ε} {r r' : Region φ} (p : StepD Γ r r')
--   : r'.effect Γ ≤ r.effect Γ := by
--   cases p with
--   | let1_beta _ _ he =>
--     apply le_of_eq
--     simp only [effect_vsubst, Subst.effect, effect, he, ge_iff_le, bot_le, sup_of_le_right]
--     congr
--     funext k
--     cases k with
--     | zero => simp [he, Nat.liftBot]
--     | succ k => rfl
--   | reduce p => exact p.effect_le
--   | rw p => rw [p.effect]
--   | rw_op p => rw [p.effect]
