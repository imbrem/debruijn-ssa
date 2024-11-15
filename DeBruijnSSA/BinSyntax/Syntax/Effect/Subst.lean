import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Effect.Definitions

namespace BinSyntax

section Definitions

variable [Φ : EffectSet φ ε] [Bot ε] [Max ε]

namespace Term

namespace Subst

def effect (Γ : ℕ → ε) (σ : Subst φ) : ℕ → ε := Term.effect Γ ∘ σ

def hasEffect [PartialOrder ε] (Γ : ℕ → ε) (σ : Subst φ) (e : ε) : Prop := ∀n, effect Γ σ n ≤ e

@[simp]
theorem effect_apply (Γ : ℕ → ε) (σ : Subst φ) (n : ℕ) : effect Γ σ n = Term.effect Γ (σ n) := rfl

theorem effect_liftBot_lift (Γ : ℕ → ε) (σ : Subst φ)
  : effect (Nat.liftBot Γ) (σ.lift) = Nat.liftBot (effect Γ σ)
  := by funext k; cases k <;> simp [Nat.liftBot, Term.effect_wk]

theorem effect_liftnBot_liftn (Γ : ℕ → ε) (σ : Subst φ)
  : effect (Nat.liftnBot n Γ) (σ.liftn n) = Nat.liftnBot n (effect Γ σ) := by
  simp only [Subst.liftn_eq_iterate_lift_apply, Nat.liftnWk_eq_iterate_liftWk, Nat.liftnBot_iterate]
  induction n with
  | zero => rfl
  | succ n I => simp only [Function.iterate_succ', Function.comp_apply, effect_liftBot_lift, I]

end Subst

theorem effect_subst (Γ : ℕ → ε) (σ : Subst φ) (e : Term φ)
  : (e.subst σ).effect Γ = e.effect (σ.effect Γ) := by induction e generalizing σ Γ
  <;> simp [Subst.effect_liftBot_lift, Subst.effect_liftnBot_liftn, *]

theorem effect_effect (Γ : ℕ → ε) (σ : Subst φ) (e : Term φ)
  : e.effect (σ.effect Γ) = (e.subst σ).effect Γ := (effect_subst Γ σ e).symm

end Term

namespace Terminator

namespace Subst

def jump_effect (Γ : ℕ → ε) (σ : Subst φ) : ℕ → ε := Terminator.jump_effect Γ ∘ σ

def hasJumpEffect [PartialOrder ε] (Γ : ℕ → ε) (σ : Subst φ) (e : ε) : Prop
  := ∀n, jump_effect Γ σ n ≤ e

def trg_effect (target : ℕ) (Γ : ℕ → ε) (σ : Subst φ) : ℕ → ε := Terminator.trg_effect target Γ ∘ σ

def hasTrgEffect [PartialOrder ε] (target : ℕ) (Γ : ℕ → ε) (σ : Subst φ) (e : ε) : Prop
  := ∀n, trg_effect target Γ σ n ≤ e

end Subst

theorem effect_vsubst (Γ : ℕ → ε) (σ : Term.Subst φ) (t : Terminator φ)
  : (t.vsubst σ).effect Γ = t.effect (σ.effect Γ)
    := by induction t generalizing Γ σ
    <;> simp [Term.effect_subst, Term.Subst.effect_liftBot_lift, *]

end Terminator

namespace Region

namespace Subst

def jump_effect (Γ : ℕ → ε) (σ : Subst φ) : ℕ → ε := Region.jump_effect Γ ∘ σ

def hasJumpEffect [PartialOrder ε] (Γ : ℕ → ε) (σ : Subst φ) (e : ε) : Prop
  := ∀n, jump_effect Γ σ n ≤ e

def trg_effect (target : ℕ) (Γ : ℕ → ε) (σ : Subst φ) : ℕ → ε := Region.trg_effect target Γ ∘ σ

def hasTrgEffect [PartialOrder ε] (target : ℕ) (Γ : ℕ → ε) (σ : Subst φ) (e : ε) : Prop
  := ∀n, trg_effect target Γ σ n ≤ e

end Subst

theorem effect_vsubst (Γ : ℕ → ε) (σ : Term.Subst φ) (r : Region φ)
  : (r.vsubst σ).effect Γ = r.effect (σ.effect Γ)
    := by induction r generalizing Γ σ
    <;> simp [Term.effect_subst,
      Term.Subst.effect_liftBot_lift,
      Term.Subst.effect_liftnBot_liftn, *]

end Region

end Definitions
