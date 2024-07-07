import DeBruijnSSA.BinSyntax.Typing.Term
import DeBruijnSSA.BinSyntax.Syntax.Rewrite.Term.Step

import Discretion.Utils.Quotient

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

inductive TStep : (Γ : Ctx α ε) → (V : Ty α × ε) → (r r' : Term φ) → Prop
  | let1_beta : a.Wf Γ ⟨A, ⊥⟩ → b.Wf (⟨A, ⊥⟩::Γ) V → TStep Γ V (let1 a b) (b.subst a.subst0)
  | rewrite : r.Wf Γ V → r'.Wf Γ V → Rewrite r r' → TStep Γ V r r'
  | reduce : r.Wf Γ V → r'.Wf Γ V → Reduce r r' → TStep Γ V r r'
  | initial : Γ.IsInitial → e.Wf Γ V → e'.Wf Γ V → TStep Γ V e e'
  -- TODO: make this is IsTerminal?
  | terminal : a.Wf Γ ⟨Ty.unit, ⊥⟩ → a'.Wf Γ ⟨Ty.unit, ⊥⟩ → TStep Γ ⟨Ty.unit, e⟩ a a'

theorem TStep.left {e e' : Term φ} (h : TStep Γ V e e') : e.Wf Γ V := by cases h with
  | let1_beta da db => exact Term.Wf.let1 (da.wk_eff (by simp)) db
  | terminal de de' => exact de.wk_eff (by simp)
  | _ => assumption

theorem TStep.right {e e' : Term φ} (h : TStep Γ V e e') : e'.Wf Γ V := by cases h with
  | let1_beta da db => exact db.subst da.subst0
  | terminal de de' => exact de'.wk_eff (by simp)
  | _ => assumption

theorem TStep.cast_src {Γ L} {r₀' r₀ r₁ : Term φ} (h : r₀' = r₀) (p : TStep Γ L r₀ r₁)
  : TStep Γ L r₀' r₁ := h ▸ p

theorem TStep.cast_trg {Γ L} {r₀ r₁' r₁ : Term φ} (p : TStep Γ L r₀ r₁) (h : r₁ = r₁')
  : TStep Γ L r₀ r₁' := h ▸ p

theorem TStep.wf {Γ L} {r r' : Term φ} (h : TStep Γ L r r') : r.Wf Γ L ∧ r'.Wf Γ L
  := ⟨left h, right h⟩

theorem TStep.wk {Γ Δ : Ctx α ε} {L r r' ρ} (hρ : Γ.Wkn Δ ρ)
  : TStep (φ := φ) Δ L r r' → TStep Γ L (r.wk ρ) (r'.wk ρ)
  | let1_beta de dr => (let1_beta (de.wk hρ) (dr.wk hρ.slift)).cast_trg (by simp [subst_subst0_wk])
  | rewrite d d' p => rewrite (d.wk hρ) (d'.wk hρ) sorry--(p.wk ρ)
  | reduce d d' p => reduce (d.wk hρ) (d'.wk hρ) sorry--(p.wk ρ)
  | initial di d d' => initial (di.wk hρ) (d.wk hρ) (d'.wk hρ)
  | terminal de de' => terminal (de.wk hρ) (de'.wk hρ)

theorem TStep.wk_res {Γ : Ctx α ε} {L L'} (h : L ≤ L') {r r'}
  : TStep (φ := φ) Γ L r r' → TStep Γ L' r r'
  | let1_beta de dr => let1_beta de (dr.wk_res h)
  | rewrite d d' p => rewrite (d.wk_res h) (d'.wk_res h) p
  | reduce d d' p => reduce (d.wk_res h) (d'.wk_res h) p
  | initial di d d' => initial di (d.wk_res h) (d'.wk_res h)
  | terminal de de' => by
    cases L'
    cases h with
    | intro l r =>
      simp only at *
      cases l
      exact terminal de de'

theorem TStep.let1_beta_drop {Γ : Ctx α ε} {a b : Term φ} (ha : a.Wf Γ ⟨A, ⊥⟩) (hb : b.Wf Γ V)
  : TStep Γ V (let1 a b.wk0) b
  := (let1_beta ha hb.wk0).cast_trg sorry

-- NOTE: subst needs InS lore for initiality, so that's in Setoid.lean
