import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.CategoryTheory.PathCategory
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Discretion.Correspondence.Definitions

import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Effect.Subst
import DeBruijnSSA.BinSyntax.Syntax.Fv
import DeBruijnSSA.BinSyntax.Syntax.Compose.Region

namespace BinSyntax

variable {φ : Type u} {ε : Type v} [Φ: EffectSet φ ε] [SemilatticeSup ε] [OrderBot ε]

-- -- TODO: define as Subst.cons or smt...
-- def Term.subst₂ (a b: Term φ) : Subst φ
--   | 0 => a
--   | 1 => b
--   | n + 2 => Term.var n

namespace Region

open Term

-- TODO: CongD is effect monotone/antitone iff underlying is
-- ==> CongD is effect preserving iff underlying is

-- TODO: make these rewrites bidirectional

-- That is, weakenings induce a prefunctor

-- That is, label weakenings induce a prefunctor

-- TODO: eqv_lwk

inductive ReduceD : Region φ → Region φ → Type _
  | case_inl (e r s) : ReduceD (case (inl e) r s) (let1 e r)
  | case_inr (e r s) : ReduceD (case (inr e) r s) (let1 e s)
  | wk_cfg (β n G k) (ρ : Fin k → Fin n) :
    ReduceD
      (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
      (cfg β k (G ∘ ρ))
  | dead_cfg_left (β n G m G') :
    ReduceD
      (cfg (β.lwk (· + n)) (n + m) (Fin.addCases G (lwk (· + n) ∘ G')))
      (cfg β m G')
  -- | ucfg (β n G) : ReduceD (cfg β n G) (ucfg n β G)
  -- | codiagonal (β G : Region φ) :
  --   ReduceD
  --     (cfg β 1 (Fin.elim1 (cfg nil 1 (Fin.elim1 G.vwk1))))
  --     (cfg β 1 (Fin.elim1 $ G.lsubst nil.lsubst0))

inductive Reduce : Region φ → Region φ → Prop
  | case_inl (e r s) : Reduce (case (inl e) r s) (let1 e r)
  | case_inr (e r s) : Reduce (case (inr e) r s) (let1 e s)
  | wk_cfg (β n G k) (ρ : Fin k → Fin n) :
    Reduce
      (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
      (cfg β k (G ∘ ρ))
  | dead_cfg_left (β n G m G') :
    Reduce
      (cfg (β.lwk (· + n)) (n + m) (Fin.addCases G (lwk (· + n) ∘ G')))
      (cfg β m G')
  -- | ucfg (β n G) : Reduce (cfg β n G) (ucfg n β G)
  -- | codiagonal (β G : Region φ) :
  --   Reduce
  --     (cfg β 1 (Fin.elim1 (cfg nil 1 (Fin.elim1 G.vwk1))))
  --     (cfg β 1 (Fin.elim1 $ G.lsubst nil.lsubst0))

theorem ReduceD.reduce {r r' : Region φ} (p : ReduceD r r') : Reduce r r'
  := by cases p <;> constructor

theorem Reduce.nonempty {r r' : Region φ} (p : Reduce r r') : Nonempty (ReduceD r r')
  := by cases p <;> constructor <;> constructor

theorem Reduce.of_nonempty {r r' : Region φ} (p : Nonempty (ReduceD r r')) : Reduce r r'
  := let ⟨p⟩ := p; p.reduce

theorem Reduce.nonempty_iff {r r' : Region φ} : Reduce r r' ↔ Nonempty (ReduceD r r')
  := ⟨Reduce.nonempty, Reduce.of_nonempty⟩

theorem Reduce.fvs_le {r r' : Region φ} (p : Reduce r r') : r'.fvs ⊆ r.fvs := by cases p with
  | case_inl e r s => simp
  | case_inr e r s =>
    simp only [fvs, Term.fvs, Set.union_subset_iff, Set.subset_union_right, and_true]
    rw [Set.union_assoc]
    simp
  | wk_cfg β n G k ρ =>
    simp only [fvs, Function.comp_apply, fvs_lwk, Set.union_subset_iff, Set.subset_union_left,
      Set.iUnion_subset_iff, true_and]
    intro i
    apply Set.subset_union_of_subset_right
    apply Set.subset_iUnion_of_subset (ρ i)
    rfl
  | dead_cfg_left β n G m G' =>
    simp only [fvs, fvs_lwk, Fin.comp_addCases_apply, Set.iUnion_addCases, Function.comp_apply]
    apply Set.union_subset_union_right
    apply Set.subset_union_right
  -- | ucfg β n G => sorry

def ReduceD.cast_trg {r₀ r₁ r₁' : Region φ} (p : ReduceD r₀ r₁) (h : r₁ = r₁')
  : ReduceD r₀ r₁' := h ▸ p

def ReduceD.cast_src {r₀ r₀' r₁ : Region φ} (h : r₀' = r₀) (p : ReduceD r₀ r₁)
  : ReduceD r₀' r₁ := h ▸ p

def ReduceD.cast {r₀ r₀' r₁ r₁' : Region φ} (h₀ : r₀ = r₀') (h₁ : r₁ = r₁')
  (p : ReduceD r₀ r₁) : ReduceD r₀' r₁' := h₁ ▸ h₀ ▸ p

def ReduceD.vwk {r r' : Region φ} (ρ : ℕ → ℕ) (d : ReduceD r r') : ReduceD (r.vwk ρ) (r'.vwk ρ)
  := by cases d with
  | dead_cfg_left β n G m G' =>
    simp only [Region.vwk, wk, Function.comp_apply, vwk_lwk, Fin.comp_addCases_apply]
    rw [<-Function.comp.assoc, vwk_comp_lwk, Function.comp.assoc]
    apply dead_cfg_left
  -- | ucfg β n G =>
  --   sorry
  | _ =>
    simp only [Region.vwk, wk, Function.comp_apply, vwk_lwk]
    constructor

theorem Reduce.vwk {r r' : Region φ} (ρ : ℕ → ℕ) (p : Reduce r r') : Reduce (r.vwk ρ) (r'.vwk ρ)
  := let ⟨d⟩ := p.nonempty; (d.vwk ρ).reduce

def ReduceD.lwk {r r' : Region φ} (ρ : ℕ → ℕ) (d : ReduceD r r') : ReduceD (r.lwk ρ) (r'.lwk ρ)
  := by cases d with
  | dead_cfg_left β n G m G' =>
    apply cast_src _
    apply dead_cfg_left
      (β := β.lwk (Nat.liftnWk m ρ))
      (n := n) (G := (Region.lwk (Nat.liftnWk (n + m) ρ)) ∘ G)
      (m := m) (G' := (Region.lwk (Nat.liftnWk m ρ)) ∘ G')
    simp only [
      Region.lwk, lwk_lwk, Region.lwk_addCases, <-Function.comp.assoc, Region.comp_lwk,
      Nat.liftnWk_comp_add_right
    ]
  | wk_cfg β n G k σ =>
    simp only [Region.lwk, Region.lwk_lwk, Function.comp_apply, Fin.liftnWk_comp_toNatWk]
    simp only [<-Region.lwk_lwk]
    apply wk_cfg
  -- | ucfg β n G =>
  --   sorry
  | _ =>
    simp only [Region.lwk, wk, Function.comp_apply, lwk_vwk]
    constructor

theorem Reduce.lwk {r r' : Region φ} (ρ : ℕ → ℕ) (p : Reduce r r') : Reduce (r.lwk ρ) (r'.lwk ρ)
  := let ⟨d⟩ := p.nonempty; (d.lwk ρ).reduce

theorem ReduceD.effect_le {Γ : ℕ → ε} {r r' : Region φ} (p : ReduceD r r')
  : r'.effect Γ ≤ r.effect Γ := by
  cases p with
  | case_inl _ _ _ => simp
  | case_inr e r s =>
    simp only [effect, Term.effect]
    rw [sup_assoc, sup_comm (r.effect _), <-sup_assoc]
    simp
  | wk_cfg _ _ _ _ _ =>
    simp only [effect_cfg, effect_lwk, <-Function.comp.assoc, effect_comp_lwk]
    apply sup_le_sup_left
    apply Fin.sup_comp_le
  | dead_cfg_left _ _ _ _ =>
    simp only [effect_cfg, effect_lwk, Fin.comp_addCases, Fin.sup_addCases]
    apply sup_le_sup_left
    apply le_sup_of_le_right
    rw [<-Function.comp.assoc, effect_comp_lwk]
  -- | ucfg β n G =>
  --   sorry
