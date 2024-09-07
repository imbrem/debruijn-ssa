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

def ReduceD.vsubst {r r' : Region φ} (σ : Term.Subst φ) (d : ReduceD r r')
  : ReduceD (r.vsubst σ) (r'.vsubst σ) := by cases d with
  | case_inl e r s => exact case_inl (e.subst σ) (r.vsubst σ.lift) (s.vsubst σ.lift)
  | case_inr e r s => exact case_inr (e.subst σ) (r.vsubst σ.lift) (s.vsubst σ.lift)
  | wk_cfg β n G k ρ =>
    convert wk_cfg (β.vsubst σ) n (λi => (G i).vsubst σ.lift) k ρ
    simp only [BinSyntax.Region.vsubst, vsubst_lwk, Function.comp_apply, cfg.injEq, heq_eq_eq,
      true_and]
    rfl
  | dead_cfg_left β n G m G' =>
    convert dead_cfg_left (β.vsubst σ) n (λi => (G i).vsubst σ.lift) m (λi => (G' i).vsubst σ.lift)
    simp only [BinSyntax.Region.vsubst, vsubst_lwk, Function.comp_apply, cfg.injEq, heq_eq_eq,
      true_and]
    funext i
    simp only [Fin.addCases, Function.comp_apply, eq_rec_constant]
    split <;> simp [vsubst_lwk]

theorem Reduce.vsubst
  {r r' : Region φ} (σ : Term.Subst φ) (p : Reduce r r') : Reduce (r.vsubst σ) (r'.vsubst σ)
  := let ⟨d⟩ := p.nonempty; (d.vsubst σ).reduce

def ReduceD.lsubst {r r' : Region φ} (σ : Subst φ) (d : ReduceD r r')
  : ReduceD (r.lsubst σ) (r'.lsubst σ) := by cases d with
  | case_inl e r s => exact case_inl e (r.lsubst σ.vlift) (s.lsubst σ.vlift)
  | case_inr e r s => exact case_inr e (r.lsubst σ.vlift) (s.lsubst σ.vlift)
  | wk_cfg β n G k ρ =>
    convert wk_cfg (β.lsubst (σ.liftn k)) n (λi => (G i).lsubst (σ.liftn k).vlift) k ρ
    simp only [
      BinSyntax.Region.lsubst, lsubst_lwk, Function.comp_apply, cfg.injEq, heq_eq_eq, true_and]
    constructor
    · rw [<-lsubst_fromLwk, lsubst_lsubst]; congr
      funext i
      simp only [Function.comp_apply, Subst.liftn, Fin.toNatWk, Subst.comp, Subst.fromLwk_vlift]
      split
      · simp [Fin.toNatWk, *]
      · simp only [add_lt_iff_neg_right, not_lt_zero', ↓reduceIte, add_tsub_cancel_right,
        lsubst_fromLwk, lwk_lwk]
        congr; funext i
        simp [Fin.toNatWk]
    · funext i
      simp only [← lsubst_fromLwk, Function.comp_apply, lsubst_lsubst]; congr
      funext i
      simp only [Function.comp_apply, Subst.liftn, Fin.toNatWk, Subst.comp, Subst.fromLwk_vlift]
      split
      · simp [Subst.vlift, Subst.liftn, vwk1, Fin.toNatWk, *]
      · simp only [Subst.vlift, Function.comp_apply, Subst.liftn, add_lt_iff_neg_right,
        not_lt_zero', ↓reduceIte, add_tsub_cancel_right, vwk1_lwk, *]
        simp only [← lsubst_fromLwk, lsubst_lsubst]
        congr
        funext i; simp [Subst.comp, Fin.toNatWk]
  | dead_cfg_left β n G m G' =>
    convert dead_cfg_left (β.lsubst (σ.liftn m)) n (λi => (G i).lsubst (σ.liftn (n + m)).vlift) m
      (λi => (G' i).lsubst (σ.liftn m).vlift)
    simp only [
      BinSyntax.Region.lsubst, lsubst_lwk, Function.comp_apply, cfg.injEq, heq_eq_eq, true_and]
    constructor
    · simp only [←lsubst_fromLwk, lsubst_lsubst]
      congr
      funext i; simp_arith only [Function.comp_apply, Subst.liftn, Subst.comp, Subst.fromLwk_vlift]
      split; rfl
      simp only [lsubst_fromLwk, lwk_lwk, comp_add_right]
      congr 2
      funext i; omega
      rw [Nat.add_comm n m, Nat.add_sub_add_right]
    · funext i
      simp only [Fin.addCases, Function.comp_apply, eq_rec_constant]
      split; rfl
      simp only [<-lsubst_fromLwk, lsubst_lsubst]
      congr
      funext i
      simp_arith only [
        Subst.comp, BinSyntax.Region.lsubst, Subst.vlift, Function.comp_apply, Subst.liftn,
        Subst.vwk1_comp_fromLwk
      ]
      split
      · rfl
      · simp only [vsubst0_var0_vwk1, lsubst_fromLwk, ← vwk1_lwk, lwk_lwk, comp_add_right]
        congr 3
        funext i; omega
        rw [Nat.add_comm n m, Nat.add_sub_add_right]

theorem Reduce.lsubst
  {r r' : Region φ} (σ : Subst φ) (p : Reduce r r') : Reduce (r.lsubst σ) (r'.lsubst σ)
  := let ⟨d⟩ := p.nonempty; (d.lsubst σ).reduce

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
