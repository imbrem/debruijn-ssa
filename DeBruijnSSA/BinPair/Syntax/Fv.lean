import Discretion.Wk.Fun
import Discretion.Wk.Multiset
import DeBruijnSSA.BinPair.Syntax.Definitions
import Discretion.Wk.Multiset

import DeBruijnSSA.BinPair.Syntax.Subst

namespace BinPair

/-! ### Free variables and labels

Definitions and lemmas about free variables and free labels
 -/
section Definitions

/-- Get the set of free variables of a term as a multiset (to allow counting occurences) -/
@[simp]
def Term.fv : Term φ → Multiset ℕ
  | var x => {x}
  | op _ x => x.fv
  | pair x y => x.fv + y.fv
  | _ => 0

theorem Term.fv_wk (ρ : ℕ → ℕ) (t : Term φ) : (t.wk ρ).fv = t.fv.map ρ := by
  induction t <;> simp [*]

/-- Get the index of the highest free variable in this term, plus one -/
@[simp]
def Term.fvi : Term φ → ℕ
  | var x => x + 1
  | op _ x => x.fvi
  | pair x y => Nat.max x.fvi y.fvi
  | _ => 0

theorem Term.fvi_zero_iff_fv_zero (t : Term φ) : t.fvi = 0 ↔ t.fv = 0 := by
  induction t <;> simp [*]

/-- The free variables in this body -/
@[simp]
def Body.fv : Body φ → Multiset ℕ
  | nil => 0
  | let1 e t => e.fv + t.fv.liftFv
  | let2 e t => e.fv + t.fv.liftnFv 2

theorem Body.fv_wk (ρ : ℕ → ℕ) (b : Body φ) : (b.wk ρ).fv = b.fv.map ρ := by
  induction b generalizing ρ <;>
  simp [Term.fv_wk, *]

/-- The highest free variable in this body, plus one -/
@[simp]
def Body.fvi : Body φ → ℕ
  | nil => 0
  | let1 e t => Nat.max e.fvi (t.fvi - 1)
  | let2 e t => Nat.max e.fvi (t.fvi - 2)

/-- The free variables of this terminator -/
@[simp]
def Terminator.fv : Terminator φ → Multiset ℕ
  | br _ e => e.fv
  | ite e s t => e.fv + s.fv + t.fv

theorem Terminator.fv_vwk (ρ : ℕ → ℕ) (r : Terminator φ) : (r.vwk ρ).fv = r.fv.map ρ := by
  induction r <;> simp [*, Term.fv_wk]

theorem Terminator.fv_lwk (ρ : ℕ → ℕ) (r : Terminator φ) : (r.lwk ρ).fv = r.fv := by
  induction r <;> simp [*]

/-- The highest free variable in this terminator, plus one -/
@[simp]
def Terminator.fvi : Terminator φ → ℕ
  | br _ e => e.fvi
  | ite e s t => Nat.max e.fvi (Nat.max s.fvi t.fvi)

/-- The free labels of this terminator -/
@[simp]
def Terminator.fl : Terminator φ → Multiset ℕ
  | br n _ => {n}
  | ite _ s t => s.fl + t.fl

theorem Terminator.fl_vwk (ρ : ℕ → ℕ) (r : Terminator φ) : (r.vwk ρ).fl = r.fl := by
  induction r <;> simp [*]

theorem Terminator.fl_lwk (ρ : ℕ → ℕ) (r : Terminator φ) : (r.lwk ρ).fl = r.fl.map ρ := by
  induction r <;> simp [*]

/-- The highest free label in this terminator, plus one -/
@[simp]
def Terminator.fli : Terminator φ → ℕ
  | br n _ => n + 1
  | ite _ s t => Nat.max s.fli t.fli

/-- The free variables in this basic block -/
@[simp]
def Block.fv (β : Block φ) : Multiset ℕ := β.body.fv + β.terminator.fv.liftnFv β.body.num_defs

theorem Block.fv_vwk (ρ : ℕ → ℕ) (β : Block φ) : (β.vwk ρ).fv = β.fv.map ρ := by
  simp [Terminator.fv_vwk, Body.fv_wk, Body.num_defs_wk]

/-- The highest free variable in this basic block, plus one -/
@[simp]
def Block.fvi (β : Block φ) : ℕ := Nat.max β.body.fvi (β.terminator.fvi - β.body.num_defs)

/-- The free labels in this basic block -/
@[simp]
def Block.fl (β : Block φ) : Multiset ℕ := β.terminator.fl

theorem Block.fl_vwk (ρ : ℕ → ℕ) (β : Block φ) : (β.vwk ρ).fl = β.fl := by
  simp [Terminator.fl_vwk]

/-- The highest free label in this basic block, plus one -/
@[simp]
def Block.fli (β : Block φ) : ℕ := β.terminator.fli

/-- The free variables in this region -/
@[simp]
def BBRegion.fv : BBRegion φ → Multiset ℕ
  | cfg β _ f => β.fv + Finset.sum Finset.univ (λi => (f i).fv.liftnFv (β.body.num_defs + 1))

theorem BBRegion.fv_vwk (ρ : ℕ → ℕ) (r : BBRegion φ) : (r.vwk ρ).fv = r.fv.map ρ := by
  induction r generalizing ρ
  simp only [fv, Block.fv, Block.vwk, Body.fv_wk, Body.num_defs_wk, Terminator.fv_vwk,
    Multiset.liftnFv_map_liftnWk, Nat.liftnWk_succ', Function.comp_apply, Multiset.map_add,
    Multiset.map_finsum, add_right_inj, *]
  congr
  funext i
  rw [
    Multiset.liftnFv_succ,
    Multiset.liftFv_map_liftWk,
    Multiset.liftnFv_map_liftnWk,
    Multiset.liftnFv_succ]

theorem BBRegion.fv_lwk (ρ : ℕ → ℕ) (r : BBRegion φ) : (r.lwk ρ).fv = r.fv := by
  induction r generalizing ρ; simp [Terminator.fv_lwk, *]

/-- The free label variables in this region -/
@[simp]
def BBRegion.fl : BBRegion φ → Multiset ℕ
  | cfg β n f => β.fl.liftnFv n + Finset.sum Finset.univ (λi => (f i).fl.liftnFv n)

theorem BBRegion.fl_vwk (ρ : ℕ → ℕ) (r : BBRegion φ) : (r.vwk ρ).fl = r.fl := by
  induction r generalizing ρ; simp [Terminator.fl_vwk, *]

theorem BBRegion.fl_lwk (ρ : ℕ → ℕ) (r : BBRegion φ) : (r.lwk ρ).fl = r.fl.map ρ := by
  induction r generalizing ρ; simp [Terminator.fl_lwk, Multiset.map_finsum, *]

/- The free variables in this control-flow graph -/
@[simp]
def BBCFG.fv (cfg : BBCFG φ) : Multiset ℕ := Finset.sum Finset.univ (λi => (cfg.targets i).fv)

/- The free label variables in this control-flow graph -/
@[simp]
def BBCFG.fl (cfg : BBCFG φ) : Multiset ℕ := Finset.sum Finset.univ (λi => (cfg.targets i).fl)

/-- The free variables in this region -/
@[simp]
def TRegion.fv : TRegion φ → Multiset ℕ
  | let1 e t => e.fv + t.fv.liftFv
  | let2 e t => e.fv + t.fv.liftnFv 2
  | cfg β _ f => β.fv + Finset.sum Finset.univ (λi => (f i).fv.liftFv)

/-- The free label variables in this region -/
@[simp]
def TRegion.fl : TRegion φ → Multiset ℕ
  | let1 _ t => t.fl
  | let2 _ t => t.fl
  | cfg β n f => β.fl + Finset.sum Finset.univ (λi => (f i).fl.liftnFv n)

/-- The free variables in this control-flow graph -/
@[simp]
def TCFG.fv (cfg : TCFG φ) : Multiset ℕ := Finset.sum Finset.univ (λi => (cfg.targets i).fv)

/-- The free label variables in this control-flow graph -/
@[simp]
def TCFG.fl (cfg : TCFG φ) : Multiset ℕ := Finset.sum Finset.univ (λi => (cfg.targets i).fl)

/-- The free variables in this region -/
@[simp]
def Region.fv : Region φ → Multiset ℕ
  | br _ e => e.fv
  | ite e s t => e.fv + s.fv + t.fv
  | let1 e t => e.fv + t.fv.liftFv
  | let2 e t => e.fv + t.fv.liftnFv 2
  | cfg β _ f => β.fv + Finset.sum Finset.univ (λi => (f i).fv.liftnFv 1)

/-- The free label variables in this region -/
@[simp]
def Region.fl : Region φ → Multiset ℕ
  | br n _ => {n}
  | ite _ s t => s.fl + t.fl
  | let1 _ t => t.fl
  | let2 _ t => t.fl
  | cfg β n f => β.fl + Finset.sum Finset.univ (λi => (f i).fl.liftnFv n)

/-- The free variables in this control-flow graph -/
@[simp]
def CFG.fv (cfg : CFG φ) : Multiset ℕ := Finset.sum Finset.univ (λi => (cfg.targets i).fv)

/-- The free label variables in this control-flow graph -/
@[simp]
def CFG.fl (cfg : CFG φ) : Multiset ℕ := Finset.sum Finset.univ (λi => (cfg.targets i).fl)

end Definitions

/-! ### Lemmas about substitution -/
section Subst

theorem Terminator.fl_vsubst (σ : Term.Subst φ) (r : Terminator φ) : (r.vsubst σ).fl = r.fl := by
  induction r <;> simp [*]

end Subst

end BinPair

/-
TODO CORNER:
- Fill in rest of fvi, fli
- fv/fvi coerce, etc
-/
