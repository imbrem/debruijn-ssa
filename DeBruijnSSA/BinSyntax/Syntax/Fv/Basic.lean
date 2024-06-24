import Discretion.Wk.Nat
import Discretion.Wk.Fin
import Discretion.Wk.Multiset
import Discretion.Wk.Multiset
import Mathlib.Data.ENat.Basic

import DeBruijnSSA.BinSyntax.Syntax.Definitions

namespace BinSyntax

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
  | inl a => a.fv
  | inr a => a.fv
  -- | abort a => a.fv
  | _ => 0

theorem Term.fv_wk (ρ : ℕ → ℕ) (t : Term φ) : (t.wk ρ).fv = t.fv.map ρ := by
  induction t <;> simp [*]

/-- Get the index of the highest free variable in this term, plus one -/
@[simp]
def Term.fvi : Term φ → ℕ
  | var x => x + 1
  | op _ x => x.fvi
  | pair x y => Nat.max x.fvi y.fvi
  | inl a => a.fvi
  | inr a => a.fvi
  -- | abort a => a.fvi
  | _ => 0

theorem Term.fvi_var_le_iff {x n : ℕ} : (@var φ x).fvi ≤ n ↔ x < n := by simp [Nat.succ_le_iff]

theorem Term.fvi_op_le_iff {o : φ} {t : Term φ} {n} : (op o t).fvi ≤ n ↔ t.fvi ≤ n := Iff.rfl

theorem Term.fvi_pair_le_iff {l r : Term φ} {n} : (pair l r).fvi ≤ n ↔ l.fvi ≤ n ∧ r.fvi ≤ n
  := by simp

theorem Term.fvi_pair_le_left {l r : Term φ} {n} : (pair l r).fvi ≤ n → l.fvi ≤ n
  := by simp only [fvi, max_le_iff, and_imp]; exact λl _ => l

theorem Term.fvi_pair_le_right {l r : Term φ} {n} : (pair l r).fvi ≤ n → r.fvi ≤ n
  := by simp only [fvi, max_le_iff, and_imp]; exact λ_ r => r

theorem Term.fvi_inl_le_iff {t : Term φ} {n : ℕ} : t.inl.fvi ≤ n ↔ t.fvi ≤ n := Iff.rfl

theorem Term.fvi_inr_le_iff {t : Term φ} {n : ℕ} : t.inr.fvi ≤ n ↔ t.fvi ≤ n := Iff.rfl

-- theorem Term.fvi_abort_le_iff {t : Term φ} {n : ℕ} : t.abort.fvi ≤ n ↔ t.fvi ≤ n := Iff.rfl

theorem Term.fvi_zero_iff_fv_zero (t : Term φ) : t.fvi = 0 ↔ t.fv = 0 := by
  induction t <;> simp [*]

/-- Get the count of how often a free variable occurs in this term -/
@[simp]
def Term.fvc (x : ℕ) : Term φ → ℕ
  | var y => if x = y then 1 else 0
  | op _ y => y.fvc x
  | pair y z => y.fvc x + z.fvc x
  | inl y => y.fvc x
  | inr y => y.fvc x
  -- | abort y => y.fvc x
  | _ => 0

theorem Term.fvc_eq_fv_count (x : ℕ) (t : Term φ) : t.fvc x = t.fv.count x := by
  induction t with
  | var y => simp [Multiset.count_singleton]
  | _ => simp [*]

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

/-- Get the count of how often a free variable occurs in this body -/
@[simp]
def Body.fvc (x : ℕ) : Body φ → ℕ
  | nil => 0
  | let1 e t => e.fvc x + t.fvc (x + 1)
  | let2 e t => e.fvc x + t.fvc (x + 2)

theorem Body.fvc_eq_fv_count (x : ℕ) (b : Body φ) : b.fvc x = b.fv.count x := by
  induction b generalizing x <;>
  simp [Term.fvc_eq_fv_count, Multiset.count_liftnFv, Multiset.count_liftFv, *]

/-- The free variables of this terminator -/
@[simp]
def Terminator.fv : Terminator φ → Multiset ℕ
  | br _ e => e.fv
  | case e s t => e.fv + s.fv.liftFv + t.fv.liftFv

theorem Terminator.fv_vwk (ρ : ℕ → ℕ) (r : Terminator φ) : (r.vwk ρ).fv = r.fv.map ρ := by
  induction r generalizing ρ <;> simp [*, Term.fv_wk]

theorem Terminator.fv_lwk (ρ : ℕ → ℕ) (r : Terminator φ) : (r.lwk ρ).fv = r.fv := by
  induction r <;> simp [*]

/-- The highest free variable in this terminator, plus one -/
@[simp]
def Terminator.fvi : Terminator φ → ℕ
  | br _ e => e.fvi
  | case e s t => Nat.max e.fvi (Nat.max (s.fvi - 1) (t.fvi - 1))

/-- Get the count of how often a free variable occurs in this terminator -/
@[simp]
def Terminator.fvc (x : ℕ) : Terminator φ → ℕ
  | br _ e => e.fvc x
  | case e s t => e.fvc x + s.fvc (x + 1) + t.fvc (x + 1)

/-- Get the count of how often a free variable occurs in this terminator, or ∞ if it appears
 in a special position. Currently all terminator positions count as special -/
@[simp]
def Terminator.sfvc (x : ℕ) : Terminator φ → ℕ∞
  | br _ e => if e.fvc x = 0 then 0 else ⊤
  | case e s t => e.fvc x + s.fvc (x + 1) + t.fvc (x + 1)

theorem Terminator.fvc_eq_fv_count (x : ℕ) (r : Terminator φ) : r.fvc x = r.fv.count x := by
  induction r generalizing x <;> simp [Term.fvc_eq_fv_count, Multiset.count_liftFv, *]

/-- The free labels of this terminator -/
@[simp]
def Terminator.fl : Terminator φ → Multiset ℕ
  | br n _ => {n}
  | case _ s t => s.fl + t.fl

theorem Terminator.fl_vwk (ρ : ℕ → ℕ) (r : Terminator φ) : (r.vwk ρ).fl = r.fl := by
  induction r generalizing ρ <;> simp [*]

theorem Terminator.fl_lwk (ρ : ℕ → ℕ) (r : Terminator φ) : (r.lwk ρ).fl = r.fl.map ρ := by
  induction r <;> simp [*]

/-- The highest free label in this terminator, plus one -/
@[simp]
def Terminator.fli : Terminator φ → ℕ
  | br n _ => n + 1
  | case _ s t => Nat.max s.fli t.fli

/-- The free variables in this basic block -/
@[simp]
def Block.fv (β : Block φ) : Multiset ℕ := β.body.fv + β.terminator.fv.liftnFv β.body.num_defs

theorem Block.fv_vwk (ρ : ℕ → ℕ) (β : Block φ) : (β.vwk ρ).fv = β.fv.map ρ := by
  simp [Terminator.fv_vwk, Body.fv_wk, Body.num_defs_wk]

theorem Block.fv_lwk (ρ : ℕ → ℕ) (β : Block φ) : (β.lwk ρ).fv = β.fv := by
  simp [Terminator.fv_lwk]

/-- The highest free variable in this basic block, plus one -/
@[simp]
def Block.fvi (β : Block φ) : ℕ := Nat.max β.body.fvi (β.terminator.fvi - β.body.num_defs)

/-- Get the count of how often a free variable occurs in this basic block -/
@[simp]
def Block.fvc (x : ℕ) (β : Block φ) : ℕ := β.body.fvc x + β.terminator.fvc (x + β.body.num_defs)

/-- Get the count of how often a free variable occurs in this basic block, or ∞ if it
  appears in a special position -/
@[simp]
def Block.sfvc (x : ℕ) (β : Block φ) : ℕ∞ := β.body.fvc x + β.terminator.sfvc (x + β.body.num_defs)

/-- The free labels in this basic block -/
@[simp]
def Block.fl (β : Block φ) : Multiset ℕ := β.terminator.fl

theorem Block.fl_vwk (ρ : ℕ → ℕ) (β : Block φ) : (β.vwk ρ).fl = β.fl := by
  simp [Terminator.fl_vwk]

theorem Block.fl_lwk (ρ : ℕ → ℕ) (β : Block φ) : (β.lwk ρ).fl = β.fl.map ρ := by
  simp [Terminator.fl_lwk]

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

/-- Get the count of how often a free variable occurs in this region -/
@[simp]
def BBRegion.fvc (x : ℕ) : BBRegion φ → ℕ
  | cfg β _ f => β.fvc x + Finset.sum Finset.univ (λi => (f i).fvc (x + β.body.num_defs + 1))

/-- Get the count of how often a free variable occurs in this region, or ∞ if it appears
 in a special position. -/
@[simp]
def BBRegion.sfvc (x : ℕ) : BBRegion φ → ℕ∞
  | cfg β _ f => β.sfvc x + Finset.sum Finset.univ (λi => (f i).sfvc (x + β.body.num_defs + 1))

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
  | cfg β _ G => β.fv + Finset.sum Finset.univ (λi => (G i).fv.liftFv)

/-- The highest free variable in this region, plus one -/
@[simp]
def TRegion.fvi : TRegion φ → ℕ
  | let1 e t => Nat.max e.fvi (t.fvi - 1)
  | let2 e t => Nat.max e.fvi (t.fvi - 2)
  | cfg β _ G => Nat.max β.fvi (Finset.sup Finset.univ (λi => (G i).fvi - 1))

/-- Get the count of how often a free variable occurs in this region -/
@[simp]
def TRegion.fvc (x : ℕ) : TRegion φ → ℕ
  | let1 e t => e.fvc x + t.fvc (x + 1)
  | let2 e t => e.fvc x + t.fvc (x + 2)
  | cfg β _ G => β.fvc x + Finset.sum Finset.univ (λi => (G i).fvc (x + 1))

/-- Get the count of how often a free variable occurs in this region, or ∞ if it appears
 in a special position. -/
@[simp]
def TRegion.sfvc (x : ℕ) : TRegion φ → ℕ∞
  | let1 e t => e.fvc x + t.fvc (x + 1)
  | let2 e t => e.fvc x + t.fvc (x + 2)
  | cfg β _ G => β.sfvc x + Finset.sum Finset.univ (λi => (G i).sfvc (x + 1))

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
  | case e s t => e.fv + s.fv.liftFv + t.fv.liftFv
  | let1 e t => e.fv + t.fv.liftFv
  | let2 e t => e.fv + t.fv.liftnFv 2
  | cfg β _ f => β.fv + Finset.sum Finset.univ (λi => (f i).fv.liftnFv 1)

/-- The highest free variable in this region, plus one -/
@[simp]
def Region.fvi : Region φ → ℕ
  | br _ e => e.fvi
  | case e s t => Nat.max e.fvi (Nat.max (s.fvi - 1) (t.fvi - 1))
  | let1 e t => Nat.max e.fvi (t.fvi - 1)
  | let2 e t => Nat.max e.fvi (t.fvi - 2)
  | cfg β _ f => Nat.max β.fvi (Finset.sup Finset.univ (λi => (f i).fvi - 1))

theorem Region.fvi_br_le_iff {n : ℕ} {e : Term φ} : (br n e).fvi ≤ n ↔ e.fvi ≤ n := Iff.rfl

theorem Region.fvi_case_le_iff {e} {s t : Region φ} {n : ℕ}
  : (case e s t).fvi ≤ n ↔ e.fvi ≤ n ∧ s.fvi ≤ n + 1 ∧ t.fvi ≤ n + 1
  := by simp

theorem Region.fvi_case_le_disc {e} {s t : Region φ} {n : ℕ}
  : (case e s t).fvi ≤ n → e.fvi ≤ n
  := by rw [fvi_case_le_iff]; exact λ⟨he, _, _⟩ => he

theorem Region.fvi_case_le_left {e} {s t : Region φ} {n : ℕ}
  : (case e s t).fvi ≤ n → s.fvi ≤ n + 1
  := by rw [fvi_case_le_iff]; exact λ⟨_, hs, _⟩ => hs

theorem Region.fvi_case_le_right {e} {s t : Region φ} {n : ℕ}
  : (case e s t).fvi ≤ n → t.fvi ≤ n + 1
  := by rw [fvi_case_le_iff]; exact λ⟨_, _, ht⟩ => ht

theorem Region.fvi_let1_le_iff {e : Term φ} {t} {n : ℕ}
  : (let1 e t).fvi ≤ n ↔ e.fvi ≤ n ∧ t.fvi ≤ n + 1
  := by simp

theorem Region.fvi_let1_le_bind {e : Term φ} {t} {n : ℕ}
  : (let1 e t).fvi ≤ n → e.fvi ≤ n
  := by rw [fvi_let1_le_iff]; exact λ⟨he, _⟩ => he

theorem Region.fvi_let1_le_rest {e : Term φ} {t} {n : ℕ}
  : (let1 e t).fvi ≤ n → t.fvi ≤ n + 1
  := by rw [fvi_let1_le_iff]; exact λ⟨_, ht⟩ => ht

theorem Region.fvi_let2_le_iff {e : Term φ} {t} {n : ℕ}
  : (let2 e t).fvi ≤ n ↔ e.fvi ≤ n ∧ t.fvi ≤ n + 2
  := by simp

theorem Region.fvi_let2_le_bind {e : Term φ} {t} {n : ℕ}
  : (let2 e t).fvi ≤ n → e.fvi ≤ n
  := by rw [fvi_let2_le_iff]; exact λ⟨he, _⟩ => he

theorem Region.fvi_let2_le_rest {e : Term φ} {t} {n : ℕ}
  : (let2 e t).fvi ≤ n → t.fvi ≤ n + 2
  := by rw [fvi_let2_le_iff]; exact λ⟨_, ht⟩ => ht

theorem Region.fvi_cfg_le_iff {β : Region φ} {k : ℕ} {f : Fin k → Region φ}
  : (cfg β k f).fvi ≤ n ↔ β.fvi ≤ n ∧ ∀i, (f i).fvi ≤ n + 1
  := by simp

theorem Region.fvi_cfg_le_entry {β : Region φ} {n : ℕ} {f : Fin k → Region φ}
  : (cfg β k f).fvi ≤ n → β.fvi ≤ n
  := by rw [fvi_cfg_le_iff]; exact λ⟨hβ, _⟩ => hβ

theorem Region.fvi_cfg_le_blocks {β : Region φ} {n : ℕ} {f : Fin k → Region φ}
  : (cfg β k f).fvi ≤ n → ∀i, (f i).fvi ≤ n + 1
  := by rw [fvi_cfg_le_iff]; exact λ⟨_, hf⟩ i => hf i

/-- Get the count of how often a free variable occurs in this region -/
@[simp]
def Region.fvc (x : ℕ) : Region φ → ℕ
  | br _ e => e.fvc x
  | case e s t => e.fvc x + s.fvc (x + 1) + t.fvc (x + 1)
  | let1 e t => e.fvc x + t.fvc (x + 1)
  | let2 e t => e.fvc x + t.fvc (x + 2)
  | cfg β _ f => β.fvc x + Finset.sum Finset.univ (λi => (f i).fvc (x + 1))

/-- Get the count of how often a free variable occurs in this region, or ∞ if it appears
 in a special position. -/
@[simp]
def Region.sfvc (x : ℕ) : Region φ → ℕ∞
  | br _ e => if e.fvc x = 0 then 0 else ⊤
  | case e s t => if e.fvc x = 0 then 0 else ⊤ + s.fvc (x + 1) + t.fvc (x + 1)
  | let1 e t => e.fvc x + t.fvc (x + 1)
  | let2 e t => e.fvc x + t.fvc (x + 2)
  | cfg β _ f => β.fvc x + Finset.sum Finset.univ (λi => (f i).sfvc (x + 1))

theorem Region.fv_lwk (ρ : ℕ → ℕ) (r : Region φ) : (r.lwk ρ).fv = r.fv := by
  induction r generalizing ρ <;> simp [*]

/-- The free label variables in this region -/
@[simp]
def Region.fl : Region φ → Multiset ℕ
  | br n _ => {n}
  | case _ s t => s.fl + t.fl
  | let1 _ t => t.fl
  | let2 _ t => t.fl
  | cfg β n f => β.fl.liftnFv n + Finset.sum Finset.univ (λi => (f i).fl.liftnFv n)

theorem Region.fl_vwk (ρ : ℕ → ℕ) (r : Region φ) : (r.vwk ρ).fl = r.fl := by
  induction r generalizing ρ <;> simp [*]

theorem Region.fl_lwk (ρ : ℕ → ℕ) (r : Region φ) : (r.lwk ρ).fl = r.fl.map ρ := by
  induction r generalizing ρ <;> simp [Multiset.map_finsum, *]

/-- The free variables in this control-flow graph -/
@[simp]
def CFG.fv (cfg : CFG φ) : Multiset ℕ := Finset.sum Finset.univ (λi => (cfg.targets i).fv)

/-- The free label variables in this control-flow graph -/
@[simp]
def CFG.fl (cfg : CFG φ) : Multiset ℕ := Finset.sum Finset.univ (λi => (cfg.targets i).fl)

end Definitions

end BinSyntax

/-
TODO CORNER:
- Fill in rest of fvi, fli
- fv/fvi coerce, etc
-/
