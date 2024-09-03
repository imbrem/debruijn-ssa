import Discretion.Wk.Nat
import Discretion.Wk.Fin
import Discretion.Wk.Multiset
import Discretion.Wk.Set
import Mathlib.Data.ENat.Basic

import DeBruijnSSA.BinSyntax.Syntax.Definitions
import Discretion.Utils.Set

namespace BinSyntax

-- TODO: loop-aware fv...

/-! ### Free variables and labels

Definitions and lemmas about free variables and free labels
 -/
section Definitions

/-- Get the set of free variables of a term as a multiset (to allow counting occurences) -/
@[simp]
def Term.fv : Term φ → Multiset ℕ
  | var x => {x}
  | op _ x => x.fv
  | let1 a e => a.fv + e.fv.liftFv
  | pair x y => x.fv + y.fv
  | let2 a e => a.fv + e.fv.liftnFv 2
  | inl a => a.fv
  | inr a => a.fv
  | case a l r => a.fv + l.fv.liftFv + r.fv.liftFv
  | abort a => a.fv
  | _ => 0

theorem Term.fv_wk (ρ : ℕ → ℕ) (t : Term φ) : (t.wk ρ).fv = t.fv.map ρ := by
  induction t generalizing ρ <;> simp [*]

/-- Get the set of free variables of a term -/
@[simp]
def Term.fvs : Term φ → Set ℕ
  | var x => {x}
  | op _ x => x.fvs
  | let1 a e => a.fvs ∪ e.fvs.liftFv
  | pair x y => x.fvs ∪ y.fvs
  | let2 a e => a.fvs ∪ e.fvs.liftnFv 2
  | inl a => a.fvs
  | inr a => a.fvs
  | case a l r => a.fvs ∪ l.fvs.liftFv ∪ r.fvs.liftFv
  | abort a => a.fvs
  | _ => ∅

theorem Term.fvs_wk (ρ : ℕ → ℕ) (t : Term φ) : (t.wk ρ).fvs = ρ '' t.fvs := by
  induction t generalizing ρ <;> simp [Set.image_union, *]

theorem Term.fvs_wk1 (r : Term φ) : r.wk1.fvs = Nat.liftWk Nat.succ '' r.fvs := by
  simp [wk1, fvs_wk]

theorem Term.wk_eqOn_fvs (t : Term φ) {ρ ρ' : ℕ → ℕ} (h : t.fvs.EqOn ρ ρ')
  : t.wk ρ = t.wk ρ' := by
  induction t generalizing ρ ρ' with
  | var x => simp [h rfl]
  | pair l r Il Ir => simp [Il (λi hi => @h i (by simp [hi])), Ir (λi hi => @h i (by simp [hi]))]
  | op _ a Ia | inl a Ia | inr a Ia | abort a Ia => simp [Ia h]
  | let1 _ _ Ia Ib =>
    simp only [wk]
    rw [Ia (λi hi => @h i (by simp [hi])), Ib]
    intro i hi
    simp only [Nat.liftWk]
    split
    · rfl
    · simp [@h _, Set.mem_liftFv, hi]
  | let2 _ _ Ia Ib =>
    simp only [wk]
    rw [Ia (λi hi => @h i (by simp [hi])), Ib]
    intro i hi
    simp only [Nat.liftnWk]
    split
    case isTrue => rfl
    case isFalse h' => simp [@h _, Set.mem_liftnFv, Nat.ge_of_not_lt h', hi]
  | case _ _ _ Id Il Ir =>
    simp only [wk]
    rw [Id (λi hi => @h i (by simp [hi])), Il, Ir] <;>
    intro i hi <;>
    simp only [Nat.liftWk] <;>
    split <;>
    simp [@h _, Set.mem_liftFv, hi]
  | _ => rfl

/-- Get the index of the highest free variable in this term, plus one -/
@[simp]
def Term.fvi : Term φ → ℕ
  | var x => x + 1
  | op _ x => x.fvi
  | let1 a e => Nat.max a.fvi (e.fvi - 1)
  | pair x y => Nat.max x.fvi y.fvi
  | let2 a e => Nat.max a.fvi (e.fvi - 2)
  | inl a => a.fvi
  | inr a => a.fvi
  | case a l r => Nat.max a.fvi (Nat.max (l.fvi - 1) (r.fvi - 1))
  | abort a => a.fvi
  | _ => 0

theorem Term.fvi_var_le_iff {x n : ℕ} : (@var φ x).fvi ≤ n ↔ x < n := by simp [Nat.succ_le_iff]

theorem Term.fvi_op_le_iff {o : φ} {t : Term φ} {n} : (op o t).fvi ≤ n ↔ t.fvi ≤ n := Iff.rfl

theorem Term.fvi_let1_le_iff {a e : Term φ} {n} : (let1 a e).fvi ≤ n ↔ a.fvi ≤ n ∧ e.fvi ≤ n + 1
  := by simp

theorem Term.fvi_pair_le_iff {l r : Term φ} {n} : (pair l r).fvi ≤ n ↔ l.fvi ≤ n ∧ r.fvi ≤ n
  := by simp

theorem Term.fvi_let2_le_iff {a e : Term φ} {n} : (let2 a e).fvi ≤ n ↔ a.fvi ≤ n ∧ e.fvi ≤ n + 2
  := by simp

@[simp]
theorem Term.fvi_unit_le {n} : (unit : Term φ).fvi ≤ n := by simp

theorem Term.fvi_pair_le_left {l r : Term φ} {n} : (pair l r).fvi ≤ n → l.fvi ≤ n
  := by simp only [fvi, max_le_iff, and_imp]; exact λl _ => l

theorem Term.fvi_pair_le_right {l r : Term φ} {n} : (pair l r).fvi ≤ n → r.fvi ≤ n
  := by simp only [fvi, max_le_iff, and_imp]; exact λ_ r => r

theorem Term.fvi_inl_le_iff {t : Term φ} {n : ℕ} : t.inl.fvi ≤ n ↔ t.fvi ≤ n := Iff.rfl

theorem Term.fvi_inr_le_iff {t : Term φ} {n : ℕ} : t.inr.fvi ≤ n ↔ t.fvi ≤ n := Iff.rfl

theorem Term.fvi_case_le_iff {t : Term φ} {l r : Term φ} {n : ℕ}
  : (t.case l r).fvi ≤ n ↔ t.fvi ≤ n ∧ l.fvi ≤ n + 1 ∧ r.fvi ≤ n + 1
  := by simp

theorem Term.fvi_abort_le_iff {t : Term φ} {n : ℕ} : t.abort.fvi ≤ n ↔ t.fvi ≤ n := Iff.rfl

theorem Term.le_fvi_var_iff {x n : ℕ} : n ≤ (@var φ x).fvi ↔ n ≤ x + 1 := by simp

theorem Term.le_fvi_op_iff {o : φ} {t : Term φ} {n} : n ≤ (op o t).fvi ↔ n ≤ t.fvi := Iff.rfl

theorem Term.le_fvi_let1_iff {a e : Term φ} {n} : n ≤ (let1 a e).fvi ↔ n ≤ a.fvi ∨ n ≤ e.fvi - 1
  := by simp

theorem Term.le_fvi_pair_iff {l r : Term φ} {n} : n ≤ (pair l r).fvi ↔ n ≤ l.fvi ∨ n ≤ r.fvi
  := by simp

theorem Term.le_fvi_let2_iff {a e : Term φ} {n} : n ≤ (let2 a e).fvi ↔ n ≤ a.fvi ∨ n ≤ e.fvi - 2
  := by simp

theorem Term.le_fvi_inl_iff {t : Term φ} {n : ℕ} : n ≤ t.inl.fvi ↔ n ≤ t.fvi := Iff.rfl

theorem Term.le_fvi_inr_iff {t : Term φ} {n : ℕ} : n ≤ t.inr.fvi ↔ n ≤ t.fvi := Iff.rfl

theorem Term.le_fvi_case_iff {t : Term φ} {l r : Term φ} {n : ℕ}
  : n ≤ (t.case l r).fvi ↔ n ≤ t.fvi ∨ n ≤ l.fvi - 1 ∨ n ≤ r.fvi - 1
  := by simp

theorem Term.le_fvi_abort_iff {t : Term φ} {n : ℕ} : n ≤ t.abort.fvi ↔ n ≤ t.fvi := Iff.rfl

theorem Term.le_fvi_unit_iff {n : ℕ} : n ≤ (unit : Term φ).fvi ↔ n = 0 := by simp

theorem Term.fvs_fvi {t : Term φ} : t.fvs ⊆ Set.Iio t.fvi := by
  induction t with
  | let1 =>
    simp only [fvs, fvi, Set.Iio_max]
    apply Set.union_subset_union
    assumption
    apply Set.liftFv_subset_Iio_of_subset_Iio
    assumption
  | pair =>
    simp only [fvs, fvi, Set.Iio_max]
    apply Set.union_subset_union <;> assumption
  | let2 =>
    simp only [fvs, fvi, Set.Iio_max]
    apply Set.union_subset_union
    assumption
    apply Set.liftnFv_subset_Iio_of_subset_Iio
    assumption
  | case =>
    simp only [fvs, fvi, Set.Iio_max, Set.union_assoc]
    apply Set.union_subset_union
    assumption
    apply Set.union_subset_union <;>
    apply Set.liftFv_subset_Iio_of_subset_Iio <;>
    assumption
  | _ => simp [*]

theorem Term.wk_eqOn_fvi {t : Term φ} (h : (Set.Iio t.fvi).EqOn ρ ρ')
  : t.wk ρ = t.wk ρ' := t.wk_eqOn_fvs (h.mono t.fvs_fvi)

theorem Term.fvs_empty_of_fvi_zero {t : Term φ} (h : t.fvi = 0) : t.fvs = ∅ := by
  apply Set.eq_empty_of_subset_empty
  convert h ▸ t.fvs_fvi
  ext k; simp

-- theorem Term.fvi_zero_of_fvs_empty {t : Term φ} (h : t.fvs = ∅) : t.fvi = 0 := by
--   sorry

-- theorem Term.fvi_zero_iff_fvs_empty (t : Term φ) : t.fvi = 0 ↔ t.fvs = ∅
--   := ⟨Term.fvs_empty_of_fvi_zero, Term.fvi_zero_of_fvs_empty⟩

-- theorem Term.fvi_zero_iff_fv_zero (t : Term φ) : t.fvi = 0 ↔ t.fv = 0 := by
--   stop induction t generalizing ρ <;> simp [*]

/-- Get the count of how often a free variable occurs in this term -/
@[simp]
def Term.fvc (x : ℕ) : Term φ → ℕ
  | var y => if x = y then 1 else 0
  | op _ y => y.fvc x
  | pair y z => y.fvc x + z.fvc x
  | inl y => y.fvc x
  | inr y => y.fvc x
  | abort y => y.fvc x
  | _ => 0

-- theorem Term.fvc_eq_fv_count (x : ℕ) (t : Term φ) : t.fvc x = t.fv.count x := by
--   induction t generalizing x with
--   | var y => simp [Multiset.count_singleton]
--   | _ => stop simp [*]

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

-- theorem Body.fvc_eq_fv_count (x : ℕ) (b : Body φ) : b.fvc x = b.fv.count x := by
--   induction b generalizing x <;>
--   simp [Term.fvc_eq_fv_count, Multiset.count_liftnFv, Multiset.count_liftFv, *]

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

-- theorem Terminator.fvc_eq_fv_count (x : ℕ) (r : Terminator φ) : r.fvc x = r.fv.count x := by
--   induction r generalizing x <;> simp [Term.fvc_eq_fv_count, Multiset.count_liftFv, *]

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
  | cfg β _ f => β.fv + Finset.sum Finset.univ (λi => (f i).fv.liftFv)

theorem Region.fv_vwk (ρ : ℕ → ℕ) (r : Region φ) : (r.vwk ρ).fv = r.fv.map ρ := by
  induction r generalizing ρ <;> simp [Multiset.map_finsum, Term.fv_wk, *]

/-- The free variables in this region -/
@[simp]
def Region.fvs : Region φ → Set ℕ
  | br _ e => e.fvs
  | case e s t => e.fvs ∪ s.fvs.liftFv ∪ t.fvs.liftFv
  | let1 e t => e.fvs ∪ t.fvs.liftFv
  | let2 e t => e.fvs ∪ t.fvs.liftnFv 2
  | cfg β _ f => β.fvs ∪ Set.iUnion (λi => (f i).fvs.liftFv)

theorem Region.fvs_vwk (ρ : ℕ → ℕ) (r : Region φ) : (r.vwk ρ).fvs = ρ '' r.fvs := by
  induction r generalizing ρ <;> simp [Set.image_union, Set.image_iUnion, Term.fvs_wk, *]

theorem Region.fvs_vwk1 (r : Region φ) : r.vwk1.fvs = Nat.liftWk Nat.succ '' r.fvs := by
  simp [vwk1, fvs_vwk]

@[simp]
theorem Region.fvs_lwk (ρ : ℕ → ℕ) (r : Region φ) : (r.lwk ρ).fvs = r.fvs := by
  induction r generalizing ρ <;> simp [*]

-- theorem Region.vwk_eqOn_fvs (r : Region φ) {ρ ρ' : ℕ → ℕ} (h : r.fvs.EqOn ρ ρ')
--   : r.vwk ρ = r.vwk ρ' := by
--   induction r generalizing ρ ρ' with
--   | br n e => simp [e.wk_eqOn_fvs h]
--   | case e s t Is It =>
--     simp only [vwk, e.wk_eqOn_fvs (λi hi => @h i (by simp [hi]))]
--     rw [Is, It]
--     sorry
--     sorry
--   | let1 e t It =>
--     simp only [vwk, e.wk_eqOn_fvs (λi hi => @h i (by simp [hi]))]
--     rw [It]
--     sorry
--   | let2 e t It =>
--     simp only [vwk, e.wk_eqOn_fvs (λi hi => @h i (by simp [hi]))]
--     rw [It]
--     sorry
--   | cfg β n G Iβ IG =>
--     simp only [vwk]
--     congr 1
--     exact Iβ sorry
--     funext i
--     apply IG
--     sorry

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

theorem Region.fvs_fvi {r : Region φ} : r.fvs ⊆ Set.Iio r.fvi := by
  induction r with
  | br _ e => simp [Term.fvs_fvi]
  | case e s t =>
    simp only [fvs, fvi, Set.Iio_max, Set.union_assoc]
    apply Set.union_subset_union
    apply Term.fvs_fvi
    apply Set.union_subset_union <;>
    apply Set.liftFv_subset_Iio_of_subset_Iio <;>
    assumption
  | let1 e t =>
    simp only [fvs, fvi, Set.Iio_max]
    apply Set.union_subset_union
    apply Term.fvs_fvi
    apply Set.liftFv_subset_Iio_of_subset_Iio
    assumption
  | let2 e t =>
    simp only [fvs, fvi, Set.Iio_max]
    apply Set.union_subset_union
    apply Term.fvs_fvi
    apply Set.liftnFv_subset_Iio_of_subset_Iio
    assumption
  | cfg β _ f Iβ I =>
    simp only [fvs, fvi, Set.Iio_max, Set.Iio_finset_univ_sup]
    apply Set.union_subset_union Iβ
    exact Set.iUnion_mono λi => Set.liftnFv_subset_Iio_of_subset_Iio (I i)

-- theorem Region.vwk_eqOn_fvi {r : Region φ} (h : (Set.Iio r.fvi).EqOn ρ ρ')
--   : r.vwk ρ = r.vwk ρ' := r.vwk_eqOn_fvs (h.mono r.fvs_fvi)

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

/-- The free label variables in this region -/
@[simp]
def Region.fls : Region φ → Set ℕ
  | br n _ => {n}
  | case _ s t => s.fls ∪ t.fls
  | let1 _ t => t.fls
  | let2 _ t => t.fls
  | cfg β n f => β.fls.liftnFv n ∪ Set.iUnion (λi => (f i).fls.liftnFv n)

theorem Region.fls_vwk (ρ : ℕ → ℕ) (r : Region φ) : (r.vwk ρ).fls = r.fls := by
  induction r generalizing ρ <;> simp [Set.image_union, Set.image_iUnion, *]

theorem Region.fls_lwk (ρ : ℕ → ℕ) (r : Region φ) : (r.lwk ρ).fls = ρ '' r.fls := by
  induction r generalizing ρ <;> simp [Set.image_union, Set.image_iUnion, *]

theorem Region.lwk_eqOn_fls (r : Region φ) (ρ ρ' : ℕ → ℕ) (h : r.fls.EqOn ρ ρ')
  : r.lwk ρ = r.lwk ρ' := by
  induction r generalizing ρ ρ' with
  | br ℓ e => simp [@h ℓ]
  | case e s t Is It => simp [lwk,
    Is ρ ρ' (λi hi => @h i (by simp [hi])),
    It ρ ρ' (λi hi => @h i (by simp [hi]))]
  | let1 e t It | let2 e t It => simp [lwk, It ρ ρ' h]
  | cfg β n G Iβ IG =>
    simp only [lwk]
    congr 1
    apply Iβ _ _ _
    rw [Nat.liftnWk_eqOn_iff]
    apply h.mono
    simp [fls]
    funext i
    apply IG
    rw [Nat.liftnWk_eqOn_iff]
    apply h.mono
    apply Set.subset_union_of_subset_right
    apply Set.subset_iUnion_of_subset
    rfl

-- theorem Region.fls_fli {r : Region φ} : r.fls ⊆ Set.Iio r.fli := by sorry

end Definitions

end BinSyntax

/-
TODO CORNER:
- Fill in rest of fvi, fli
- fv/fvi coerce, etc
-/
