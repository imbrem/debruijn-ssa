import Discretion.Wk.Nat
import Discretion.Wk.Fin

namespace BinSyntax

/-! ### Basic syntax definitions

Free variables and simple coercions are given immediately after each definition to give an idea of how
the de-Bruijn indices are supposed to be interpreted.
 -/
section Definitions

/-- A simple term, consisting of variables, operations, pairs, units, and booleans -/
inductive FTerm (φ : Type _) (vars : ℕ) : Type _
  | var : Fin vars → FTerm φ vars
  | op : φ → FTerm φ vars → FTerm φ vars
  | pair : FTerm φ vars → FTerm φ vars → FTerm φ vars
  | unit : FTerm φ vars
  | inl : FTerm φ vars → FTerm φ vars
  | inr : FTerm φ vars → FTerm φ vars
  | abort : FTerm φ vars → FTerm φ vars

/-- Rename the variables in a `Term` using `ρ` -/
@[simp]
def FTerm.wk (ρ : Fin varsIn → Fin varsOut) : FTerm φ varsIn → FTerm φ varsOut
  | var x => var (ρ x)
  | op f e => op f (wk ρ e)
  | pair l r => pair (wk ρ l) (wk ρ r)
  | unit => unit
  | inl a => inl (wk ρ a)
  | inr a => inr (wk ρ a)
  | abort a => abort (wk ρ a)

/-- A single-entry multiple-exit region, similar to [A-normal
  form](https://en.wikipedia.org/wiki/A-normal_form) -/
inductive FRegion (φ : Type _) : ℕ → ℕ → Type _
  | br : Fin labels → FTerm φ vars → FRegion φ labels vars
  | case : FTerm φ vars →
    FRegion φ labels (vars + 1) →
    FRegion φ labels (vars + 1) →
    FRegion φ labels vars
  | let1 : FTerm φ vars → FRegion φ labels (vars + 1) → FRegion φ labels vars
  | let2 : FTerm φ vars → FRegion φ labels (vars + 2) → FRegion φ labels vars
  | cfg (cfgLabels : Nat) (β : FRegion φ (labels + cfgLabels) vars) :
    (Fin cfgLabels → FRegion φ (labels + cfgLabels) (vars + 1)) → FRegion φ labels vars

-- Why is recursion failing here???

-- /-- Rename the variables in a `Region` using `ρ` -/
-- @[simp]
-- def FRegion.vwk (ρ : Fin varsIn → Fin varsOut) : FRegion φ labels varsIn → FRegion φ labels varsOut
--   | br n e => br n (e.wk ρ)
--   | case e s t => case (e.wk ρ) (vwk (Fin.liftWk ρ) s) (vwk (Fin.liftWk ρ) t)
--   | let1 e t => let1 (e.wk ρ) (vwk (Fin.liftWk ρ) t)
--   | let2 e t => let2 (e.wk ρ) (vwk (Fin.liftnWk 2 ρ) t)
--   | cfg n β G => cfg n (β.vwk ρ) (λi => (G i).vwk (Fin.liftWk ρ))
