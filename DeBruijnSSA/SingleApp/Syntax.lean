import Discretion

-- TODO: use abstract higher-ERT type formalism, add to discretion?

namespace SingleApp

/-- A simple term, consisting of variables, operations, pairs, units, and booleans -/
inductive Term (φ : Type) where
| var : ℕ → Term φ
| op : φ → Term φ → Term φ
| pair : Term φ → Term φ → Term φ
| unit : Term φ
| bool : Bool → Term φ

/-- Rename the variables in a `Term` using `ρ` -/
def Term.wk (ρ : ℕ → ℕ) : Term φ → Term φ
| var x => var (ρ x)
| op f x => op f (wk ρ x)
| pair x y => pair (wk ρ x) (wk ρ y)
| unit => unit
| bool b => bool b

@[simp]
theorem Term.wk_id (t : Term φ) : t.wk id = t := by induction t <;> simp [wk, *]

theorem Term.wk_id' : (t : Term φ) -> t.wk (λx => x) = t
  := Term.wk_id

theorem Term.wk_comp (σ : ℕ → ℕ) (ρ : ℕ → ℕ) (t : Term φ)
  : t.wk (ρ ∘ σ) = (t.wk σ).wk ρ := by induction t <;> simp [wk, *]

/-- A substitution mapping variables to terms -/
def Subst (φ : Type) := ℕ → Term φ

/-- The identity substitution, which simply maps variables to themselves -/
def Subst.id : Subst φ := Term.var

@[simp]
theorem Subst.id_apply (n : ℕ) : @Subst.id φ n = Term.var n := rfl

/-- Lift a substitution under a binder -/
def Subst.lift (σ : Subst φ) : Subst φ
| 0 => Term.var 0
| n + 1 => (σ n).wk Nat.succ

/-- Lift a substitution under `n` binders -/
def Subst.liftn (n : ℕ) (σ : Subst φ) : Subst φ
  := λm => if m < n then Term.var m else (σ (m - n)).wk (λv => v + n)

theorem Subst.liftn_zero (σ : Subst φ) : σ.liftn 0 = σ := by
  funext n
  simp only [liftn]
  split
  . rename_i H; cases H
  . exact (σ n).wk_id

theorem Subst.liftn_one (σ : Subst φ) : σ.liftn 1 = σ.lift := by funext m; cases m <;> rfl

theorem Subst.liftn_succ (n) (σ: Subst φ) : σ.liftn n.succ = (σ.liftn n).lift := by
  induction n with
  | zero => rw [σ.liftn_one, σ.liftn_zero]
  | succ n I => -- TODO: I'm sure this can be made _much_ cleaner...
    funext m
    rw [I]
    simp only [lift]
    split
    . rfl
    . simp only [liftn]
      split
      . split
        . rfl
        . split
          . rfl
          . rename_i H C; exact (C (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ H))).elim
      . split
        . rename_i H; simp_arith at H
        . split
          . rename_i C H; exact (C (Nat.succ_lt_succ (Nat.succ_lt_succ H))).elim
          . simp only [<-Term.wk_comp]
            apply congr
            apply congrArg
            funext v
            simp_arith
            simp_arith

theorem Subst.liftn_eq_iterate_lift_apply (n: ℕ) (σ: Subst φ) : σ.liftn n = (Subst.lift^[n] σ) := by
  induction n with
  | zero => exact σ.liftn_zero
  | succ n I => simp only [Function.iterate_succ_apply', Subst.liftn_succ, *]

theorem Subst.liftn_eq_iterate_lift (n: ℕ) : Subst.liftn n = (@Subst.lift φ)^[n] := by
  funext σ
  rw [liftn_eq_iterate_lift_apply]

theorem Subst.lift_id : (@id φ).lift = id := by funext n; cases n <;> rfl

theorem Subst.iterate_lift_id : (n: ℕ) -> Subst.lift^[n] (@id φ) = id
  | 0 => rfl
  | n + 1 => by simp [lift_id, iterate_lift_id n]

@[simp]
theorem Subst.liftn_id (n: ℕ): (@id φ).liftn n = id := by
  rw [liftn_eq_iterate_lift_apply, iterate_lift_id]


theorem Subst.liftn_add (n m: ℕ) : Subst.liftn (m + n) = (@Subst.liftn α m) ∘ (@Subst.liftn α n)
  := by simp [liftn_eq_iterate_lift, Function.iterate_add]

theorem Subst.liftn_add_apply (n m: ℕ) (σ: Subst α): (σ.liftn n).liftn m = σ.liftn (m + n)
  := by simp [liftn_add]

/-- Substitute the variables in a `Term` using `σ` -/
def Term.subst (σ : Subst φ) : Term φ → Term φ
| var x => σ x
| op f x => op f (subst σ x)
| pair x y => pair (subst σ x) (subst σ y)
| unit => unit
| bool b => bool b

@[simp]
theorem Term.subst_id (t : Term φ) : t.subst Subst.id = t
  := by induction t <;> simp [subst, *]

/-- Create a substitution from a variable renaming -/
def Subst.fromWk (ρ : ℕ -> ℕ): Subst φ := Term.var ∘ ρ

@[simp]
theorem Subst.fromWk_apply (ρ : ℕ -> ℕ) (n : ℕ) : (@fromWk φ ρ) n = Term.var (ρ n) := rfl

theorem Subst.fromWk_lift (ρ) : (@fromWk φ ρ).lift = fromWk (Nat.liftWk ρ) := by
  funext n; cases n <;> rfl

theorem Subst.fromWk_iterate_lift
  : (n : ℕ) -> ∀ρ, Subst.lift^[n] (@fromWk φ ρ) = fromWk (Nat.liftWk^[n] ρ)
  | 0, ρ => rfl
  | n + 1, ρ => by simp [fromWk_lift, fromWk_iterate_lift n]

theorem Subst.fromWk_liftn (n ρ) : (@fromWk φ ρ).liftn n = fromWk (Nat.liftnWk n ρ) := by
  rw [liftn_eq_iterate_lift, Nat.liftnWk_eq_iterate_liftWk, fromWk_iterate_lift]

theorem Term.subst_wk (ρ : ℕ -> ℕ) (t : Term φ) : t.subst (Subst.fromWk ρ) = t.wk ρ := by
  induction t <;> simp [Term.subst, Term.wk, Subst.fromWk_liftn, *]

theorem Term.subst_liftn (n : ℕ) (σ : Subst α) (t : Term α)
    : (t.wk (Nat.liftnWk n Nat.succ)).subst (σ.liftn (n + 1))
      = (t.subst (σ.liftn n)).wk (Nat.liftnWk n Nat.succ)
  := by induction t with
  | var =>
    --TODO: how should this be factored?
    simp only [wk, subst, Nat.liftnWk, Subst.liftn]
    split
    . split
      . simp [wk, Nat.liftnWk, *]
      . rename_i H C; exact (C (Nat.le_step H)).elim
    . rename_i C
      simp_arith only [ite_false, <-wk_comp]
      apply congr
      . apply congrArg
        funext v
        simp_arith [Function.comp_apply, Zero.zero, Nat.liftnWk]
      . simp [Nat.succ_add, Nat.succ_sub_succ, Nat.add_sub_assoc]
  | _ => simp [subst, wk, *]

theorem Term.subst_iterate_lift (n : ℕ) (σ : Subst α) (t : Term α)
  : (t.wk (Nat.liftWk^[n] Nat.succ)).subst (Subst.lift^[n + 1] σ)
    = (t.subst (Subst.lift^[n] σ)).wk (Nat.liftWk^[n] Nat.succ)
  := by simp only [<-Subst.liftn_eq_iterate_lift, <-Nat.liftnWk_eq_iterate_liftWk, subst_liftn]

theorem Term.subst_lift (t : Term α) (σ : Subst α)
  : (t.wk Nat.succ).subst (σ.lift) = (t.subst σ).wk Nat.succ := t.subst_iterate_lift 0 σ

/-- Compose two substitutions on terms to yield another -/
def Subst.comp (σ τ : Subst α): Subst α
  | n => (τ n).subst σ

theorem Subst.lift_comp (σ τ : Subst α) : (σ.comp τ).lift = σ.lift.comp τ.lift := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [lift, comp, Term.subst_lift]

theorem Subst.iterate_lift_comp
  : (n : ℕ) -> ∀σ τ : Subst α, Subst.lift^[n] (σ.comp τ)
    = (Subst.lift^[n] σ).comp (Subst.lift^[n] τ)
  | 0, σ, τ => rfl
  | n + 1, σ, τ => by simp [Subst.lift_comp, iterate_lift_comp n]

theorem Subst.liftn_comp (n : ℕ) (σ τ : Subst α)
  : (σ.comp τ).liftn n = (σ.liftn n).comp (τ.liftn n)
  := by rw [liftn_eq_iterate_lift, iterate_lift_comp]

theorem Term.subst_comp (σ τ : Subst α) (t : Term α) : t.subst (σ.comp τ) = (t.subst τ).subst σ
  := by induction t <;> simp only [subst, Subst.liftn_comp, Subst.comp, *]

/-- Substitute a term for the smallest variable, bumping the rest downwards -/
def Term.subst0 (t : Term α) : Subst α
  | 0 => t
  | n + 1 => var n

/-- Substitute a term for the smallest variable, leaving the rest unchanged -/
def Term.alpha0 (t : Term α) : Subst α
  | 0 => t
  | n => var n

/-- A terminator -/
inductive Terminator (φ : Type) : Type
| br : Nat → Term φ → Terminator φ
| ite : Term φ → Terminator φ → Terminator φ → Terminator φ

/-- A basic block body -/
inductive Body (φ : Type) : Type
| let1 : Term φ → Term φ → Body φ
| let2 : Term φ → Term φ → Body φ

/-- A basic-block -/
structure Block (φ : Type) : Type where
  body : Body φ
  terminator : Terminator φ

/-- A basic block-based single-entry multiple-exit region -/
inductive BBRegion (φ : Type) : Type
| cfg (β : Block φ) (n : Nat) : (Fin n → BBRegion φ) → BBRegion φ

/-- A terminator-based single-entry multiple-exit region -/
inductive TRegion (φ : Type) : Type
| let1 : Term φ → TRegion φ → TRegion φ
| let2 : Term φ → TRegion φ → TRegion φ
| cfg (β : Terminator φ) (n : Nat) : (Fin n → TRegion φ) → TRegion φ

/-- A single-entry multiple-exit region -/
inductive Region (φ : Type) : Type
| br : Nat → Term φ → Region φ
| ite : Term φ → Region φ → Region φ → Region φ
| let1 : Term φ → Region φ → Region φ
| let2 : Term φ → Region φ → Region φ
| cfg (β : Region φ) (n : Nat) : (Fin n → Region φ) → Region φ

/-- Rename the variables in a `Region` using `ρ` -/
def Region.vwk (ρ : ℕ → ℕ) : Region φ → Region φ
| br n e => br n (e.wk ρ)
| ite e s t => ite (e.wk ρ) (vwk ρ s) (vwk ρ t)
| let1 e t => let1 (e.wk ρ) (vwk (Nat.liftWk ρ) t)
| let2 e t => let2 (e.wk ρ) (vwk (Nat.liftnWk 2 ρ) t)
| cfg β n f => cfg (vwk ρ β) n (λ i => (f i).vwk ρ)

@[simp]
theorem Region.vwk_id (r : Region φ) : r.vwk id = r := by
  induction r <;> simp [Region.vwk, Nat.liftnWk_id, *]

theorem Region.vwk_comp (σ τ : ℕ → ℕ) (r : Region φ)
  : r.vwk (σ ∘ τ) = (r.vwk τ).vwk σ := by
  induction r generalizing σ τ
  <;> simp [vwk, Term.wk_comp, Nat.liftWk_comp, Nat.liftnWk_comp, *]

/-- Substitute the variables in a `Region` using `σ` -/
def Region.vsubst (σ : Subst φ) : Region φ → Region φ
| br n e => br n (e.subst σ)
| ite e s t => ite (e.subst σ) (vsubst σ s) (vsubst σ t)
| let1 e t => let1 (e.subst σ) (vsubst σ.lift t)
| let2 e t => let2 (e.subst σ) (vsubst (σ.liftn 2) t)
| cfg β n f => cfg (vsubst σ β) n (λ i => (f i).vsubst σ)

@[simp]
theorem Region.vsubst_id (r : Region φ) : r.vsubst Subst.id = r := by
  induction r <;> simp [Region.vsubst, Subst.lift_id, Subst.liftn_id, *]

theorem Region.vsubst_comp (σ τ : Subst φ) (r : Region φ)
  : r.vsubst (σ.comp τ) = (r.vsubst τ).vsubst σ := by
  induction r generalizing σ τ
  <;> simp [vsubst, Term.subst_comp, Subst.lift_comp, Subst.liftn_comp, *]

/-- Rename the labels in a `Region` using `ρ` -/
def Region.lwk (ρ : ℕ → ℕ) : Region φ → Region φ
| br n e => br (ρ n) e
| ite e s t => ite e (lwk ρ s) (lwk ρ t)
| let1 e t => let1 e (lwk ρ t)
| let2 e t => let2 e (lwk ρ t)
| cfg β n f => cfg (lwk ρ β) n (λ i => (f i).lwk (Nat.liftnWk n ρ))

@[simp]
theorem Region.lwk_id (r : Region φ) : r.lwk id = r := by
  induction r <;> simp [Region.lwk, Nat.liftnWk_id, *]

theorem Region.lwk_comp (σ τ : ℕ → ℕ) (r : Region φ)
  : r.lwk (σ ∘ τ) = (r.lwk τ).lwk σ := by
  induction r generalizing σ τ <;> simp [lwk, Nat.liftnWk_comp, *]

-- TODO: label-substitution

/-- A control-flow graph with `length` entry-point regions -/
structure CFG (φ : Type) : Type where
  /-- The number of entry points to this CFG -/
  length : Nat
  /-- The number of exits for this CFG -/
  targets : Fin length → Region φ

/-- Rename the variables in a `CFG` using `ρ` -/
def CFG.vwk (ρ : ℕ → ℕ) (G : CFG φ) : CFG φ where
  length := G.length
  targets := λ i => (G.targets i).vwk ρ

@[simp]
theorem CFG.vwk_id (G : CFG φ) : G.vwk id = G := by cases G; simp [vwk]

/-- Substitute the variables in a `CFG` using `σ` -/
def CFG.vsubst (σ : Subst φ) (G : CFG φ) : CFG φ where
  length := G.length
  targets := λ i => (G.targets i).vsubst σ

@[simp]
theorem CFG.vsubst_id (G : CFG φ) : G.vsubst Subst.id = G := by cases G; simp [vsubst]

/-- Rename the labels in a `CFG` using `ρ` -/
def CFG.lwk (ρ : ℕ → ℕ) (G : CFG φ) : CFG φ where
  length := G.length
  targets := λ i => (G.targets i).lwk ρ

@[simp]
theorem CFG.lwk_id (G : CFG φ) : G.lwk id = G := by cases G; simp [lwk]

/-- A single-entry multiple-exit region, applying a substitution on jumps -/
inductive SRegion (φ : Type) : Type
| br : Nat → Subst φ → SRegion φ
| ite : Term φ → SRegion φ → SRegion φ → SRegion φ
| let1 : Term φ → SRegion φ → SRegion φ
| let2 : Term φ → SRegion φ → SRegion φ
| cfg (β : SRegion φ) (n : Nat) : (Fin n → SRegion φ) → SRegion φ

/-- A control-flow graph with `length` entry-point regions -/
structure SCFG (φ : Type) : Type where
  /-- The number of entry points to this CFG -/
  length : Nat
  /-- The number of exits for this CFG -/
  targets : Fin length → SRegion φ

end SingleApp
