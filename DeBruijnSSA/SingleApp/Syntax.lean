import Discretion
import Discretion.Wk.Multiset
import Mathlib.Algebra.BigOperators.Basic

-- TODO: use abstract higher-ERT type formalism, add to discretion?

-- TODO: splat file?

namespace SingleApp

/-- A simple term, consisting of variables, operations, pairs, units, and booleans -/
inductive Term (φ : Type) where
  | var : ℕ → Term φ
  | op : φ → Term φ → Term φ
  | pair : Term φ → Term φ → Term φ
  | unit : Term φ
  | bool : Bool → Term φ

/-- Get the set of free variables of a term as a multiset (to allow counting occurences) -/
@[simp]
def Term.fv : Term φ → Multiset ℕ
  | var x => {x}
  | op _ x => x.fv
  | pair x y => x.fv + y.fv
  | _ => 0

/-- Get the index of the highest free variable in this term, plus one -/
@[simp]
def Term.fvi : Term φ → ℕ
  | var x => x + 1
  | op _ x => x.fvi
  | pair x y => Nat.max x.fvi y.fvi
  | _ => 0

theorem Term.fvi_zero_iff_fv_zero (t : Term φ) : t.fvi = 0 ↔ t.fv = 0 := by
  induction t <;> simp [*]

/-- Rename the variables in a `Term` using `ρ` -/
@[simp]
def Term.wk (ρ : ℕ → ℕ) : Term φ → Term φ
  | var x => var (ρ x)
  | op f x => op f (wk ρ x)
  | pair x y => pair (wk ρ x) (wk ρ y)
  | unit => unit
  | bool b => bool b

@[simp]
theorem Term.wk_id (t : Term φ) : t.wk id = t := by induction t <;> simp [*]

theorem Term.wk_id' : (t : Term φ) -> t.wk (λx => x) = t
  := Term.wk_id

theorem Term.wk_comp (σ : ℕ → ℕ) (ρ : ℕ → ℕ) (t : Term φ)
  : t.wk (ρ ∘ σ) = (t.wk σ).wk ρ := by induction t <;> simp [*]

theorem Term.fv_wk (ρ : ℕ → ℕ) (t : Term φ) : (t.wk ρ).fv = t.fv.map ρ := by
  induction t <;> simp [*]

/-- A substitution mapping variables to terms -/
def Subst (φ : Type) := ℕ → Term φ -- TODO: Term.Subst?

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

@[simp]
theorem Subst.lift_id : (@id φ).lift = id := by funext n; cases n <;> rfl

@[simp]
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

theorem Subst.lift_succ (σ : Subst φ) (i : ℕ) : σ.lift (i + 1) = (σ i).wk Nat.succ := rfl

/-- Substitute the variables in a `Term` using `σ` -/
@[simp]
def Term.subst (σ : Subst φ) : Term φ → Term φ
| var x => σ x
| op f x => op f (subst σ x)
| pair x y => pair (subst σ x) (subst σ y)
| unit => unit
| bool b => bool b

@[simp]
theorem Term.subst_id (t : Term φ) : t.subst Subst.id = t := by induction t <;> simp [*]

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
  induction t <;> simp [Subst.fromWk_liftn, *]

theorem Term.subst_liftn (n : ℕ) (σ : Subst α) (t : Term α)
    : (t.wk (Nat.liftnWk n Nat.succ)).subst (σ.liftn (n + 1))
      = (t.subst (σ.liftn n)).wk (Nat.liftnWk n Nat.succ)
  := by induction t with
  | var =>
    --TODO: how should this be factored?
    simp only [wk, subst, Nat.liftnWk, Subst.liftn]
    split
    . split
      . simp [Nat.liftnWk, *]
      . rename_i H C; exact (C (Nat.le_step H)).elim
    . rename_i C
      simp_arith only [ite_false, <-wk_comp]
      apply congr
      . apply congrArg
        funext v
        simp_arith [Function.comp_apply, Zero.zero, Nat.liftnWk]
      . simp [Nat.succ_add, Nat.succ_sub_succ, Nat.add_sub_assoc]
  | _ => simp [*]

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

@[simp]
theorem Subst.comp_id (σ : Subst α) : σ.comp Subst.id = σ := by funext n; rfl

@[simp]
theorem Subst.id_comp (σ : Subst α) : Subst.id.comp σ = σ := by funext n; simp [comp]

theorem Subst.comp_assoc (σ τ ρ : Subst α) : (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) := by
  funext n
  simp only [comp, Function.comp_apply, Term.subst_comp]

/-- Substitute a term for the smallest variable, bumping the rest downwards -/
@[simp]
def Term.subst0 (t : Term α) : Subst α
  | 0 => t
  | n + 1 => var n

@[simp]
theorem Term.wk_succ_comp_subst0 (e : Term α) : e.subst0.comp (Subst.fromWk Nat.succ) = Subst.id
  := by funext n; cases n <;> rfl

@[simp]
theorem Term.wk_succ_subst_subst0 (e s : Term α) : (e.wk Nat.succ).subst s.subst0 = e := by
  rw [<-subst_wk, <-subst_comp, wk_succ_comp_subst0, subst_id]

/-- Substitute a term for the smallest variable, leaving the rest unchanged -/
def Term.alpha0 (t : Term α) : Subst α
  | 0 => t
  | n => var n

@[simp]
theorem Term.wk_lift_succ_comp_subst0 (e : Term α)
  : e.subst0.comp (Subst.fromWk (Nat.liftWk Nat.succ)) = e.alpha0
  := by funext n; cases n <;> rfl

@[simp]
theorem Term.alpha0_var0 : (var 0).alpha0 = @Subst.id φ := by funext n; cases n <;> rfl

/-- A terminator -/
inductive Terminator (φ : Type) : Type
  | br : Nat → Term φ → Terminator φ
  | ite : Term φ → Terminator φ → Terminator φ → Terminator φ

/-- The free variables of this terminator -/
@[simp]
def Terminator.vfv : Terminator φ → Multiset ℕ
  | br _ e => e.fv
  | ite e s t => e.fv + s.vfv + t.vfv

/-- The highest free variable in this terminator, plus one -/
@[simp]
def Terminator.vfvi : Terminator φ → ℕ
  | br _ e => e.fvi
  | ite e s t => Nat.max e.fvi (Nat.max s.vfvi t.vfvi)

/-- The free labels of this terminator -/
@[simp]
def Terminator.lfv : Terminator φ → Multiset ℕ
  | br n _ => {n}
  | ite _ s t => s.lfv + t.lfv

/-- The highest free label in this terminator, plus one -/
@[simp]
def Terminator.lfvi : Terminator φ → ℕ
  | br n _ => n + 1
  | ite _ s t => Nat.max s.lfvi t.lfvi

/-- Rename the variables in a `Terminator` using `ρ` -/
@[simp]
def Terminator.vwk (ρ : ℕ → ℕ) : Terminator φ → Terminator φ
  | br n e => br n (e.wk ρ)
  | ite e s t => ite (e.wk ρ) (vwk ρ s) (vwk ρ t)

@[simp]
theorem Terminator.vwk_id (r : Terminator φ) : r.vwk id = r := by
  induction r <;> simp [Nat.liftnWk_id, *]

theorem Terminator.vwk_comp (σ τ : ℕ → ℕ) (r : Terminator φ)
  : r.vwk (σ ∘ τ) = (r.vwk τ).vwk σ := by
  induction r generalizing σ τ
  <;> simp [vwk, Term.wk_comp, Nat.liftWk_comp, Nat.liftnWk_comp, *]

theorem Terminator.vfv_vwk (ρ : ℕ → ℕ) (r : Terminator φ) : (r.vwk ρ).vfv = r.vfv.map ρ := by
  induction r <;> simp [*, Term.fv_wk]

theorem Terminator.lfv_vwk (ρ : ℕ → ℕ) (r : Terminator φ) : (r.vwk ρ).lfv = r.lfv := by
  induction r <;> simp [*]

/-- Substitute the variables in a `Terminator` using `σ` -/
@[simp]
def Terminator.vsubst (σ : Subst φ) : Terminator φ → Terminator φ
  | br n e => br n (e.subst σ)
  | ite e s t => ite (e.subst σ) (vsubst σ s) (vsubst σ t)

@[simp]
theorem Terminator.vsubst_id (r : Terminator φ) : r.vsubst Subst.id = r := by
  induction r <;> simp [Subst.lift_id, Subst.liftn_id, *]

theorem Terminator.vsubst_comp (σ τ : Subst φ) (r : Terminator φ)
  : r.vsubst (σ.comp τ) = (r.vsubst τ).vsubst σ := by
  induction r generalizing σ τ
  <;> simp [Term.subst_comp, Subst.lift_comp, Subst.liftn_comp, *]

theorem Terminator.lfv_vsubst (σ : Subst φ) (r : Terminator φ) : (r.vsubst σ).lfv = r.lfv := by
  induction r <;> simp [*]

theorem Terminator.vsubst_wk (ρ : ℕ -> ℕ) (r : Terminator φ)
  : r.vsubst (Subst.fromWk ρ) = r.vwk ρ := by
  induction r <;> simp [Term.subst_wk, Subst.fromWk_liftn, *]

@[simp]
theorem Terminator.vwk_succ_vsubst_subst0 (t : Terminator φ) (s : Term φ)
  : (t.vwk Nat.succ).vsubst s.subst0 = t := by
  rw [<-vsubst_wk, <-vsubst_comp, Term.wk_succ_comp_subst0, vsubst_id]

/-- Rename the labels in a `Region` using `ρ` -/
@[simp]
def Terminator.lwk (ρ : ℕ → ℕ) : Terminator φ → Terminator φ
  | br n e => br (ρ n) e
  | ite e s t => ite e (lwk ρ s) (lwk ρ t)

@[simp]
theorem Terminator.lwk_id (r : Terminator φ) : r.lwk id = r := by
  induction r <;> simp [Terminator.lwk, Nat.liftnWk_id, *]

theorem Terminator.lwk_comp (σ τ : ℕ → ℕ) (r : Terminator φ)
  : r.lwk (σ ∘ τ) = (r.lwk τ).lwk σ := by
  induction r generalizing σ τ <;> simp [lwk, Nat.liftnWk_comp, *]

theorem Terminator.vfv_lwk (ρ : ℕ → ℕ) (r : Terminator φ) : (r.lwk ρ).vfv = r.vfv := by
  induction r <;> simp [*]

theorem Terminator.lfv_lwk (ρ : ℕ → ℕ) (r : Terminator φ) : (r.lwk ρ).lfv = r.lfv.map ρ := by
  induction r <;> simp [*]

/-- A substitution mapping labels to terminators -/
def TSubst (φ : Type) := ℕ → Terminator φ

/-- The identity substitution, which maps labels to themselves -/
def TSubst.id : TSubst φ := λn => Terminator.br n (Term.var 0)

theorem TSubst.id_apply (n : ℕ) : @TSubst.id φ n = Terminator.br n (Term.var 0) := rfl

/-- Lift a substitution under a label binder -/
def TSubst.lift (σ : TSubst φ) : TSubst φ
  | 0 => Terminator.br 0 (Term.var 0)
  | n + 1 => (σ n).lwk Nat.succ

/-- Lift a substitution under `n` label binders -/
def TSubst.liftn (n : ℕ) (σ : TSubst φ) : TSubst φ
  := λm => if m < n then Terminator.br m (Term.var 0) else (σ (m - n)).lwk (λv => v + n)

theorem TSubst.liftn_zero (σ : TSubst φ) : σ.liftn 0 = σ := by
  funext n
  simp only [liftn]
  split
  . rename_i H; cases H
  . exact (σ n).lwk_id

theorem TSubst.liftn_one (σ : TSubst φ) : σ.liftn 1 = σ.lift := by funext m; cases m <;> rfl

theorem TSubst.liftn_succ (n) (σ: TSubst φ) : σ.liftn n.succ = (σ.liftn n).lift := by
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
          . simp only [<-Terminator.lwk_comp]
            apply congr
            apply congrArg
            funext v
            simp_arith
            simp_arith

theorem TSubst.liftn_eq_iterate_lift_apply (n: ℕ) (σ: TSubst φ) : σ.liftn n = (TSubst.lift^[n] σ) := by
  induction n with
  | zero => exact σ.liftn_zero
  | succ n => simp only [Function.iterate_succ_apply', TSubst.liftn_succ, *]

theorem TSubst.liftn_eq_iterate_lift (n: ℕ) : TSubst.liftn n = (@TSubst.lift φ)^[n] := by
  funext σ
  rw [liftn_eq_iterate_lift_apply]

@[simp]
theorem TSubst.lift_id : (@id φ).lift = id := by funext n; cases n <;> rfl

@[simp]
theorem TSubst.iterate_lift_id : (n: ℕ) -> TSubst.lift^[n] (@id φ) = id
  | 0 => rfl
  | n + 1 => by simp [lift_id, iterate_lift_id n]

@[simp]
theorem TSubst.liftn_id (n: ℕ): (@id φ).liftn n = id := by
  rw [liftn_eq_iterate_lift_apply, iterate_lift_id]

theorem TSubst.liftn_add (n m: ℕ) : TSubst.liftn (m + n) = (@TSubst.liftn α m) ∘ (@TSubst.liftn α n)
  := by simp [liftn_eq_iterate_lift, Function.iterate_add]

theorem TSubst.liftn_add_apply (n m: ℕ) (σ: TSubst α): (σ.liftn n).liftn m = σ.liftn (m + n)
  := by simp [liftn_add]

theorem TSubst.lift_succ (σ : TSubst φ) (i : ℕ) : σ.lift (i + 1) = (σ i).lwk Nat.succ := rfl

/-- Lift a substitution under a variable binder -/
def TSubst.vlift (σ : TSubst φ) : TSubst φ
  := Terminator.vwk (Nat.liftWk Nat.succ) ∘ σ

/-- Lift a substitution under `n` variable binders -/
def TSubst.vliftn (n : ℕ) (σ : TSubst φ) : TSubst φ
  := Terminator.vwk (Nat.liftWk (λi => i + n)) ∘ σ

-- TODO: vlift lemmas

/-- Substitute the labels in a `Terminator` using `σ` -/
@[simp]
def Terminator.lsubst (σ : TSubst φ) : Terminator φ → Terminator φ
  | Terminator.br n e => (σ n).vsubst e.subst0
  | Terminator.ite e s t => Terminator.ite e (lsubst σ s) (lsubst σ t)

@[simp]
theorem Terminator.lsubst_id (t : Terminator φ) : t.lsubst TSubst.id = t
  := by induction t <;> simp [*]

/-- Create a substitution from a label renaming -/
def TSubst.fromLwk (ρ : ℕ -> ℕ): TSubst φ := λn => Terminator.br (ρ n) (Term.var 0)

@[simp]
theorem TSubst.fromLwk_apply (ρ : ℕ -> ℕ) (n : ℕ)
  : (@fromLwk φ ρ) n = Terminator.br (ρ n) (Term.var 0) := rfl

theorem TSubst.fromLwk_lift (ρ) : (@fromLwk φ ρ).lift = fromLwk (Nat.liftWk ρ) := by
  funext n; cases n <;> rfl

theorem TSubst.fromLwk_iterate_lift (n : ℕ) (ρ)
  : TSubst.lift^[n] (@fromLwk φ ρ) = fromLwk (Nat.liftWk^[n] ρ)
  := by induction n generalizing ρ <;> simp [fromLwk_lift, *]

theorem TSubst.fromLwk_liftn (n ρ) : (@fromLwk φ ρ).liftn n = fromLwk (Nat.liftnWk n ρ) := by
  rw [liftn_eq_iterate_lift, Nat.liftnWk_eq_iterate_liftWk, fromLwk_iterate_lift]

theorem Terminator.lsubst_lwk (ρ : ℕ -> ℕ) (t : Terminator φ)
  : t.lsubst (TSubst.fromLwk ρ) = t.lwk ρ := by
  induction t <;> simp [Terminator.lsubst, Terminator.lwk, Term.subst_wk, *]

theorem Terminator.lsubst_liftn (n : ℕ) (σ : TSubst α) (t : Terminator α)
    : (t.lwk (Nat.liftnWk n Nat.succ)).lsubst (σ.liftn (n + 1))
      = (t.lsubst (σ.liftn n)).lwk (Nat.liftnWk n Nat.succ)
  := by induction t with
  | br ℓ e =>
    simp only [lwk, lsubst, Nat.liftnWk, TSubst.liftn]
    split
    . split
      . simp [lwk, Nat.liftnWk, *]
      . rename_i H C; exact (C (Nat.le_step H)).elim
    . rename_i C
      simp_arith only [ite_false]
      rw [Nat.succ_eq_add_one]
      have h : ℓ - n + 1 + n - (n + 1) = ℓ - n := by
        rw [Nat.add_assoc, Nat.add_comm 1 n, Nat.add_sub_cancel]
      rw [h]
      -- TODO: factor out as lemma
      generalize σ (ℓ - n) = t'
      induction t' with
      | br ℓ' e' => simp_arith [Nat.liftnWk]
      | _ => simp [*]
  | _ => simp [*]

theorem Terminator.lsubst_iterate_lift (n : ℕ) (σ : TSubst α) (t : Terminator α)
  : (t.lwk (Nat.liftWk^[n] Nat.succ)).lsubst (TSubst.lift^[n + 1] σ)
    = (t.lsubst (TSubst.lift^[n] σ)).lwk (Nat.liftWk^[n] Nat.succ)
  := by simp only [<-TSubst.liftn_eq_iterate_lift, <-Nat.liftnWk_eq_iterate_liftWk, lsubst_liftn]

theorem Terminator.lsubst_lift (t : Terminator α) (σ : TSubst α)
  : (t.lwk Nat.succ).lsubst (σ.lift) = (t.lsubst σ).lwk Nat.succ := t.lsubst_iterate_lift 0 σ

/-- Compose two label-substitutions to yield another -/
def TSubst.comp (σ τ : TSubst α): TSubst α
  | n => (τ n).lsubst (Terminator.vwk (Nat.liftWk Nat.succ) ∘ σ)

@[simp]
theorem TSubst.comp_id (σ : TSubst α) : σ.comp TSubst.id = σ := by
  funext n
  simp only [comp, Terminator.lsubst, Function.comp_apply]
  rw [<-Terminator.vsubst_wk, <-Terminator.vsubst_comp]
  simp

theorem TSubst.id_comp (σ : TSubst α) : TSubst.id.comp σ = σ := by
  funext n;
  simp only [comp]
  generalize σ n = t
  induction t <;> simp [*]

theorem Terminator.lsubst_comp (σ τ : TSubst α) (t : Terminator α)
  : t.lsubst (σ.comp τ) = (t.lsubst τ).lsubst σ
  := by induction t with
  | br ℓ e =>
    simp only [lsubst, TSubst.comp]
    -- TODO: factor out as lemma
    generalize τ ℓ = t'
    induction t' with
    | br ℓ' e' =>
      simp only [lsubst, <-vsubst_comp, <-vsubst_wk, Function.comp_apply]
      congr
      -- TODO: factor out as lemma
      funext n
      cases n <;> rfl
    | _ => simp [*]
  | _ => simp only [lsubst, TSubst.comp, *]

theorem TSubst.lift_comp (σ τ : TSubst α) : (σ.comp τ).lift = σ.lift.comp τ.lift := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [lift, comp, <-Terminator.lsubst_lwk, <-Terminator.lsubst_comp]
    congr
    funext n
    simp only [
      comp, lift, Function.comp_apply, Terminator.lsubst, Nat.succ_eq_add_one,
      <-Terminator.vsubst_wk, <-Terminator.vsubst_comp
    ]
    rw [<-Subst.comp_assoc, Term.wk_lift_succ_comp_subst0, Term.alpha0_var0, Subst.id_comp]
    generalize σ n = t
    induction t <;> simp [*]

theorem TSubst.iterate_lift_comp
  : (n : ℕ) -> ∀σ τ : TSubst α, TSubst.lift^[n] (σ.comp τ)
    = (TSubst.lift^[n] σ).comp (TSubst.lift^[n] τ)
  | 0, σ, τ => rfl
  | n + 1, σ, τ => by simp [TSubst.lift_comp, iterate_lift_comp n]

theorem TSubst.liftn_comp (n : ℕ) (σ τ : TSubst α)
  : (σ.comp τ).liftn n = (σ.liftn n).comp (τ.liftn n)
  := by rw [liftn_eq_iterate_lift, iterate_lift_comp]

/-- A basic block body -/
inductive Body (φ : Type) : Type
  | nil : Body φ
  | let1 : Term φ → Body φ → Body φ
  | let2 : Term φ → Body φ → Body φ

/-- The free variables in this body -/
@[simp]
def Body.fv : Body φ → Multiset ℕ
  | nil => 0
  | let1 e t => e.fv + t.fv.liftFv
  | let2 e t => e.fv + t.fv.liftnFv 2

/-- The highest free variable in this body, plus one -/
@[simp]
def Body.fvi : Body φ → ℕ
  | nil => 0
  | let1 e t => Nat.max e.fvi (t.fvi - 1)
  | let2 e t => Nat.max e.fvi (t.fvi - 2)

/-- Weaken a body -/
@[simp]
def Body.wk (ρ : ℕ → ℕ) : Body φ → Body φ
  | nil => nil
  | let1 e t => let1 (e.wk ρ) (t.wk (Nat.liftWk ρ))
  | let2 e t => let2 (e.wk ρ) (t.wk (Nat.liftnWk 2 ρ))

@[simp]
theorem Body.wk_id (b : Body φ) : b.wk id = b := by induction b <;> simp [*]

theorem Body.wk_comp (σ τ : ℕ → ℕ) (b : Body φ)
  : b.wk (σ ∘ τ) = (b.wk τ).wk σ := by
  induction b generalizing σ τ
  <;> simp [Term.wk_comp, Nat.liftWk_comp, Nat.liftnWk_comp, *]

theorem Body.fv_wk (ρ : ℕ → ℕ) (b : Body φ) : (b.wk ρ).fv = b.fv.map ρ := by
  induction b generalizing ρ <;>
  simp [Term.fv_wk, *]

/-- Substitute the variables in a body -/
@[simp]
def Body.subst (σ : Subst φ) : Body φ → Body φ
  | nil => nil
  | let1 e t => let1 (e.subst σ) (t.subst σ.lift)
  | let2 e t => let2 (e.subst σ) (t.subst (σ.liftn 2))

@[simp]
theorem Body.subst_id (b : Body φ) : b.subst Subst.id = b := by
  induction b <;> simp [Subst.lift_id, Subst.liftn_id, *]

theorem Body.subst_comp (σ τ : Subst φ) (b : Body φ)
  : b.subst (σ.comp τ) = (b.subst τ).subst σ := by
  induction b generalizing σ τ
  <;> simp [Term.subst_comp, Subst.lift_comp, Subst.liftn_comp, *]

/-- The number of variables defined in a body -/
@[simp]
def Body.num_defs : Body φ → ℕ
  | nil => 0
  | let1 _ t => t.num_defs + 1
  | let2 _ t => t.num_defs + 2

theorem Body.num_defs_wk (ρ : ℕ → ℕ) (b : Body φ) : (b.wk ρ).num_defs = b.num_defs := by
  induction b generalizing ρ <;> simp [*]

theorem Body.num_defs_subst (σ : Subst φ) (b : Body φ) : (b.subst σ).num_defs = b.num_defs := by
  induction b generalizing σ <;> simp [*]

-- TODO: stepnwk and friends

/-- Append two bodies, letting the second use the variables defined in the first -/
def Body.append (b b' : Body φ) : Body φ := match b with
  | nil => b'
  | let1 a t => let1 a (t.append b')
  | let2 a t => let2 a (t.append b')

theorem Body.fv_append (b b' : Body φ) : (b.append b').fv = b.fv + b'.fv.liftnFv b.num_defs := by
  induction b generalizing b'
  <;> simp [append, fv, <-Multiset.liftnFv_add, add_assoc, Nat.add_comm, *]

theorem Body.append_num_defs (b b' : Body φ)
  : (b.append b').num_defs = b.num_defs + b'.num_defs := by
  induction b generalizing b' <;> simp_arith [append, num_defs, *]

@[simp]
theorem Body.nil_append (b : Body φ) : nil.append b = b := rfl

@[simp]
theorem Body.append_nil (b : Body φ) : b.append nil = b := by
  induction b <;> simp [append, *]

theorem Body.append_assoc (b b' b'' : Body φ)
  : (b.append b').append b'' = b.append (b'.append b'') := by
  induction b generalizing b' b'' <;> simp [append, *]

theorem Body.wk_append (ρ : ℕ → ℕ) (b b' : Body φ)
  : (b.append b').wk ρ = (b.wk ρ).append (b'.wk (Nat.liftnWk b.num_defs ρ)) := by
  induction b generalizing ρ b' with
  | nil => rfl
  | _ => simp only [wk, *, append, num_defs, let1.injEq, true_and, Nat.liftnWk_succ]; congr

/-- Append two bodies, weakening the second so that it shares the same inputs as the first -/
def Body.ltimes (b b' : Body φ) : Body φ := b.append (b'.wk (· + b.num_defs))

theorem Body.fv_ltimes (b b' : Body φ) : (b.ltimes b').fv = b.fv + b'.fv := by
  rw [ltimes, fv_append, fv_wk]
  congr
  -- TODO: factor out as theorem in `Discretion`
  generalize b'.fv = s
  generalize b.num_defs = n
  open Multiset in
  ext i
  simp only [liftnFv, ge_iff_le, count_map, filter_filter, <-countP_eq_card_filter, countP_map]
  congr
  ext a
  simp

theorem Body.ltimes_num_defs (b b' : Body φ) : (b.ltimes b').num_defs = b.num_defs + b'.num_defs
  := by simp [ltimes, append_num_defs, Body.num_defs_wk]

theorem Body.wk_ltimes (ρ : ℕ → ℕ) (b b' : Body φ)
  : (b.ltimes b').wk ρ = (b.wk ρ).ltimes (b'.wk ρ) := by
  simp only [ltimes, wk_append, <-wk_comp]
  congr
  funext n
  simp [Function.comp_apply, Nat.liftnWk, num_defs_wk]

@[simp]
theorem Body.ltimes_nil (b : Body φ) : b.ltimes nil = b := by simp [ltimes]

@[simp]
theorem Body.nil_ltimes (b : Body φ) : nil.ltimes b = b :=
  by simp only [ltimes, num_defs, add_zero, nil_append]; exact b.wk_id

theorem Body.let1_ltimes (a : Term φ) (b b' : Body φ)
  : (let1 a b).ltimes b' = let1 a (b.ltimes (b'.wk Nat.succ)) := by
  simp only [ltimes, append, wk_append, <-wk_comp]
  congr
  funext n
  simp_arith

theorem Body.let2_ltimes (a : Term φ) (b b' : Body φ)
  : (let2 a b).ltimes b' = let2 a (b.ltimes (b'.wk (λn => n + 2))) := by
  simp only [ltimes, append, wk_append, <-wk_comp]
  congr
  funext n
  simp_arith

theorem Body.ltimes_assoc (b b' b'' : Body φ)
  : (b.ltimes b').ltimes b'' = b.ltimes (b'.ltimes b'') := by
  induction b generalizing b' b'' <;> simp [let1_ltimes, let2_ltimes, wk_ltimes, *]

-- TODO: make Body into a monoid this way

-- TODO: relationship between append and comp

-- TODO: define comp as append instead? removes the need for compn...

-- TODO: another issue: now there are _two_ monoid structures on Body

-- TODO: variant with a body followed by a weakening (WBody?). This is also a monoid, of course.

-- TODO: in fact, _this_ variant supports an _rtimes_ operation. Wow!

/-- A basic-block -/
structure Block (φ : Type) : Type where
  /-- The body of this basic block, containing the instructions and variable definitions within -/
  body : Body φ
  /-- The terminator of this basic block, determining where control flow goes to after the body
  is finished executing -/
  terminator : Terminator φ

/-- The free variables in this basic block -/
@[simp]
def Block.vfv (β : Block φ) : Multiset ℕ := β.body.fv + β.terminator.vfv.liftnFv β.body.num_defs

/-- The highest free variable in this basic block, plus one -/
@[simp]
def Block.vfvi (β : Block φ) : ℕ := Nat.max β.body.fvi (β.terminator.vfvi - β.body.num_defs)

/-- The free labels in this basic block -/
@[simp]
def Block.lfv (β : Block φ) : Multiset ℕ := β.terminator.lfv

/-- The highest free label in this basic block, plus one -/
@[simp]
def Block.lfvi (β : Block φ) : ℕ := β.terminator.lfvi

/-- Weaken the variables in this basic block -/
@[simp]
def Block.vwk (ρ : ℕ → ℕ) (β : Block φ) : Block φ where
  body := β.body.wk ρ
  terminator := β.terminator.vwk (Nat.liftnWk β.body.num_defs ρ)

@[simp]
theorem Block.vwk_id (β : Block φ) : β.vwk id = β := by simp

theorem Block.vwk_comp (σ τ : ℕ → ℕ) (β : Block φ) : β.vwk (σ ∘ τ) = (β.vwk τ).vwk σ
  := by simp [Body.wk_comp, Terminator.vwk_comp, Body.num_defs_wk, Nat.liftnWk_comp, *]

theorem Block.vfv_vwk (ρ : ℕ → ℕ) (β : Block φ) : (β.vwk ρ).vfv = β.vfv.map ρ := by
  simp [Terminator.vfv_vwk, Body.fv_wk, Body.num_defs_wk]

theorem Block.lfv_vwk (ρ : ℕ → ℕ) (β : Block φ) : (β.vwk ρ).lfv = β.lfv := by
  simp [Terminator.lfv_vwk]

/-- Substitute the variables in this basic block -/
@[simp]
def Block.vsubst (σ : Subst φ) (β : Block φ) : Block φ where
  body := β.body.subst σ
  terminator := β.terminator.vsubst (σ.liftn β.body.num_defs)

@[simp]
theorem Block.vsubst_id (β : Block φ) : β.vsubst Subst.id = β := by simp

theorem Block.vsubst_comp (σ τ : Subst φ) (β : Block φ)
  : β.vsubst (σ.comp τ) = (β.vsubst τ).vsubst σ
  := by simp [Body.subst_comp, Body.num_defs_subst, Subst.liftn_comp, Terminator.vsubst_comp, *]

/-- Weaken the labels in this basic block -/
@[simp]
def Block.lwk (ρ : ℕ → ℕ) (β : Block φ) : Block φ where
  body := β.body
  terminator := β.terminator.lwk ρ

@[simp]
theorem Block.lwk_id (β : Block φ) : β.lwk id = β := by simp

theorem Block.lwk_comp (σ τ : ℕ → ℕ) (β : Block φ) : β.lwk (σ ∘ τ) = (β.lwk τ).lwk σ
  := by simp [Terminator.lwk_comp]

theorem Block.vfv_lwk (ρ : ℕ → ℕ) (β : Block φ) : (β.lwk ρ).vfv = β.vfv := by
  simp [Terminator.vfv_lwk]

theorem Block.lfv_lwk (ρ : ℕ → ℕ) (β : Block φ) : (β.lwk ρ).lfv = β.lfv.map ρ := by
  simp [Terminator.lfv_lwk]

def Block.lsubst (σ : TSubst φ) (β : Block φ) : Block φ where
  body := β.body
  terminator := β.terminator.lsubst (σ.vliftn β.body.num_defs)

/-- Prepend a body of instructions to this basic block -/
def Block.prepend (b : Body φ) (β : Block φ) : Block φ where
  body := b.append β.body
  terminator := β.terminator

theorem Block.prepend_nil (β : Block φ) : β.prepend Body.nil = β := rfl

theorem Block.prepend_append (b b' : Body φ) (β : Block φ)
  : β.prepend (b.append b') = (β.prepend b').prepend b := by
  simp only [Block.prepend, Body.append_assoc]

-- TODO: prepend_nil, pretty trivial

-- TODO: prepend_vwk

-- TODO: prepend_lwk

-- TODO: rename to rtimes?

/-- Precompose a body of instructions to this basic block, while weakening the block so that
they share the same inputs -/
def Block.ltimes (b : Body φ) (β : Block φ) : Block φ
  := (β.vwk (· + b.num_defs)).prepend b
  -- body := b.ltimes β.body
  -- terminator := β.terminator.vwk (β.body.num_defs.liftnWk (· + b.num_defs))

theorem Block.ltimes_nil : (β : Block φ) → β.ltimes Body.nil = β
  | ⟨body, terminator⟩ => by
    simp only [ltimes, prepend, vwk, Body.num_defs, add_zero, Body.nil_append, mk.injEq]
    exact ⟨Body.wk_id _, Nat.liftnWk_id body.num_defs ▸ Terminator.vwk_id _⟩

-- theorem Block.ltimes_ltimes (b b' : Body φ) (β : Block φ)
--   : β.ltimes (b.ltimes b') = (β.ltimes b').ltimes b := by
--   simp only [ltimes_eq_append_wk, Body.ltimes]
--   rw [prepend_append]
--   sorry -- TODO: by prepend_vwk

-- TODO: make Body have a monoid action on Block

-- TODO: ltimes_vwk

-- TODO: ltimes_lwk

/-- Convert this terminator to a basic block with no instructions -/
def Terminator.toBlock (t : Terminator φ) : Block φ := ⟨Body.nil, t⟩

theorem Terminator.toBlock_vwk (ρ : ℕ → ℕ) (t : Terminator φ) : (t.vwk ρ).toBlock = t.toBlock.vwk ρ
  := rfl

theorem Terminator.toBlock_vsubst (σ : Subst φ) (t : Terminator φ)
  : (t.vsubst σ).toBlock = t.toBlock.vsubst σ
  := by simp [toBlock, Block.vsubst, Body.subst, Body.num_defs, Subst.liftn_zero]

theorem Terminator.toBlock_lwk (ρ : ℕ → ℕ) (t : Terminator φ) : (t.lwk ρ).toBlock = t.toBlock.lwk ρ
  := rfl

-- TODO: toBlock_lsubst

theorem Terminator.toBlock_injective : Function.Injective (@Terminator.toBlock φ) := by
  intro t₁ t₂ H
  cases t₁ <;> cases t₂ <;> cases H <;> rfl

theorem Terminator.toBlock_inj {t₁ t₂ : Terminator φ} : t₁.toBlock = t₂.toBlock ↔ t₁ = t₂ :=
    Terminator.toBlock_injective.eq_iff

instance : Coe (Terminator φ) (Block φ) := ⟨Terminator.toBlock⟩

theorem Terminator.coe_toBlock_vwk (ρ : ℕ → ℕ) (t : Terminator φ)
  : (t.vwk ρ : Block φ) = (t : Block φ).vwk ρ := rfl

theorem Terminator.coe_toBlock_vsubst (σ : Subst φ) (t : Terminator φ)
  : (t.vsubst σ : Block φ) = (t : Block φ).vsubst σ := toBlock_vsubst σ t

theorem Terminator.coe_toBlock_lwk (ρ : ℕ → ℕ) (t : Terminator φ)
  : (t.lwk ρ : Block φ) = (t : Block φ).lwk ρ := rfl

theorem Terminator.coe_toBlock_inj {t₁ t₂ : Terminator φ} : (t₁ : Block φ) = t₂ ↔ t₁ = t₂ :=
    Terminator.toBlock_injective.eq_iff

-- TODO: coe_lsubst

/-- A basic block-based single-entry multiple-exit region -/
inductive BBRegion (φ : Type) : Type
  | cfg (β : Block φ) (n : Nat) : (Fin n → BBRegion φ) → BBRegion φ

/-- The free variables in this region -/
@[simp]
def BBRegion.vfv : BBRegion φ → Multiset ℕ
  | cfg β _ f => β.vfv + Finset.sum Finset.univ (λi => (f i).vfv.liftnFv (β.body.num_defs + 1))

/-- The free label variables in this region -/
@[simp]
def BBRegion.lfv : BBRegion φ → Multiset ℕ
  | cfg β n f => β.lfv.liftnFv n + Finset.sum Finset.univ (λi => (f i).lfv.liftnFv n)

/-- Weaken the variables in this region -/
@[simp]
def BBRegion.vwk (ρ : ℕ → ℕ) : BBRegion φ → BBRegion φ
  | cfg β n f => cfg (β.vwk ρ) n (λ i => (f i).vwk (Nat.liftnWk (β.body.num_defs + 1) ρ))

@[simp]
theorem BBRegion.vwk_id (r : BBRegion φ) : r.vwk id = r := by
  induction r; simp [*]

theorem BBRegion.vwk_comp (σ τ : ℕ → ℕ) (r : BBRegion φ)
  : r.vwk (σ ∘ τ) = (r.vwk τ).vwk σ := by
  induction r generalizing σ τ
  simp [Body.wk_comp, Terminator.vwk_comp, Body.num_defs_wk, Nat.liftWk_comp, Nat.liftnWk_comp, *]

theorem BBRegion.vfv_vwk (ρ : ℕ → ℕ) (r : BBRegion φ) : (r.vwk ρ).vfv = r.vfv.map ρ := by
  induction r generalizing ρ
  simp only [vfv, Block.vfv, Block.vwk, Body.fv_wk, Body.num_defs_wk, Terminator.vfv_vwk,
    Multiset.liftnFv_map_liftnWk, Nat.liftnWk_succ', Function.comp_apply, Multiset.map_add,
    Multiset.map_finsum, add_right_inj, *]
  congr
  funext i
  rw [
    Multiset.liftnFv_succ,
    Multiset.liftFv_map_liftWk,
    Multiset.liftnFv_map_liftnWk,
    Multiset.liftnFv_succ]

theorem BBRegion.lfv_vwk (ρ : ℕ → ℕ) (r : BBRegion φ) : (r.vwk ρ).lfv = r.lfv := by
  induction r generalizing ρ; simp [Terminator.lfv_vwk, *]

/-- Substitute the variables in this region -/
@[simp]
def BBRegion.vsubst (σ : Subst φ) : BBRegion φ → BBRegion φ
  | cfg β n f => cfg (β.vsubst σ) n (λ i => (f i).vsubst (σ.liftn (β.body.num_defs + 1)))

@[simp]
theorem BBRegion.vsubst_id (r : BBRegion φ) : r.vsubst Subst.id = r := by
  induction r; simp [*]

theorem BBRegion.vsubst_comp (σ τ : Subst φ) (r : BBRegion φ)
  : r.vsubst (σ.comp τ) = (r.vsubst τ).vsubst σ := by
  induction r generalizing σ τ
  simp [Body.subst_comp, Body.num_defs_subst, Subst.liftn_comp, Terminator.vsubst_comp, *]

/-- Weaken the labels in this region -/
@[simp]
def BBRegion.lwk (ρ : ℕ → ℕ) : BBRegion φ → BBRegion φ
  | cfg β n f => cfg (β.lwk (Nat.liftnWk n ρ)) n (λ i => (f i).lwk (Nat.liftnWk n ρ))

@[simp]
theorem BBRegion.lwk_id (r : BBRegion φ) : r.lwk id = r := by
  induction r; simp [*]

theorem BBRegion.lwk_comp (σ τ : ℕ → ℕ) (r : BBRegion φ)
  : r.lwk (σ ∘ τ) = (r.lwk τ).lwk σ := by
  induction r generalizing σ τ
  simp [Body.wk_comp, Terminator.lwk_comp, Nat.liftnWk_comp, *]

theorem BBRegion.vfv_lwk (ρ : ℕ → ℕ) (r : BBRegion φ) : (r.lwk ρ).vfv = r.vfv := by
  induction r generalizing ρ; simp [Terminator.vfv_lwk, *]

theorem BBRegion.lfv_lwk (ρ : ℕ → ℕ) (r : BBRegion φ) : (r.lwk ρ).lfv = r.lfv.map ρ := by
  induction r generalizing ρ; simp [Terminator.lfv_lwk, Multiset.map_finsum, *]

def BBRegion.lsubst (σ : TSubst φ) : BBRegion φ → BBRegion φ
  | cfg β n f => cfg (β.lsubst (σ.liftn n)) n
    (λ i => (f i).lsubst ((σ.liftn n).vliftn β.body.num_defs))

-- TODO: BBRegion.prepend

-- TODO: BBRegion.ltimes

/-- A basic-block based control-flow graph with `length` entry-point regions -/
structure BBCFG (φ : Type) : Type where
  /-- The number of entry points to this CFG -/
  length : Nat
  /-- The number of exits for this CFG -/
  targets : Fin length → BBRegion φ

@[simp]
def BBCFG.vwk (ρ : ℕ → ℕ) (cfg : BBCFG φ) : BBCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).vwk ρ

@[simp]
theorem BBCFG.vwk_id (cfg : BBCFG φ) : cfg.vwk id = cfg := by
  cases cfg; simp [*]

theorem BBCFG.vwk_comp (σ τ : ℕ → ℕ) (cfg : BBCFG φ) : cfg.vwk (σ ∘ τ) = (cfg.vwk τ).vwk σ := by
  cases cfg; simp [BBRegion.vwk_comp, *]

@[simp]
def BBCFG.vsubst (σ : Subst φ) (cfg : BBCFG φ) : BBCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).vsubst σ

@[simp]
theorem BBCFG.vsubst_id (cfg : BBCFG φ) : cfg.vsubst Subst.id = cfg := by
  cases cfg; simp [*]

theorem BBCFG.vsubst_comp (σ τ : Subst φ) (cfg : BBCFG φ)
  : cfg.vsubst (σ.comp τ) = (cfg.vsubst τ).vsubst σ := by
  cases cfg; simp [BBRegion.vsubst_comp, *]

@[simp]
def BBCFG.lwk (ρ : ℕ → ℕ) (cfg : BBCFG φ) : BBCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).lwk ρ

@[simp]
theorem BBCFG.lwk_id (cfg : BBCFG φ) : cfg.lwk id = cfg := by
  cases cfg; simp [*]

theorem BBCFG.lwk_comp (σ τ : ℕ → ℕ) (cfg : BBCFG φ) : cfg.lwk (σ ∘ τ) = (cfg.lwk τ).lwk σ := by
  cases cfg; simp [BBRegion.lwk_comp, *]

def BBCFG.lsubst (σ : TSubst φ) (cfg : BBCFG φ) : BBCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).lsubst σ

/-- A terminator-based single-entry multiple-exit region -/
inductive TRegion (φ : Type) : Type
  | let1 : Term φ → TRegion φ → TRegion φ
  | let2 : Term φ → TRegion φ → TRegion φ
  | cfg (β : Terminator φ) (n : Nat) : (Fin n → TRegion φ) → TRegion φ

/-- Weaken the variables in this region -/
@[simp]
def TRegion.vwk (ρ : ℕ → ℕ) : TRegion φ → TRegion φ
  | let1 e t => let1 (e.wk ρ) (t.vwk (Nat.liftWk ρ))
  | let2 e t => let2 (e.wk ρ) (t.vwk (Nat.liftnWk 2 ρ))
  | cfg β n f => cfg (β.vwk ρ) n (λ i => (f i).vwk (Nat.liftWk ρ))

@[simp]
theorem TRegion.vwk_id (r : TRegion φ) : r.vwk id = r := by
  induction r <;> simp [TRegion.vwk, *]

theorem TRegion.vwk_comp (σ τ : ℕ → ℕ) (r : TRegion φ)
  : r.vwk (σ ∘ τ) = (r.vwk τ).vwk σ := by
  induction r generalizing σ τ
  <;> simp [Term.wk_comp, Terminator.vwk_comp, Nat.liftWk_comp, Nat.liftnWk_comp, *]

/-- Substitute the variables in this region -/
@[simp]
def TRegion.vsubst (σ : Subst φ) : TRegion φ → TRegion φ
  | let1 e t => let1 (e.subst σ) (t.vsubst σ.lift)
  | let2 e t => let2 (e.subst σ) (t.vsubst (σ.liftn 2))
  | cfg β n f => cfg (β.vsubst σ) n (λ i => (f i).vsubst σ.lift)

@[simp]
theorem TRegion.vsubst_id (r : TRegion φ) : r.vsubst Subst.id = r := by
  induction r <;> simp [TRegion.vsubst, Subst.lift_id, Subst.liftn_id, *]

theorem TRegion.vsubst_comp (σ τ : Subst φ) (r : TRegion φ)
  : r.vsubst (σ.comp τ) = (r.vsubst τ).vsubst σ := by
  induction r generalizing σ τ
  <;> simp [Term.subst_comp, Terminator.vsubst_comp, Subst.lift_comp, Subst.liftn_comp, *]

/-- Weaken the labels in this region -/
@[simp]
def TRegion.lwk (ρ : ℕ → ℕ) : TRegion φ → TRegion φ
  | let1 e t => let1 e (t.lwk ρ)
  | let2 e t => let2 e (t.lwk ρ)
  | cfg β n f => cfg (β.lwk (Nat.liftnWk n ρ)) n (λ i => (f i).lwk (Nat.liftnWk n ρ))

@[simp]
theorem TRegion.lwk_id (r : TRegion φ) : r.lwk id = r := by
  induction r <;> simp [TRegion.lwk, *]

theorem TRegion.lwk_comp (σ τ : ℕ → ℕ) (r : TRegion φ)
  : r.lwk (σ ∘ τ) = (r.lwk τ).lwk σ := by
  induction r generalizing σ τ
  <;> simp [Term.wk_comp, Terminator.lwk_comp, Nat.liftnWk_comp, *]

def TRegion.lsubst (σ : TSubst φ) : TRegion φ → TRegion φ
  | let1 e t => let1 e (t.lsubst σ.vlift)
  | let2 e t => let2 e (t.lsubst (σ.vliftn 2))
  | cfg β n f => cfg (β.lsubst (σ.liftn n)) n (λ i => (f i).lsubst (σ.liftn n))

-- TODO: TRegion.prepend

-- TODO: TRegion.ltimes

-- TODO: TRegion.body

-- TODO: TRegion.tail

-- TODO: tail.prepend body = id

/-- A terminator-block based control-flow graph with `length` entry-point regions -/
structure TCFG (φ : Type) : Type where
  /-- The number of entry points to this CFG -/
  length : Nat
  /-- The number of exits for this CFG -/
  targets : Fin length → TRegion φ

def TCFG.vwk (ρ : ℕ → ℕ) (cfg : TCFG φ) : TCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).vwk ρ

@[simp]
theorem TCFG.vwk_id (cfg : TCFG φ) : cfg.vwk id = cfg := by
  cases cfg; simp [TCFG.vwk, *]

theorem TCFG.vwk_comp (σ τ : ℕ → ℕ) (cfg : TCFG φ) : cfg.vwk (σ ∘ τ) = (cfg.vwk τ).vwk σ := by
  cases cfg; simp [TCFG.vwk, TRegion.vwk_comp, *]

def TCFG.vsubst (σ : Subst φ) (cfg : TCFG φ) : TCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).vsubst σ

@[simp]
theorem TCFG.vsubst_id (cfg : TCFG φ) : cfg.vsubst Subst.id = cfg := by
  cases cfg; simp [TCFG.vsubst, *]

theorem TCFG.vsubst_comp (σ τ : Subst φ) (cfg : TCFG φ)
  : cfg.vsubst (σ.comp τ) = (cfg.vsubst τ).vsubst σ := by
  cases cfg; simp [TCFG.vsubst, TRegion.vsubst_comp, *]

def TCFG.lwk (ρ : ℕ → ℕ) (cfg : TCFG φ) : TCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).lwk (Nat.liftnWk cfg.length ρ)

@[simp]
theorem TCFG.lwk_id (cfg : TCFG φ) : cfg.lwk id = cfg := by
  cases cfg; simp [TCFG.lwk, *]

theorem TCFG.lwk_comp (σ τ : ℕ → ℕ) (cfg : TCFG φ) : cfg.lwk (σ ∘ τ) = (cfg.lwk τ).lwk σ := by
  cases cfg; simp [TCFG.lwk, TRegion.lwk_comp, Nat.liftnWk_comp, *]

def TCFG.lsubst (σ : TSubst φ) (cfg : TCFG φ) : TCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).lsubst σ

-- TODO: TRegion.tail'

-- TODO: TRegion.terminator

-- TODO: TRegion.cfg

-- TODO: normalize TRegion to BBRegion; commutes with label-substitution

-- TODO: normalize BBRegion to TRegion; commutes with label-substitution

/-- A single-entry multiple-exit region -/
inductive Region (φ : Type) : Type
  | br : Nat → Term φ → Region φ
  | ite : Term φ → Region φ → Region φ → Region φ
  | let1 : Term φ → Region φ → Region φ
  | let2 : Term φ → Region φ → Region φ
  | cfg (β : Region φ) (n : Nat) : (Fin n → Region φ) → Region φ

/-- Rename the variables in a `Region` using `ρ` -/
@[simp]
def Region.vwk (ρ : ℕ → ℕ) : Region φ → Region φ
  | br n e => br n (e.wk ρ)
  | ite e s t => ite (e.wk ρ) (vwk ρ s) (vwk ρ t)
  | let1 e t => let1 (e.wk ρ) (vwk (Nat.liftWk ρ) t)
  | let2 e t => let2 (e.wk ρ) (vwk (Nat.liftnWk 2 ρ) t)
  | cfg β n f => cfg (vwk ρ β) n (λ i => (f i).vwk (Nat.liftWk ρ))

@[simp]
theorem Region.vwk_id (r : Region φ) : r.vwk id = r := by
  induction r <;> simp [Region.vwk, Nat.liftnWk_id, *]

theorem Region.vwk_comp (σ τ : ℕ → ℕ) (r : Region φ)
  : r.vwk (σ ∘ τ) = (r.vwk τ).vwk σ := by
  induction r generalizing σ τ
  <;> simp [vwk, Term.wk_comp, Nat.liftWk_comp, Nat.liftnWk_comp, *]

/-- Substitute the variables in a `Region` using `σ` -/
@[simp]
def Region.vsubst (σ : Subst φ) : Region φ → Region φ
  | br n e => br n (e.subst σ)
  | ite e s t => ite (e.subst σ) (vsubst σ s) (vsubst σ t)
  | let1 e t => let1 (e.subst σ) (vsubst σ.lift t)
  | let2 e t => let2 (e.subst σ) (vsubst (σ.liftn 2) t)
  | cfg β n f => cfg (vsubst σ β) n (λ i => (f i).vsubst σ.lift)

@[simp]
theorem Region.vsubst_id (r : Region φ) : r.vsubst Subst.id = r := by
  induction r <;> simp [*]

theorem Region.vsubst_comp (σ τ : Subst φ) (r : Region φ)
  : r.vsubst (σ.comp τ) = (r.vsubst τ).vsubst σ := by
  induction r generalizing σ τ
  <;> simp [Term.subst_comp, Subst.lift_comp, Subst.liftn_comp, *]

/-- Rename the labels in a `Region` using `ρ` -/
@[simp]
def Region.lwk (ρ : ℕ → ℕ) : Region φ → Region φ
  | br n e => br (ρ n) e
  | ite e s t => ite e (lwk ρ s) (lwk ρ t)
  | let1 e t => let1 e (lwk ρ t)
  | let2 e t => let2 e (lwk ρ t)
  | cfg β n f => cfg (lwk (Nat.liftnWk n ρ) β) n (λ i => (f i).lwk (Nat.liftnWk n ρ))

@[simp]
theorem Region.lwk_id (r : Region φ) : r.lwk id = r := by induction r <;> simp [*]

theorem Region.lwk_comp (σ τ : ℕ → ℕ) (r : Region φ) : r.lwk (σ ∘ τ) = (r.lwk τ).lwk σ := by
  induction r generalizing σ τ <;> simp [Nat.liftnWk_comp, *]

/-- A substitution mapping labels to regions -/
def RSubst (φ : Type) := ℕ → Region φ -- TODO: Region.Subst?

/-- The identity substitution, which maps labels to themselves -/
def RSubst.id : RSubst φ := λn => Region.br n (Term.var 0)

theorem RSubst.id_apply (n : ℕ) : @RSubst.id φ n = Region.br n (Term.var 0) := rfl

/-- Lift a substitution under a label binder -/
def RSubst.lift (σ : RSubst φ) : RSubst φ
  | 0 => Region.br 0 (Term.var 0)
  | n + 1 => (σ n).lwk Nat.succ

/-- Lift a substitution under `n` label binders -/
def RSubst.liftn (n : ℕ) (σ : RSubst φ) : RSubst φ
  := λm => if m < n then Region.br m (Term.var 0) else (σ (m - n)).lwk (λv => v + n)

theorem RSubst.liftn_zero (σ : RSubst φ) : σ.liftn 0 = σ := by
  funext n
  simp only [liftn]
  split
  . rename_i H; cases H
  . exact (σ n).lwk_id

theorem RSubst.liftn_one (σ : RSubst φ) : σ.liftn 1 = σ.lift := by funext m; cases m <;> rfl

theorem RSubst.liftn_succ (n) (σ: RSubst φ) : σ.liftn n.succ = (σ.liftn n).lift := by
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
          . simp only [<-Region.lwk_comp]
            apply congr
            apply congrArg
            funext v
            simp_arith
            simp_arith

theorem RSubst.liftn_eq_iterate_lift_apply (n: ℕ) (σ: RSubst φ) : σ.liftn n = (RSubst.lift^[n] σ) := by
  induction n with
  | zero => exact σ.liftn_zero
  | succ n => simp only [Function.iterate_succ_apply', RSubst.liftn_succ, *]

theorem RSubst.liftn_eq_iterate_lift (n: ℕ) : RSubst.liftn n = (@RSubst.lift φ)^[n] := by
  funext σ
  rw [liftn_eq_iterate_lift_apply]

@[simp]
theorem RSubst.lift_id : (@id φ).lift = id := by funext n; cases n <;> rfl

@[simp]
theorem RSubst.iterate_lift_id : (n: ℕ) -> RSubst.lift^[n] (@id φ) = id
  | 0 => rfl
  | n + 1 => by simp [lift_id, iterate_lift_id n]

@[simp]
theorem RSubst.liftn_id (n: ℕ): (@id φ).liftn n = id := by
  rw [liftn_eq_iterate_lift_apply, iterate_lift_id]

theorem RSubst.liftn_add (n m: ℕ) : RSubst.liftn (m + n) = (@RSubst.liftn α m) ∘ (@RSubst.liftn α n)
  := by simp [liftn_eq_iterate_lift, Function.iterate_add]

theorem RSubst.liftn_add_apply (n m: ℕ) (σ: RSubst α): (σ.liftn n).liftn m = σ.liftn (m + n)
  := by simp [liftn_add]

theorem RSubst.lift_succ (σ : RSubst φ) (i : ℕ) : σ.lift (i + 1) = (σ i).lwk Nat.succ := rfl

/-- Lift a substitution under a variable binder -/
def RSubst.vlift (σ : RSubst φ) : RSubst φ
  := Region.vwk (Nat.liftWk Nat.succ) ∘ σ

/-- Lift a substitution under `n` variable binders -/
def RSubst.vliftn (n : ℕ) (σ : RSubst φ) : RSubst φ
  := Region.vwk (Nat.liftWk (λi => i + n)) ∘ σ

/-- Substitute the labels in a `Region` using `σ` -/
@[simp]
def Region.lsubst (σ : RSubst φ) : Region φ → Region φ
  | br n e => (σ n).vsubst e.subst0
  | ite e s t => ite e (lsubst σ s) (lsubst σ t)
  | let1 e t => let1 e (lsubst σ.vlift t)
  | let2 e t => let2 e (lsubst (σ.vliftn 2) t)
  | cfg β n f => cfg (lsubst (σ.liftn n) β) n (λ i => lsubst (σ.liftn n) (f i))

-- TODO: lsubst_id, lsubst_comp

/-- Compose two label-substitutions to yield another -/
def RSubst.comp (σ τ : RSubst α): RSubst α
  | n => (τ n).lsubst (Region.vwk (Nat.liftWk Nat.succ) ∘ σ)

/-- Convert this `Terminator` to a `Region` -/
@[simp]
def Terminator.toRegion : Terminator φ → Region φ
  | Terminator.br n e => Region.br n e
  | Terminator.ite e s t => Region.ite e s.toRegion t.toRegion

theorem Terminator.toRegion_vwk (ρ : ℕ → ℕ) (t : Terminator φ)
  : (t.vwk ρ).toRegion = t.toRegion.vwk ρ := by induction t <;> simp [*]

theorem Terminator.toRegion_vsubst (σ : Subst φ) (t : Terminator φ)
  : (t.vsubst σ).toRegion = t.toRegion.vsubst σ := by induction t <;> simp [*]

theorem Terminator.toRegion_lwk (ρ : ℕ → ℕ) (t : Terminator φ)
  : (t.lwk ρ).toRegion = t.toRegion.lwk ρ := by induction t <;> simp [*]

theorem Terminator.toRegion_inj {t₁ t₂ : Terminator φ} : t₁.toRegion = t₂.toRegion ↔ t₁ = t₂ := by
  induction t₁ generalizing t₂ <;> cases t₂ <;> simp [*]

theorem Terminator.toRegion_injective : Function.Injective (@Terminator.toRegion φ)
  := λ_ _ h => toRegion_inj.mp h

instance : Coe (Terminator φ) (Region φ) := ⟨Terminator.toRegion⟩

theorem Terminator.coe_toRegion_vwk (ρ : ℕ → ℕ) (t : Terminator φ)
  : (t.vwk ρ : Region φ) = (t : Region φ).vwk ρ := toRegion_vwk ρ t

theorem Terminator.coe_toRegion_vsubst (σ : Subst φ) (t : Terminator φ)
  : (t.vsubst σ : Region φ) = (t : Region φ).vsubst σ := toRegion_vsubst σ t

theorem Terminator.coe_toRegion_lwk (ρ : ℕ → ℕ) (t : Terminator φ)
  : (t.lwk ρ : Region φ) = (t : Region φ).lwk ρ := toRegion_lwk ρ t

def TSubst.toRegion (σ : TSubst φ) : RSubst φ := λn => σ n -- TODO: Terminator.Subst?

theorem TSubst.toRegion_lift (σ : TSubst φ) : σ.lift.toRegion = σ.toRegion.lift := by
  funext n; simp only [RSubst.lift, toRegion, lift]; split <;> simp [Terminator.toRegion_lwk]

theorem TSubst.toRegion_liftn (n : ℕ) (σ : TSubst φ) : (σ.liftn n).toRegion = σ.toRegion.liftn n :=
  by funext m; simp only [RSubst.liftn, toRegion, liftn]; split <;> simp [Terminator.toRegion_lwk]

theorem TSubst.toRegion_vlift (σ : TSubst φ) : σ.vlift.toRegion = σ.toRegion.vlift := by
  funext n; simp [RSubst.vlift, toRegion, vlift, Terminator.toRegion_vwk]

theorem TSubst.toRegion_vliftn (n : ℕ) (σ : TSubst φ)
  : (σ.vliftn n).toRegion = σ.toRegion.vliftn n :=
  by funext m; simp [RSubst.vliftn, toRegion, vliftn, Terminator.toRegion_vwk]

instance : Coe (TSubst φ) (RSubst φ) := ⟨TSubst.toRegion⟩

theorem TSubst.coe_lift (σ : TSubst φ) : (σ.lift : RSubst φ) = (σ : RSubst φ).lift
  := σ.toRegion_lift

theorem TSubst.coe_liftn (n : ℕ) (σ : TSubst φ) : (σ.liftn n : RSubst φ) = (σ : RSubst φ).liftn n
  := σ.toRegion_liftn n

theorem TSubst.coe_vlift (σ : TSubst φ) : (σ.vlift : RSubst φ) = (σ : RSubst φ).vlift
  := σ.toRegion_vlift

theorem TSubst.coe_vliftn (n : ℕ) (σ : TSubst φ) : (σ.vliftn n : RSubst φ) = (σ : RSubst φ).vliftn n
  := σ.toRegion_vliftn n

-- TODO: Region.prepend

-- TODO: Region.ltimes

-- TODO: Block.toRegion == terminator.toRegion.prepend body

-- TODO: Block.toRegion_{vwk, vsubst, lwk}

-- TODO: BBRegion.toRegion

-- TODO: BBRegion.toRegion_{vwk, vsubst, lwk}

/-- Convert this `TRegion` to a `Region` -/
@[simp]
def TRegion.toRegion : TRegion φ → Region φ
  | let1 e t => Region.let1 e t.toRegion
  | let2 e t => Region.let2 e t.toRegion
  | cfg β n f => Region.cfg β.toRegion n (λ i => (f i).toRegion)

theorem TRegion.toRegion_vwk (ρ : ℕ → ℕ) (t : TRegion φ) : (t.vwk ρ).toRegion = t.toRegion.vwk ρ
  := by induction t generalizing ρ <;> simp [Terminator.toRegion_vwk, *]

theorem TRegion.toRegion_vsubst (σ : Subst φ) (t : TRegion φ)
  : (t.vsubst σ).toRegion = t.toRegion.vsubst σ
  := by induction t generalizing σ <;> simp [Terminator.toRegion_vsubst, *]

theorem TRegion.toRegion_lwk (ρ : ℕ → ℕ) (t : TRegion φ) : (t.lwk ρ).toRegion = t.toRegion.lwk ρ
  := by induction t generalizing ρ <;> simp [Terminator.toRegion_lwk, *]

theorem TRegion.toRegion_inj {t₁ t₂ : TRegion φ} : t₁.toRegion = t₂.toRegion ↔ t₁ = t₂ := by
  induction t₁ generalizing t₂ <;> cases t₂
  case cfg.cfg =>
    simp only [toRegion, Region.cfg.injEq, Terminator.toRegion_inj, cfg.injEq, and_congr_right_iff]
    intro hβ hn
    cases hβ; cases hn
    simp only [heq_eq_eq, Function.funext_iff, *]
  all_goals simp [Terminator.toRegion_inj, *]

theorem TRegion.toRegion_injective : Function.Injective (@TRegion.toRegion φ)
  := λ_ _ h => toRegion_inj.mp h

instance : Coe (TRegion φ) (Region φ) := ⟨TRegion.toRegion⟩

theorem TRegion.coe_toRegion_vwk (ρ : ℕ → ℕ) (t : TRegion φ)
  : (t.vwk ρ : Region φ) = (t : Region φ).vwk ρ := toRegion_vwk ρ t

theorem TRegion.coe_toRegion_vsubst (σ : Subst φ) (t : TRegion φ)
  : (t.vsubst σ : Region φ) = (t : Region φ).vsubst σ := toRegion_vsubst σ t

theorem TRegion.coe_toRegion_lwk (ρ : ℕ → ℕ) (t : TRegion φ)
  : (t.lwk ρ : Region φ) = (t : Region φ).lwk ρ := toRegion_lwk ρ t

-- TODO: Region.body

-- TODO: Region.tail

-- TODO: tail.ltimes body = id

/-- A control-flow graph with `length` entry-point regions -/
structure CFG (φ : Type) : Type where
  /-- The number of entry points to this CFG -/
  length : Nat
  /-- The number of exits for this CFG -/
  targets : Fin length → Region φ

-- TODO: ∅ cfg; represent as 0?

/-- Rename the variables in a `CFG` using `ρ` -/
def CFG.vwk (ρ : ℕ → ℕ) (G : CFG φ) : CFG φ where
  length := G.length
  targets := λ i => (G.targets i).vwk ρ

@[simp]
theorem CFG.vwk_id (G : CFG φ) : G.vwk id = G := by cases G; simp [vwk]

theorem CFG.vwk_comp (σ τ : ℕ → ℕ) (G : CFG φ) : G.vwk (σ ∘ τ) = (G.vwk τ).vwk σ
  := by cases G; simp only [CFG.vwk, Region.vwk_comp, *]

/-- Substitute the variables in a `CFG` using `σ` -/
def CFG.vsubst (σ : Subst φ) (G : CFG φ) : CFG φ where
  length := G.length
  targets := λ i => (G.targets i).vsubst σ

@[simp]
theorem CFG.vsubst_id (G : CFG φ) : G.vsubst Subst.id = G := by cases G; simp [vsubst]

theorem CFG.vsubst_comp (σ τ : Subst φ) (G : CFG φ) : G.vsubst (σ.comp τ) = (G.vsubst τ).vsubst σ
  := by cases G; simp only [CFG.vsubst, Region.vsubst_comp, *]

/-- Rename the labels in a `CFG` using `ρ` -/
def CFG.lwk (ρ : ℕ → ℕ) (G : CFG φ) : CFG φ where
  length := G.length
  targets := λ i => (G.targets i).lwk (Nat.liftnWk G.length ρ)

@[simp]
theorem CFG.lwk_id (G : CFG φ) : G.lwk id = G := by cases G; simp [lwk]

theorem CFG.lwk_comp (σ τ : ℕ → ℕ) (G : CFG φ) : G.lwk (σ ∘ τ) = (G.lwk τ).lwk σ
  := by cases G; simp only [CFG.lwk, Nat.liftnWk_comp, Region.lwk_comp, *]

-- TODO: CFG.vcomp (say Monoid...)

-- TODO: vcomp_assoc, vcomp_nil, nil_vcomp

-- TODO: CFG.{vwk, vsubst, lwk}_vcomp

-- TODO: CFG.hcomp (say AddMonoid...)

-- TODO: hcomp_nil, nil_hcomp, hcomp_assoc

-- TODO: CFG.{vwk, vsubst, lwk}_hcomp

-- TODO: BBCFG.toCFG

def TCFG.toCFG (G : TCFG φ) : CFG φ where
  length := G.length
  targets := λ i => (G.targets i).toRegion

instance : Coe (TCFG φ) (CFG φ) := ⟨TCFG.toCFG⟩

-- TODO: Region.tail'

-- TODO: Region.terminator_region

-- TODO: Region.cfg

-- TODO: normalize Region to TRegion; commutes with label-substitution

-- TODO: transitively, normalize Region to BBRegion; commutes with label-substitution

-- TODO: normalize TRegion to Region; commutes with label-substiution

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
