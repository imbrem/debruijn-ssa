import Discretion.Wk.Nat
import Discretion.Wk.Fin
import Discretion.Wk.Multiset
import Discretion.Wk.Multiset

import DeBruijnSSA.BinSyntax.Syntax.Definitions

namespace BinSyntax

/-! ### Term substitutions
 -/
namespace Term

/-- A substitution mapping variables to terms -/
def Subst (φ : Type _) := ℕ → Term φ -- TODO: Term.Subst?

/-- The identity substitution, which simply maps variables to themselves -/
def Subst.id : Subst φ := Term.var

@[simp]
theorem Subst.id_apply (n : ℕ) : @Subst.id φ n = Term.var n := rfl

/-- Lift a substitution under a binder -/
def Subst.lift (σ : Subst φ) : Subst φ
  | 0 => Term.var 0
  | n + 1 => (σ n).wk Nat.succ

@[simp]
theorem Subst.lift_zero (σ : Subst φ) : σ.lift 0 = Term.var 0 := rfl

@[simp]
theorem Subst.lift_succ (σ : Subst φ) (i : ℕ) : σ.lift (i + 1) = (σ i).wk Nat.succ := rfl

/-- Lift a substitution under `n` binders -/
def Subst.liftn (n : ℕ) (σ : Subst φ) : Subst φ
  := λm => if m < n then Term.var m else (σ (m - n)).wk (λv => v + n)

@[simp]
theorem Subst.liftn_zero (σ : Subst φ) : σ.liftn 0 = σ := by
  funext n
  simp only [liftn]
  split
  · rename_i H; cases H
  · exact (σ n).wk_id

theorem Subst.liftn_one (σ : Subst φ) : σ.liftn 1 = σ.lift := by funext m; cases m <;> rfl

theorem Subst.liftn_succ (n) (σ: Subst φ) : σ.liftn n.succ = (σ.liftn n).lift := by
  induction n with
  | zero => rw [σ.liftn_one, σ.liftn_zero]
  | succ n I => -- TODO: I'm sure this can be made _much_ cleaner...
    funext m
    rw [I]
    simp only [lift]
    split
    · rfl
    · simp only [liftn]
      split
      · split
        · rfl
        · split
          · rfl
          · rename_i H C; exact (C (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ H))).elim
      · split
        · rename_i H; simp_arith at H
        · split
          · rename_i C H; exact (C (Nat.succ_lt_succ (Nat.succ_lt_succ H))).elim
          · simp only [Term.wk_wk]
            apply congr
            apply congrArg
            funext v
            simp_arith
            simp_arith

theorem Subst.liftn_two (σ: Subst φ) : σ.liftn 2 = σ.lift.lift
  := by rw [Subst.liftn_succ, Subst.liftn_one]

theorem Subst.liftn_eq_iterate_lift_apply (n: ℕ) (σ: Subst φ) : σ.liftn n = (Subst.lift^[n] σ) := by
  induction n with
  | zero => exact σ.liftn_zero
  | succ n I => simp only [Function.iterate_succ_apply', Subst.liftn_succ, *]

theorem Subst.liftn_eq_iterate_lift (n: ℕ) : Subst.liftn n = (@Subst.lift φ)^[n] := by
  funext σ
  rw [liftn_eq_iterate_lift_apply]

theorem Subst.liftn_succ' (n) (σ: Subst φ) : σ.liftn n.succ = σ.lift.liftn n := by
  simp [liftn_eq_iterate_lift]

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

theorem Subst.liftn_liftn (n m: ℕ) (σ: Subst φ): (σ.liftn n).liftn m = σ.liftn (m + n)
  := by simp [liftn_add]

theorem Subst.liftn_liftn' (n m: ℕ) (σ: Subst φ): (σ.liftn n).liftn m = σ.liftn (n + m)
  := by simp [liftn_liftn, Nat.add_comm]

/-- Substitute the free variables in a `Term` using `σ` -/
@[simp]
def subst (σ : Subst φ) : Term φ → Term φ
| var x => σ x
| op f x => op f (subst σ x)
| let1 a e => let1 (subst σ a) (subst σ.lift e)
| pair x y => pair (subst σ x) (subst σ y)
| unit => unit
| let2 a e => let2 (subst σ a) (subst (σ.liftn 2) e)
| inl a => inl (subst σ a)
| inr a => inr (subst σ a)
| case a l r => case (subst σ a) (subst σ.lift l) (subst σ.lift r)
| abort a => abort (subst σ a)

@[simp]
theorem subst_id (t : Term φ) : t.subst Subst.id = t := by induction t <;> simp [*]

theorem Subst.ext_subst (σ τ : Subst φ) (h : ∀t : Term φ, t.subst σ = t.subst τ) : ∀n, σ n = τ n
  := λn => h (var n)

-- i.e. subst is a faithful functor
theorem subst_injective : Function.Injective (@subst φ)
  := λσ τ h => funext (λn => σ.ext_subst τ (λ_ => h ▸ rfl) n)

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

theorem subst_fromWk_apply (ρ : ℕ -> ℕ) (t : Term φ) : t.subst (Subst.fromWk ρ) = t.wk ρ := by
  induction t generalizing ρ <;> simp [Subst.fromWk_liftn, Term.Subst.fromWk_lift,  *]

theorem subst_fromWk (ρ : ℕ -> ℕ) : @Term.subst φ (Subst.fromWk ρ) = Term.wk ρ
  := funext (subst_fromWk_apply ρ)

theorem subst_comp_fromWk : @Term.subst φ ∘ Subst.fromWk = Term.wk
  := funext subst_fromWk

theorem subst_liftn (n : ℕ) (σ : Subst φ) (t : Term φ)
    : (t.wk (Nat.liftnWk n Nat.succ)).subst (σ.liftn (n + 1))
      = (t.subst (σ.liftn n)).wk (Nat.liftnWk n Nat.succ)
  := by induction t generalizing σ n with
  | var =>
    --TODO: how should this be factored?
    simp only [wk, subst, Nat.liftnWk, Subst.liftn]
    split
    · split
      · simp [Nat.liftnWk, *]
      · rename_i H C; exact (C (Nat.le_step H)).elim
    · rename_i C
      simp_arith only [ite_false, wk_wk]
      apply congr
      · apply congrArg
        funext v
        simp_arith [Function.comp_apply, Zero.zero, Nat.liftnWk]
      · simp [Nat.succ_add, Nat.succ_sub_succ, Nat.add_sub_assoc]
  | _ => simp [
    <-Subst.liftn_succ, <-Nat.liftnWk_succ_apply', <-Nat.liftnWk_add_apply', Subst.liftn_liftn', *]

theorem subst_iterate_lift (n : ℕ) (σ : Subst φ) (t : Term φ)
  : (t.wk (Nat.liftWk^[n] Nat.succ)).subst (Subst.lift^[n + 1] σ)
    = (t.subst (Subst.lift^[n] σ)).wk (Nat.liftWk^[n] Nat.succ)
  := by simp only [<-Subst.liftn_eq_iterate_lift, <-Nat.liftnWk_eq_iterate_liftWk, subst_liftn]

theorem subst_lift (t : Term φ) (σ : Subst φ)
  : (t.wk Nat.succ).subst (σ.lift) = (t.subst σ).wk Nat.succ := t.subst_iterate_lift 0 σ

/-- Compose two substitutions on terms to yield another -/
def Subst.comp (σ τ : Subst φ): Subst φ
  | n => (τ n).subst σ

theorem Subst.lift_comp (σ τ : Subst φ) : (σ.comp τ).lift = σ.lift.comp τ.lift := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [lift, comp, Term.subst_lift]

theorem Subst.iterate_lift_comp
  : (n : ℕ) -> ∀σ τ : Subst φ, Subst.lift^[n] (σ.comp τ)
    = (Subst.lift^[n] σ).comp (Subst.lift^[n] τ)
  | 0, σ, τ => rfl
  | n + 1, σ, τ => by simp [Subst.lift_comp, iterate_lift_comp n]

theorem Subst.liftn_comp (n : ℕ) (σ τ : Subst φ)
  : (σ.comp τ).liftn n = (σ.liftn n).comp (τ.liftn n)
  := by rw [liftn_eq_iterate_lift, iterate_lift_comp]

theorem subst_comp (σ τ : Subst φ) (t : Term φ) : t.subst (σ.comp τ) = (t.subst τ).subst σ
  := by induction t generalizing σ τ with
  | var => rfl
  | _ => simp [subst, Subst.lift_comp, Subst.liftn_comp, *]

theorem subst_subst (σ τ : Subst φ) (t : Term φ)
  : (t.subst τ).subst σ = t.subst (σ.comp τ) := by rw [subst_comp]

@[simp]
theorem Subst.comp_id (σ : Subst φ) : σ.comp Subst.id = σ := by funext n; rfl

@[simp]
theorem Subst.id_comp (σ : Subst φ) : Subst.id.comp σ = σ := by funext n; simp [comp]

theorem Subst.comp_assoc (σ τ ρ : Subst φ) : (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) := by
  funext n
  simp only [comp, Function.comp_apply, subst_comp]

/-- Substitute a term for the smallest variable, bumping the rest downwards -/
def subst0 (t : Term φ) : Subst φ
  | 0 => t
  | n + 1 => var n

@[simp]
theorem subst0_zero (t : Term φ) : subst0 t 0 = t := rfl

@[simp]
theorem subst0_succ (t : Term φ) (n : ℕ) : subst0 t (n + 1) = var n := rfl

theorem subst_subst0_wk (e s : Term φ) (ρ)
  : (e.subst s.subst0).wk ρ = (e.wk (Nat.liftWk ρ)).subst (s.wk ρ).subst0 := by
  simp only [<-subst_fromWk_apply, subst_subst]
  congr
  funext n
  cases n <;> rfl

theorem subst0_comp_wk (s : Term φ)
  : (Subst.fromWk ρ).comp (subst0 s) = (s.wk ρ).subst0.comp (Subst.fromWk (Nat.liftWk ρ))
  := by funext n; cases n <;> simp [Subst.comp, subst_fromWk_apply]

theorem subst0_var0 : @subst0 φ (var 0) = Subst.fromWk Nat.pred := by funext n; cases n <;> rfl

@[simp]
theorem wk_succ_comp_subst0 (e : Term φ) : e.subst0.comp (Subst.fromWk Nat.succ) = Subst.id
  := by funext n; cases n <;> rfl

@[simp]
theorem wk_succ_subst_subst0 (e s : Term φ) : (e.wk Nat.succ).subst s.subst0 = e := by
  rw [<-subst_fromWk_apply, <-subst_comp, wk_succ_comp_subst0, subst_id]

@[simp]
theorem subst0_wk0 (e s : Term φ) : e.wk0.subst s.subst0 = e := wk_succ_subst_subst0 e s

@[simp]
theorem wk1_subst0_var0 (e : Term φ) : e.wk1.subst (var 0).subst0 = e := by
  rw [subst0_var0, subst_fromWk, wk1, wk_wk]
  apply Eq.trans _ e.wk_id
  congr
  funext i
  cases i <;> rfl

@[simp]
theorem wk1_subst0_var0' (e : Term φ) : (e.wk (Nat.liftWk Nat.succ)).subst (var 0).subst0 = e
  := e.wk1_subst0_var0

/-- Substitute a term for the `n`th variable, bumping those above it downwards -/
def substn (n : ℕ) (t : Term φ) : Subst φ := λm =>
  if m < n then var m else if m = n then t else var (m - 1)

theorem substn_zero (t : Term φ) : substn 0 t = subst0 t := by
  funext n; cases n <;> rfl

theorem substn_succ (n : ℕ) (t : Term φ)
  : substn (n + 1) (t.wk Nat.succ) = (substn n t).lift := by
  funext m
  cases m with
  | zero => simp [substn]
  | succ m =>
    simp only [substn, Nat.add_lt_add_iff_right, add_left_inj, Nat.add_sub_cancel, Subst.lift]
    split
    case isTrue => rfl
    case isFalse h =>
      split
      case isTrue => rfl
      case isFalse h' =>
        simp only [wk, Nat.succ_eq_add_one, var.injEq]
        rw [Nat.sub_add_cancel]
        exact Nat.succ_le_of_lt $ Nat.lt_of_le_of_lt
          (Nat.zero_le n)
          (Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) (Ne.symm h'))

theorem substn_add (n m : ℕ) (t : Term φ)
  : substn (n + m) (t.wk (· + m)) = (substn n t).liftn m := by
  induction m with
  | zero => simp
  | succ m I => rw [Subst.liftn_succ, <-I, <-substn_succ, <-Nat.add_assoc, wk_wk]; rfl

theorem substn_add_right (n m : ℕ) (t : Term φ)
  : substn (m + n) (t.wk (· + m)) = (substn n t).liftn m := Nat.add_comm _ _ ▸ substn_add n m t

@[simp]
theorem substn_n (n : ℕ) (t : Term φ) : substn n t n = t := by simp [substn]

theorem subst_substn_wk (e s : Term φ) (ρ) (n)
  : (e.subst (s.substn n)).wk (Nat.liftnWk n ρ)
  = (e.wk (Nat.liftnWk (n + 1) ρ)).subst ((s.wk (Nat.liftnWk n ρ)).substn n) := by
  simp only [<-subst_fromWk_apply, subst_subst]
  congr
  funext k
  simp only [Subst.fromWk, Subst.comp, wk, substn, subst, Nat.liftnWk]
  split
  case isTrue h =>
    have h' : k < n + 1 := Nat.lt_succ_of_lt h
    simp only [wk, h, h', Nat.liftnWk, ↓reduceIte]
    simp only [subst, Function.comp_apply, Nat.liftnWk, var.injEq, ite_eq_left_iff, not_lt]
    exact λhk => (Nat.not_le_of_lt h hk).elim
  case isFalse h =>
    split
    case isTrue h =>
      cases h
      simp
    case isFalse h' =>
      have hn : ¬k ≤ n := match Nat.eq_or_lt_of_not_lt h with
        | Or.inl h => (h' h).elim
        | Or.inr h => Nat.not_le_of_lt h
      have h' : ¬k < n + 1 := match Nat.eq_or_lt_of_not_lt h with
        | Or.inl h => (h' h).elim
        | Or.inr h => Nat.not_lt_of_le h
      have h'' : ¬k - 1 < n := λc => (hn (Nat.le_of_pred_lt c)).elim
      have hρ : ρ (k - 1 - n) = ρ (k - (n + 1)) := by simp [Nat.add_comm n 1, Nat.sub_add_eq]
      simp_arith [h', h'', Nat.liftnWk, hρ]

theorem liftn_subst0 (n : ℕ) (t : Term φ) : t.subst0.liftn n = (t.wk (· + n)).substn n := by
  induction n with
  | zero => simp [substn_zero]
  | succ n I =>
    rw [Subst.liftn_succ, I]
    have h : (· + (n + 1)) = Nat.succ ∘ (· + n) := by funext m; simp_arith
    rw [h, <-Term.wk_wk, substn_succ]

theorem subst_liftn_subst0_wk (e s : Term φ) (ρ n)
  : (e.subst (s.subst0.liftn n)).wk (Nat.liftnWk n ρ)
  = (e.wk (Nat.liftnWk (n + 1) ρ)).subst ((s.wk ρ).subst0.liftn n)
  := by
  simp only [liftn_subst0, subst_substn_wk, wk_wk]
  congr
  apply congrArg
  congr
  funext k
  simp [Nat.liftnWk]

/-- Substitute a term for the `n`th variable, leaving the rest unchanged -/
def alpha (n : ℕ) (t : Term φ) : Subst φ := Function.update Subst.id n t

@[simp]
theorem wk1_comp_subst0 (e : Term φ)
  : e.subst0.comp (Subst.fromWk (Nat.wkn 1)) = e.alpha 0
  := by funext n; cases n <;> rfl

@[simp]
theorem liftWk_succ_comp_subst0 (e : Term φ)
  : e.subst0.comp (Subst.fromWk (Nat.liftWk Nat.succ)) = e.alpha 0
  := by funext n; cases n <;> rfl

@[simp]
theorem wkn_comp_substn_succ (n : ℕ) (e : Term φ)
  : (e.substn n).comp (Subst.fromWk (Nat.wkn (n + 1))) = e.alpha n := by
  funext i
  simp only [Subst.comp, subst, substn, Nat.wkn, alpha, Function.update, eq_rec_constant,
    Subst.id_apply, dite_eq_ite, Nat.lt_succ_iff]
  split
  case isTrue h =>
    split
    case isTrue h' => simp [Nat.ne_of_lt h']
    case isFalse h' => simp [Nat.le_antisymm h (Nat.le_of_not_lt h')]
  case isFalse h =>
    have c : ¬(i + 1 < n) := λc => h (Nat.le_of_lt (Nat.lt_trans (by simp) c))
    have c' : i + 1 ≠ n := λc => by cases c; simp at h
    have c'' : i ≠ n := λc => h (Nat.le_of_eq c)
    simp [c, c', c'']

@[simp]
theorem alpha_var : (var n).alpha n = @Subst.id φ := by funext n; simp [alpha, Subst.id]

theorem wk0_subst {σ : Subst φ} {e : Term φ}
  : (e.subst σ).wk0 = e.wk0.subst σ.lift := (subst_lift e σ).symm

theorem wk1_subst_lift {σ : Subst φ} {e : Term φ}
  : (e.subst σ.lift).wk1 = e.wk1.subst σ.lift.lift := by
  simp only [wk1, <-subst_fromWk, subst_subst]
  congr
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    simp only [
      Subst.comp, BinSyntax.Term.subst, Nat.liftWk_succ, Nat.succ_eq_add_one, Subst.lift_succ,
      wk_wk, subst_fromWk, Nat.liftWk_succ_comp_succ
    ]
    rfl

theorem wk2_subst_lift_lift {σ : Subst φ} {e : Term φ}
  : (e.subst σ.lift.lift).wk2 = e.wk2.subst σ.lift.lift.lift := by
  simp only [wk2, <-subst_fromWk, subst_subst]
  congr
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k =>
      simp_arith only [
        Subst.comp, BinSyntax.Term.subst, Nat.liftWk_succ, Nat.succ_eq_add_one, Subst.lift_succ,
        wk_wk, subst_fromWk, Nat.liftWk_succ_comp_succ, Nat.liftnWk, ↓reduceIte
      ]
      rfl

theorem swap01_subst_lift_lift {σ : Subst φ} {e : Term φ}
  : (e.subst σ.lift.lift).swap01 = e.swap01.subst σ.lift.lift := by
  simp only [swap01, <-subst_fromWk, subst_subst]
  congr
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k =>
      simp_arith only [
        Subst.comp, BinSyntax.Term.subst, Nat.liftWk_succ, Nat.succ_eq_add_one, Subst.lift_succ,
        wk_wk, subst_fromWk, Nat.liftWk_succ_comp_succ, Nat.liftnWk, ↓reduceIte, Nat.swap0
      ]
      rfl

theorem swap02_subst_lift_lift_lift {σ : Subst φ} {e : Term φ}
  : (e.subst σ.lift.lift.lift).swap02 = e.swap02.subst σ.lift.lift.lift := by
  simp only [swap02, <-subst_fromWk, subst_subst]
  congr
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => rfl
      | succ k =>
        simp_arith only [
          Subst.comp, BinSyntax.Term.subst, Nat.liftWk_succ, Nat.succ_eq_add_one, Subst.lift_succ,
          wk_wk, subst_fromWk, Nat.liftWk_succ_comp_succ, Nat.liftnWk, ↓reduceIte, Nat.swap0
        ]
        rfl

end Term

/-- Substitute the free variables in a body -/
@[simp]
def Body.subst (σ : Term.Subst φ) : Body φ → Body φ
  | nil => nil
  | let1 e t => let1 (e.subst σ) (t.subst σ.lift)
  | let2 e t => let2 (e.subst σ) (t.subst (σ.liftn 2))

@[simp]
theorem Body.subst_id (b : Body φ) : b.subst Term.Subst.id = b := by
  induction b <;> simp [Term.Subst.lift_id, Term.Subst.liftn_id, *]

theorem Body.subst_comp (σ τ : Term.Subst φ) (b : Body φ)
  : b.subst (σ.comp τ) = (b.subst τ).subst σ := by
  induction b generalizing σ τ
  <;> simp [Term.subst_comp, Term.Subst.lift_comp, Term.Subst.liftn_comp, *]

@[simp]
theorem Body.num_defs_subst (σ : Term.Subst φ) (b : Body φ)
  : (b.subst σ).num_defs = b.num_defs := by
  induction b generalizing σ <;> simp [*]

/-- Substitute the free variables in a `Terminator` using `σ` -/
@[simp]
def Terminator.vsubst (σ : Term.Subst φ) : Terminator φ → Terminator φ
  | br ℓ e => br ℓ (e.subst σ)
  | case e s t => case (e.subst σ) (vsubst σ.lift s) (vsubst σ.lift t)

@[simp]
theorem Terminator.vsubst_id (r : Terminator φ) : r.vsubst Term.Subst.id = r := by
  induction r <;> simp [*]

theorem Terminator.vsubst_vsubst (σ τ : Term.Subst φ) (r : Terminator φ)
  : (r.vsubst τ).vsubst σ = r.vsubst (σ.comp τ) := by
  induction r generalizing σ τ
  <;> simp [Term.subst_comp, Term.Subst.lift_comp, Term.Subst.liftn_comp, *]

theorem Terminator.ext_vsubst (σ τ : Term.Subst φ)
  (h : ∀t : Terminator φ, t.vsubst σ = t.vsubst τ) : ∀n, σ n = τ n
  := λn => by
    have h' := h (br 0 (Term.var n))
    simp at h'
    exact h'

-- i.e. vsubst is a faithful functor
theorem Terminator.vsubst_injective : Function.Injective (@Terminator.vsubst φ)
  := λσ τ h => funext (λn => Terminator.ext_vsubst σ τ (λ_ => h ▸ rfl) n)

theorem Terminator.vsubst_fromWk_apply (ρ : ℕ -> ℕ) (r : Terminator φ)
  : r.vsubst (Term.Subst.fromWk ρ) = r.vwk ρ := by
  induction r generalizing ρ
  <;> simp [Term.subst_fromWk_apply, Term.Subst.fromWk_liftn, Term.Subst.fromWk_lift, *]

theorem Terminator.vsubst_fromWk (ρ : ℕ -> ℕ)
  : vsubst (Term.Subst.fromWk ρ) = @vwk φ ρ := funext (vsubst_fromWk_apply ρ)

theorem Terminator.vsubst_comp_fromWk
  : @vsubst φ ∘ Term.Subst.fromWk = @vwk φ := funext vsubst_fromWk

theorem Terminator.lwk_vsubst (σ : Term.Subst φ) (ρ : ℕ -> ℕ) (r : Terminator φ)
  : (r.vsubst σ).lwk ρ = (r.lwk ρ).vsubst σ := by induction r generalizing σ <;> simp [*]

theorem Terminator.vsubst_lwk (σ : Term.Subst φ) (ρ : ℕ -> ℕ) (r : Terminator φ)
  : (r.lwk ρ).vsubst σ = (r.vsubst σ).lwk ρ := Eq.symm $ Terminator.lwk_vsubst σ ρ r

@[simp]
theorem Terminator.vwk_succ_vsubst_subst0 (t : Terminator φ) (s : Term φ)
  : (t.vwk Nat.succ).vsubst s.subst0 = t := by
  rw [<-vsubst_fromWk_apply, vsubst_vsubst, Term.wk_succ_comp_subst0, vsubst_id]

/-- Substitute the free variables in a basic block -/
@[simp]
def Block.vsubst (σ : Term.Subst φ) (β : Block φ) : Block φ where
  body := β.body.subst σ
  terminator := β.terminator.vsubst (σ.liftn β.body.num_defs)

@[simp]
theorem Block.vsubst_id (β : Block φ) : β.vsubst Term.Subst.id = β := by simp

theorem Block.vsubst_vsubst (σ τ : Term.Subst φ) (β : Block φ)
  : (β.vsubst τ).vsubst σ = β.vsubst (σ.comp τ)
  := by simp [
    Body.subst_comp, Body.num_defs_subst, Term.Subst.liftn_comp, Terminator.vsubst_vsubst, *]

/-- Substitute the free variables in a region -/
@[simp]
def BBRegion.vsubst (σ : Term.Subst φ) : BBRegion φ → BBRegion φ
  | cfg β n f => cfg (β.vsubst σ) n (λ i => (f i).vsubst (σ.liftn (β.body.num_defs + 1)))

@[simp]
theorem BBRegion.vsubst_id (r : BBRegion φ) : r.vsubst Term.Subst.id = r := by
  induction r; simp [*]

theorem BBRegion.vsubst_vsubst (σ τ : Term.Subst φ) (r : BBRegion φ)
  : (r.vsubst τ).vsubst σ = r.vsubst (σ.comp τ) := by
  induction r generalizing σ τ
  simp [Body.subst_comp, Body.num_defs_subst, Term.Subst.liftn_comp, Terminator.vsubst_vsubst, *]

/-- Substitute the free variables in a control-flow graph -/
@[simp]
def BBCFG.vsubst (σ : Term.Subst φ) (cfg : BBCFG φ) : BBCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).vsubst σ

@[simp]
theorem BBCFG.vsubst_id (cfg : BBCFG φ) : cfg.vsubst Term.Subst.id = cfg := by
  cases cfg; simp [*]

theorem BBCFG.vsubst_vsubst (σ τ : Term.Subst φ) (cfg : BBCFG φ)
  : (cfg.vsubst τ).vsubst σ = cfg.vsubst (σ.comp τ) := by
  cases cfg; simp [BBRegion.vsubst_vsubst, *]

/-- Substitute the free variables in a region -/
@[simp]
def TRegion.vsubst (σ : Term.Subst φ) : TRegion φ → TRegion φ
  | let1 e t => let1 (e.subst σ) (t.vsubst σ.lift)
  | let2 e t => let2 (e.subst σ) (t.vsubst (σ.liftn 2))
  | cfg β n f => cfg (β.vsubst σ) n (λ i => (f i).vsubst σ.lift)

@[simp]
theorem TRegion.vsubst_id (r : TRegion φ) : r.vsubst Term.Subst.id = r := by
  induction r <;> simp [TRegion.vsubst, Term.Subst.lift_id, Term.Subst.liftn_id, *]

theorem TRegion.vsubst_vsubst (σ τ : Term.Subst φ) (r : TRegion φ)
  : (r.vsubst τ).vsubst σ = r.vsubst (σ.comp τ) := by
  induction r generalizing σ τ
  <;> simp [Term.subst_comp, Terminator.vsubst_vsubst, Term.Subst.lift_comp, Term.Subst.liftn_comp, *]

def TCFG.vsubst (σ : Term.Subst φ) (cfg : TCFG φ) : TCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).vsubst σ

@[simp]
theorem TCFG.vsubst_id (cfg : TCFG φ) : cfg.vsubst Term.Subst.id = cfg := by
  cases cfg; simp [TCFG.vsubst, *]

theorem TCFG.vsubst_vsubst (σ τ : Term.Subst φ) (cfg : TCFG φ)
  : (cfg.vsubst τ).vsubst σ = cfg.vsubst (σ.comp τ) := by
  cases cfg; simp [TCFG.vsubst, TRegion.vsubst_vsubst, *]

/-- Substitute the free variables in a `Region` using `σ` -/
@[simp]
def Region.vsubst (σ : Term.Subst φ) : Region φ → Region φ
  | br n e => br n (e.subst σ)
  | case e s t => case (e.subst σ) (vsubst σ.lift s) (vsubst σ.lift t)
  | let1 e t => let1 (e.subst σ) (vsubst σ.lift t)
  | let2 e t => let2 (e.subst σ) (vsubst (σ.liftn 2) t)
  | cfg β n f => cfg (vsubst σ β) n (λ i => (f i).vsubst σ.lift)

@[simp]
theorem Region.vsubst_id (r : Region φ) : r.vsubst Term.Subst.id = r := by
  induction r <;> simp [*]

theorem Region.vsubst_id' (r : Region φ) (h : σ = Term.Subst.id) : r.vsubst σ = r := by
  cases h; simp

theorem Region.vsubst_comp_apply (σ τ : Term.Subst φ) (r : Region φ)
  : r.vsubst (σ.comp τ) = (r.vsubst τ).vsubst σ := by
  induction r generalizing σ τ
  <;> simp [Term.subst_comp, Term.Subst.lift_comp, Term.Subst.liftn_comp, *]

theorem Region.vsubst_vsubst (σ τ : Term.Subst φ) (r : Region φ)
  : (r.vsubst τ).vsubst σ = r.vsubst (σ.comp τ) := by
  induction r generalizing σ τ
  <;> simp [Term.subst_comp, Term.Subst.lift_comp, Term.Subst.liftn_comp, *]

theorem Region.vsubst_comp (σ τ : Term.Subst φ)
  : vsubst σ ∘ vsubst τ = vsubst (σ.comp τ) := by
  funext r; simp [vsubst_vsubst]

theorem Region.ext_vsubst (σ τ : Term.Subst φ)
  (h : ∀t : Region φ, t.vsubst σ = t.vsubst τ) : ∀n, σ n = τ n
  := λn => by
    have h' := h (br 0 (Term.var n))
    simp at h'
    exact h'

theorem Region.vsubst_cfg (σ : Term.Subst φ) (β : Region φ) (n : ℕ) (G : Fin n -> Region φ)
  : (cfg β n G).vsubst σ = cfg (β.vsubst σ) n (λi => (G i).vsubst σ.lift) := rfl

theorem Region.vsubst_cfg1 (σ : Term.Subst φ) (β : Region φ) (G : Region φ)
  : (cfg β 1 (Fin.elim1 G)).vsubst σ = cfg (β.vsubst σ) 1 (Fin.elim1 (G.vsubst σ.lift)) := by
  simp only [vsubst, cfg.injEq, heq_eq_eq, true_and]
  funext i; cases i using Fin.elim1; rfl

-- i.e. vsubst is a faithful functor
theorem Region.vsubst_injective : Function.Injective (@Region.vsubst φ)
  := λσ τ h => funext (λn => Region.ext_vsubst σ τ (λ_ => h ▸ rfl) n)

theorem Region.vsubst_fromWk_apply (ρ : ℕ -> ℕ) (r : Region φ)
  : r.vsubst (Term.Subst.fromWk ρ) = r.vwk ρ := by
  induction r generalizing ρ
  <;> simp [Term.subst_fromWk_apply, Term.Subst.fromWk_liftn, Term.Subst.fromWk_lift, *]

theorem Region.vsubst_fromWk (ρ : ℕ -> ℕ)
  : vsubst (Term.Subst.fromWk ρ) = @vwk φ ρ := funext (vsubst_fromWk_apply ρ)

theorem Region.vsubst0_var0_vwk1 (r : Region φ)
  : r.vwk1.vsubst (Term.subst0 (Term.var 0)) = r := by
  rw [vwk1, <-vsubst_fromWk, vsubst_vsubst, vsubst_id']
  funext k; cases k <;> rfl

theorem Region.vsubst_comp_fromWk
  : @vsubst φ ∘ Term.Subst.fromWk = @vwk φ := funext vsubst_fromWk

theorem Region.vsubst0_var0_comp_vwk1
  : vsubst (Term.subst0 (Term.var 0)) ∘ vwk1 (φ := φ) = id
  := funext vsubst0_var0_vwk1

theorem Region.lwk_vsubst (σ : Term.Subst φ) (ρ : ℕ -> ℕ) (r : Region φ)
  : (r.vsubst σ).lwk ρ = (r.lwk ρ).vsubst σ := by induction r generalizing σ ρ <;> simp [*]

theorem Region.vsubst_lwk (σ : Term.Subst φ) (ρ : ℕ -> ℕ) (r : Region φ)
  : (r.lwk ρ).vsubst σ = (r.vsubst σ).lwk ρ := Eq.symm $ Region.lwk_vsubst σ ρ r

theorem Region.lwk1_vsubst (σ : Term.Subst φ) (r : Region φ)
  : (r.vsubst σ).lwk1 = (r.lwk1).vsubst σ := by rw [lwk1, lwk_vsubst]

theorem Region.vsubst_lwk1 (σ : Term.Subst φ) (r : Region φ)
  : (r.lwk1).vsubst σ = (r.vsubst σ).lwk1 := by rw [lwk1, vsubst_lwk]

/-- Substitute the free variables in a `CFG` using `σ` -/
def CFG.vsubst (σ : Term.Subst φ) (G : CFG φ) : CFG φ where
  length := G.length
  targets := λ i => (G.targets i).vsubst σ

@[simp]
theorem CFG.vsubst_id (G : CFG φ) : G.vsubst Term.Subst.id = G := by cases G; simp [vsubst]

theorem CFG.vsubst_comp_apply (σ τ : Term.Subst φ) (G : CFG φ) : G.vsubst (σ.comp τ) = (G.vsubst τ).vsubst σ
  := by cases G; simp only [CFG.vsubst, Region.vsubst_comp_apply, *]
