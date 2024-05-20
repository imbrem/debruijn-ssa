import Discretion.Wk.Fun
import Discretion.Wk.Multiset
import Discretion.Wk.Multiset

import DeBruijnSSA.BinSyntax.Syntax.Definitions

namespace BinSyntax

/-! ### Term substitutions
 -/
namespace Term

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
          . simp only [<-Term.wk_wk]
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

theorem Subst.liftn_add_apply (n m: ℕ) (σ: Subst φ): (σ.liftn n).liftn m = σ.liftn (m + n)
  := by simp [liftn_add]

/-- Substitute the free variables in a `Term` using `σ` -/
@[simp]
def subst (σ : Subst φ) : Term φ → Term φ
| var x => σ x
| op f x => op f (subst σ x)
| pair x y => pair (subst σ x) (subst σ y)
| unit => unit
| inl a => inl (subst σ a)
| inr a => inr (subst σ a)

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

theorem subst_wk (ρ : ℕ -> ℕ) (t : Term φ) : t.subst (Subst.fromWk ρ) = t.wk ρ := by
  induction t <;> simp [Subst.fromWk_liftn, *]

theorem subst_liftn (n : ℕ) (σ : Subst φ) (t : Term φ)
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
      simp_arith only [ite_false, <-wk_wk]
      apply congr
      . apply congrArg
        funext v
        simp_arith [Function.comp_apply, Zero.zero, Nat.liftnWk]
      . simp [Nat.succ_add, Nat.succ_sub_succ, Nat.add_sub_assoc]
  | _ => simp [*]

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
  := by induction t <;> simp only [subst, Subst.liftn_comp, Subst.comp, *]

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
  : (e.subst s.subst0).wk ρ = (e.wk (Nat.liftWk ρ)).subst (s.wk ρ).subst0
  := by induction e with
  | var n => cases n <;> rfl
  | _ => simp [*]

theorem subst0_comp_wk (s : Term φ)
  : (Subst.fromWk ρ).comp (subst0 s) = (s.wk ρ).subst0.comp (Subst.fromWk (Nat.liftWk ρ))
  := by funext n; cases n <;> simp [Subst.comp, subst_wk]

@[simp]
theorem wk_succ_comp_subst0 (e : Term φ) : e.subst0.comp (Subst.fromWk Nat.succ) = Subst.id
  := by funext n; cases n <;> rfl

@[simp]
theorem wk_succ_subst_subst0 (e s : Term φ) : (e.wk Nat.succ).subst s.subst0 = e := by
  rw [<-subst_wk, <-subst_comp, wk_succ_comp_subst0, subst_id]

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
    simp only [substn, add_lt_add_iff_right, add_left_inj, add_tsub_cancel_right, Subst.lift]
    split
    case inl => rfl
    case inr h =>
      split
      case inl => rfl
      case inr h' =>
        simp only [wk, Nat.succ_eq_add_one, var.injEq]
        rw [Nat.sub_add_cancel]
        exact Nat.succ_le_of_lt $ Nat.lt_of_le_of_lt
          (Nat.zero_le n)
          (Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) (Ne.symm h'))

@[simp]
theorem substn_n (n : ℕ) (t : Term φ) : substn n t n = t := by simp [substn]

theorem subst_substn_wk (e s : Term φ) (ρ) (n)
  : (e.subst (s.substn n)).wk (Nat.liftnWk n ρ)
  = (e.wk (Nat.liftnWk (n + 1) ρ)).subst ((s.wk (Nat.liftnWk n ρ)).substn n)
  := by induction e with
  | var k =>
    simp only [wk, substn, subst, Nat.liftnWk]
    split
    case inl h =>
      have h' : k < n + 1 := Nat.lt_succ_of_lt h
      simp only [wk, h, h', Nat.liftnWk, ↓reduceIte]
    case inr h =>
      split
      case inl h =>
        cases h
        simp
      case inr h' =>
        have hn : ¬k ≤ n := match Nat.eq_or_lt_of_not_lt h with
          | Or.inl h => (h' h).elim
          | Or.inr h => Nat.not_le_of_lt h
        have h' : ¬k < n + 1 := match Nat.eq_or_lt_of_not_lt h with
          | Or.inl h => (h' h).elim
          | Or.inr h => Nat.not_lt_of_le h
        have h'' : ¬k - 1 < n := λc => (hn (Nat.le_of_pred_lt c)).elim
        have hρ : ρ (k - 1 - n) = ρ (k - (n + 1)) := by simp [Nat.add_comm n 1, Nat.sub_add_eq]
        simp_arith [h', h'', Nat.liftnWk, hρ]
  | _ => simp [*]

theorem liftn_subst0 (n : ℕ) (t : Term φ) : t.subst0.liftn n = (t.wk (· + n)).substn n := by
  induction n with
  | zero => simp [substn_zero]
  | succ n I =>
    rw [Subst.liftn_succ, I]
    have h : (· + (n + 1)) = Nat.succ ∘ (· + n) := by funext m; simp_arith
    rw [h, Term.wk_wk, substn_succ]

theorem subst_liftn_subst0_wk (e s : Term φ) (ρ n)
  : (e.subst (s.subst0.liftn n)).wk (Nat.liftnWk n ρ)
  = (e.wk (Nat.liftnWk (n + 1) ρ)).subst ((s.wk ρ).subst0.liftn n)
  := by
  simp only [liftn_subst0, subst_substn_wk, <-wk_wk]
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
  case inl h =>
    split
    case inl h' => simp [Nat.ne_of_lt h']
    case inr h' => simp [Nat.le_antisymm h (Nat.le_of_not_lt h')]
  case inr h =>
    have c : ¬(i + 1 < n) := λc => h (Nat.le_of_lt (Nat.lt_trans (by simp) c))
    have c' : i + 1 ≠ n := λc => by cases c; simp at h
    have c'' : i ≠ n := λc => h (Nat.le_of_eq c)
    simp [c, c', c'']

@[simp]
theorem alpha_var : (var n).alpha n = @Subst.id φ := by funext n; simp [alpha, Subst.id]

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

theorem Terminator.vsubst_comp (σ τ : Term.Subst φ) (r : Terminator φ)
  : r.vsubst (σ.comp τ) = (r.vsubst τ).vsubst σ := by
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

theorem Terminator.vsubst_wk (ρ : ℕ -> ℕ) (r : Terminator φ)
  : r.vsubst (Term.Subst.fromWk ρ) = r.vwk ρ := by
  induction r generalizing ρ
  <;> simp [Term.subst_wk, Term.Subst.fromWk_liftn, Term.Subst.fromWk_lift, *]

theorem Terminator.vsubst_fromWk (ρ : ℕ -> ℕ)
  : vsubst (Term.Subst.fromWk ρ) = @vwk φ ρ := funext (vsubst_wk ρ)

theorem Terminator.vsubst_lwk_comm (σ : Term.Subst φ) (ρ : ℕ -> ℕ) (r : Terminator φ)
  : (r.vsubst σ).lwk ρ = (r.lwk ρ).vsubst σ := by induction r generalizing σ <;> simp [*]

@[simp]
theorem Terminator.vwk_succ_vsubst_subst0 (t : Terminator φ) (s : Term φ)
  : (t.vwk Nat.succ).vsubst s.subst0 = t := by
  rw [<-vsubst_wk, <-vsubst_comp, Term.wk_succ_comp_subst0, vsubst_id]

/-- Substitute the free variables in a basic block -/
@[simp]
def Block.vsubst (σ : Term.Subst φ) (β : Block φ) : Block φ where
  body := β.body.subst σ
  terminator := β.terminator.vsubst (σ.liftn β.body.num_defs)

@[simp]
theorem Block.vsubst_id (β : Block φ) : β.vsubst Term.Subst.id = β := by simp

theorem Block.vsubst_comp (σ τ : Term.Subst φ) (β : Block φ)
  : β.vsubst (σ.comp τ) = (β.vsubst τ).vsubst σ
  := by simp [
    Body.subst_comp, Body.num_defs_subst, Term.Subst.liftn_comp, Terminator.vsubst_comp, *]

/-- Substitute the free variables in a region -/
@[simp]
def BBRegion.vsubst (σ : Term.Subst φ) : BBRegion φ → BBRegion φ
  | cfg β n f => cfg (β.vsubst σ) n (λ i => (f i).vsubst (σ.liftn (β.body.num_defs + 1)))

@[simp]
theorem BBRegion.vsubst_id (r : BBRegion φ) : r.vsubst Term.Subst.id = r := by
  induction r; simp [*]

theorem BBRegion.vsubst_comp (σ τ : Term.Subst φ) (r : BBRegion φ)
  : r.vsubst (σ.comp τ) = (r.vsubst τ).vsubst σ := by
  induction r generalizing σ τ
  simp [Body.subst_comp, Body.num_defs_subst, Term.Subst.liftn_comp, Terminator.vsubst_comp, *]

/-- Substitute the free variables in a control-flow graph -/
@[simp]
def BBCFG.vsubst (σ : Term.Subst φ) (cfg : BBCFG φ) : BBCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).vsubst σ

@[simp]
theorem BBCFG.vsubst_id (cfg : BBCFG φ) : cfg.vsubst Term.Subst.id = cfg := by
  cases cfg; simp [*]

theorem BBCFG.vsubst_comp (σ τ : Term.Subst φ) (cfg : BBCFG φ)
  : cfg.vsubst (σ.comp τ) = (cfg.vsubst τ).vsubst σ := by
  cases cfg; simp [BBRegion.vsubst_comp, *]

/-- Substitute the free variables in a region -/
@[simp]
def TRegion.vsubst (σ : Term.Subst φ) : TRegion φ → TRegion φ
  | let1 e t => let1 (e.subst σ) (t.vsubst σ.lift)
  | let2 e t => let2 (e.subst σ) (t.vsubst (σ.liftn 2))
  | cfg β n f => cfg (β.vsubst σ) n (λ i => (f i).vsubst σ.lift)

@[simp]
theorem TRegion.vsubst_id (r : TRegion φ) : r.vsubst Term.Subst.id = r := by
  induction r <;> simp [TRegion.vsubst, Term.Subst.lift_id, Term.Subst.liftn_id, *]

theorem TRegion.vsubst_comp (σ τ : Term.Subst φ) (r : TRegion φ)
  : r.vsubst (σ.comp τ) = (r.vsubst τ).vsubst σ := by
  induction r generalizing σ τ
  <;> simp [Term.subst_comp, Terminator.vsubst_comp, Term.Subst.lift_comp, Term.Subst.liftn_comp, *]

def TCFG.vsubst (σ : Term.Subst φ) (cfg : TCFG φ) : TCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).vsubst σ

@[simp]
theorem TCFG.vsubst_id (cfg : TCFG φ) : cfg.vsubst Term.Subst.id = cfg := by
  cases cfg; simp [TCFG.vsubst, *]

theorem TCFG.vsubst_comp (σ τ : Term.Subst φ) (cfg : TCFG φ)
  : cfg.vsubst (σ.comp τ) = (cfg.vsubst τ).vsubst σ := by
  cases cfg; simp [TCFG.vsubst, TRegion.vsubst_comp, *]

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

theorem Region.vsubst_comp (σ τ : Term.Subst φ) (r : Region φ)
  : r.vsubst (σ.comp τ) = (r.vsubst τ).vsubst σ := by
  induction r generalizing σ τ
  <;> simp [Term.subst_comp, Term.Subst.lift_comp, Term.Subst.liftn_comp, *]

/-- Substitute the free variables in a `CFG` using `σ` -/
def CFG.vsubst (σ : Term.Subst φ) (G : CFG φ) : CFG φ where
  length := G.length
  targets := λ i => (G.targets i).vsubst σ

@[simp]
theorem CFG.vsubst_id (G : CFG φ) : G.vsubst Term.Subst.id = G := by cases G; simp [vsubst]

theorem CFG.vsubst_comp (σ τ : Term.Subst φ) (G : CFG φ) : G.vsubst (σ.comp τ) = (G.vsubst τ).vsubst σ
  := by cases G; simp only [CFG.vsubst, Region.vsubst_comp, *]

/-! ### Terminator substitutions
 -/
namespace Terminator

/-- A substitution mapping labels to terminators -/
def Subst (φ : Type) := ℕ → Terminator φ

/-- The identity substitution, which maps labels to themselves -/
def Subst.id : Subst φ := λn => Terminator.br n (Term.var 0)

theorem Subst.id_apply (n : ℕ) : @Subst.id φ n = Terminator.br n (Term.var 0) := rfl

/-- Lift a substitution under a label binder -/
def Subst.lift (σ : Subst φ) : Subst φ
  | 0 => Terminator.br 0 (Term.var 0)
  | n + 1 => (σ n).lwk Nat.succ

/-- Lift a substitution under `n` label binders -/
def Subst.liftn (n : ℕ) (σ : Subst φ) : Subst φ
  := λm => if m < n then Terminator.br m (Term.var 0) else (σ (m - n)).lwk (λv => v + n)

@[simp]
theorem Subst.liftn_zero (σ : Subst φ) : σ.liftn 0 = σ := by
  funext n
  simp only [liftn]
  split
  . rename_i H; cases H
  . exact (σ n).lwk_id

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
          . simp only [<-Terminator.lwk_lwk]
            apply congr
            apply congrArg
            funext v
            simp_arith
            simp_arith

theorem Subst.liftn_eq_iterate_lift_apply (n: ℕ) (σ: Subst φ) : σ.liftn n = (Subst.lift^[n] σ)
  := by induction n with
  | zero => exact σ.liftn_zero
  | succ n => simp only [Function.iterate_succ_apply', Subst.liftn_succ, *]

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

theorem Subst.liftn_add_apply (n m: ℕ) (σ: Subst φ): (σ.liftn n).liftn m = σ.liftn (m + n)
  := by simp [liftn_add]

theorem Subst.lift_succ (σ : Subst φ) (i : ℕ) : σ.lift (i + 1) = (σ i).lwk Nat.succ := rfl

/-- Lift a substitution under a variable binder -/
def Subst.vlift (σ : Subst φ) : Subst φ
  := Terminator.vwk (Nat.liftWk Nat.succ) ∘ σ

@[simp]
theorem Subst.vlift_id : (@id φ).vlift = id := by funext v; cases v <;> rfl

theorem Subst.vlift_lift_comm (σ : Subst σ) : σ.lift.vlift = σ.vlift.lift := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [Subst.vlift, lift, vwk_lwk]

theorem Subst.vlift_lift_comp_comm : Subst.vlift ∘ (@Subst.lift φ) = Subst.lift ∘ Subst.vlift
  := funext Subst.vlift_lift_comm

theorem Subst.vlift_liftn_comm (n : ℕ) (σ : Subst σ) : (σ.liftn n).vlift = σ.vlift.liftn n := by
  induction n generalizing σ with
  | zero => simp
  | succ _ I => rw [liftn_succ, vlift_lift_comm, I, liftn_succ]

/-- Lift a substitution under `n` variable binders -/
def Subst.vliftn (n : ℕ) (σ : Subst φ) : Subst φ
  := Terminator.vwk (Nat.liftWk (λi => i + n)) ∘ σ

@[simp]
theorem Subst.vliftn_zero (σ : Subst φ) : σ.vliftn 0 = σ := by
  funext n
  simp [vliftn]

theorem Subst.vliftn_one (σ : Subst φ) : σ.vliftn 1 = σ.vlift := by
  funext n
  simp [vliftn, vlift]

theorem Subst.vliftn_succ (σ : Subst φ) (i : ℕ) : σ.vliftn (i + 1) = (σ.vliftn i).vlift := by
  funext ℓ
  simp only [vliftn, Function.comp_apply, vlift, ←vwk_vwk]
  congr
  funext n
  cases n <;> rfl

theorem Subst.vliftn_eq_iterate_vlift_apply (n: ℕ) (σ: Subst φ) : σ.vliftn n = (Subst.vlift^[n] σ)
  := by induction n with
  | zero => exact σ.vliftn_zero
  | succ n => simp only [Function.iterate_succ_apply', Subst.vliftn_succ, *]

theorem Subst.vliftn_eq_iterate_vlift (n: ℕ) : Subst.vliftn n = (@Subst.vlift φ)^[n] := by
  funext σ
  rw [vliftn_eq_iterate_vlift_apply]

theorem Subst.vliftn_succ' (σ : Subst φ) (i : ℕ) : σ.vliftn (i + 1) = σ.vlift.vliftn i
  := by simp [vliftn_eq_iterate_vlift]

-- TODO: vliftn is iterate vlift

-- TODO: vliftn id is id

/-- Substitute the labels in a `Terminator` using `σ` -/
@[simp]
def lsubst (σ : Subst φ) : Terminator φ → Terminator φ
  | Terminator.br n e => (σ n).vsubst e.subst0
  | Terminator.case e s t => Terminator.case e (lsubst σ.vlift s) (lsubst σ.vlift t)

@[simp]
theorem lsubst_id (t : Terminator φ) : t.lsubst Subst.id = t
  := by induction t <;> simp [*]

@[simp]
theorem lsubst_id' (t : Terminator φ) : t.lsubst (λi => Terminator.br i (Term.var 0)) = t
  := t.lsubst_id

/-- Create a substitution from a label renaming -/
def Subst.fromLwk (ρ : ℕ -> ℕ): Subst φ := λn => Terminator.br (ρ n) (Term.var 0)

@[simp]
theorem Subst.fromLwk_vlift (ρ) : (@fromLwk φ ρ).vlift = fromLwk ρ := by
  funext n; cases n <;> rfl

@[simp]
theorem Subst.fromLwk_apply (ρ : ℕ -> ℕ) (n : ℕ)
  : (@fromLwk φ ρ) n = Terminator.br (ρ n) (Term.var 0) := rfl

theorem Subst.fromLwk_lift (ρ) : (@fromLwk φ ρ).lift = fromLwk (Nat.liftWk ρ) := by
  funext n; cases n <;> rfl

theorem Subst.fromLwk_iterate_lift (n : ℕ) (ρ)
  : Subst.lift^[n] (@fromLwk φ ρ) = fromLwk (Nat.liftWk^[n] ρ)
  := by induction n generalizing ρ <;> simp [fromLwk_lift, *]

theorem Subst.fromLwk_liftn (n ρ) : (@fromLwk φ ρ).liftn n = fromLwk (Nat.liftnWk n ρ) := by
  rw [liftn_eq_iterate_lift, Nat.liftnWk_eq_iterate_liftWk, fromLwk_iterate_lift]

theorem lsubst_lwk (ρ : ℕ -> ℕ) (t : Terminator φ)
  : t.lsubst (Subst.fromLwk ρ) = t.lwk ρ := by
  induction t generalizing ρ <;> simp [Terminator.lsubst, Terminator.lwk, Term.subst_wk, *]

theorem lsubst_liftn (n : ℕ) (σ : Subst φ) (t : Terminator φ)
    : (t.lwk (Nat.liftnWk n Nat.succ)).lsubst (σ.liftn (n + 1))
      = (t.lsubst (σ.liftn n)).lwk (Nat.liftnWk n Nat.succ)
  := by induction t generalizing σ n with
  | br ℓ e =>
    simp only [lwk, lsubst, Nat.liftnWk, Subst.liftn]
    split
    . split
      . simp [lwk, Nat.liftnWk, *]
      . rename_i H C; exact (C (Nat.le_step H)).elim
    . rename_i C
      simp_arith only [ite_false]
      rw [Nat.succ_eq_add_one]
      have h : ℓ - n + 1 + n - (n + 1) = ℓ - n := by
        rw [Nat.add_assoc, Nat.add_comm 1 n, Nat.add_sub_cancel]
      rw [h, Terminator.vsubst_lwk_comm, <-lwk_lwk]
      congr
      funext n
      simp_arith [Nat.liftnWk]
  | case e s t => simp [Subst.vlift_liftn_comm, *]

theorem lsubst_iterate_lift (n : ℕ) (σ : Subst φ) (t : Terminator φ)
  : (t.lwk (Nat.liftWk^[n] Nat.succ)).lsubst (Subst.lift^[n + 1] σ)
    = (t.lsubst (Subst.lift^[n] σ)).lwk (Nat.liftWk^[n] Nat.succ)
  := by simp only [<-Subst.liftn_eq_iterate_lift, <-Nat.liftnWk_eq_iterate_liftWk, lsubst_liftn]

theorem lsubst_lift (t : Terminator φ) (σ : Subst φ)
  : (t.lwk Nat.succ).lsubst (σ.lift) = (t.lsubst σ).lwk Nat.succ := t.lsubst_iterate_lift 0 σ

/-- Compose two label-substitutions to yield another -/
def Subst.comp (σ τ : Subst φ): Subst φ
  | n => (τ n).lsubst σ.vlift

@[simp]
theorem Subst.comp_id (σ : Subst φ) : σ.comp Subst.id = σ := by
  funext n
  simp only [comp, Terminator.lsubst, Function.comp_apply, vlift]
  rw [<-Terminator.vsubst_wk, <-Terminator.vsubst_comp]
  simp

@[simp]
theorem Subst.id_comp (σ : Subst φ) : Subst.id.comp σ = σ := by funext n; exact lsubst_id (σ n)

theorem Subst.vlift_comp_liftWk_stepn (σ : Subst φ) (n)
  : vlift (vwk (Nat.liftWk (· + n)) ∘ σ) = vwk (Nat.liftWk (· + n)) ∘ σ.vlift
  := by
    simp only [vlift, <-Function.comp.assoc]
    apply congrArg₂
    funext i
    simp only [Function.comp_apply, <-vwk_vwk]
    apply congrArg₂
    funext i
    simp only [Function.comp_apply, Nat.wkn]
    cases i <;> simp_arith
    rfl
    rfl

theorem Subst.vlift_comp_liftWk_succ (σ : Subst φ)
  : vlift (vwk (Nat.liftWk Nat.succ) ∘ σ) = vwk (Nat.liftWk Nat.succ) ∘ σ.vlift
  := rfl

theorem Subst.vlift_comp_wk1 (σ : Subst φ)
  : vlift (vwk (Nat.wkn 1) ∘ σ) = vwk (Nat.wkn 1) ∘ σ.vlift
  := Nat.wkn_one ▸ vlift_comp_liftWk_succ σ

theorem vsubst_substn_lsubst_vliftn (t : Terminator φ) (e : Term φ) (σ : Subst φ) (n)
  : (t.lsubst (σ.vliftn (n + 1))).vsubst (e.substn n)
  = (t.vsubst (e.substn n)).lsubst (σ.vliftn n)
  := by induction t generalizing σ e n with
  | br ℓ e' =>
    simp only [
      lsubst, Subst.vliftn, <-Terminator.vsubst_fromWk, <-Terminator.vsubst_comp,
      Function.comp_apply]
    congr
    funext k
    cases k with
    | zero => rfl
    | succ k => simp_arith [Term.Subst.comp, Term.subst, Term.substn, Nat.liftWk]
  | _ => simp only [vsubst, lsubst,  <-Subst.vliftn_succ, <-Term.substn_succ, *]

theorem vsubst_subst0_lsubst_vlift (t : Terminator φ) (e : Term φ) (σ : Subst φ)
    : (t.lsubst σ.vlift).vsubst e.subst0 = (t.vsubst e.subst0).lsubst σ := by
  have h := vsubst_substn_lsubst_vliftn t e σ 0
  simp only [Term.substn_zero, Subst.vliftn_zero, Subst.vliftn_one, Nat.zero_add] at h
  exact h

theorem vsubst_substn_vwk (t : Terminator φ) (e : Term φ) (ρ n)
  : (t.vsubst (e.substn n)).vwk (Nat.liftnWk n ρ)
  = (t.vwk (Nat.liftnWk (n + 1) ρ)).vsubst ((e.wk (Nat.liftnWk n ρ)).substn n)
  := by induction t generalizing e ρ n with
  | br ℓ e' => simp only [vwk, vsubst, Term.subst_substn_wk]
  | _ => simp [
    <-Nat.liftnWk_succ_apply',
    <-Term.substn_succ, Term.subst_substn_wk,
    <-Term.wk_wk, Nat.liftnWk_comp_succ, *]

theorem vsubst_subst0_vwk (t : Terminator φ) (e : Term φ) (ρ)
  : (t.vsubst e.subst0).vwk ρ = (t.vwk (Nat.liftWk ρ)).vsubst (e.wk ρ).subst0 := by
  have h := vsubst_substn_vwk t e ρ 0
  simp [Nat.liftnWk_one, Nat.liftnWk_zero, Term.substn_zero] at h
  exact h

theorem vwk_lsubst (σ ρ) (t : Terminator φ)
  : (t.lsubst σ).vwk ρ = (t.vwk ρ).lsubst (vwk (Nat.liftWk ρ) ∘ σ)
  := by induction t generalizing σ ρ with
  | br ℓ e => simp [vsubst_subst0_vwk]
  | _ =>
    simp only [vwk, lsubst, *]
    congr <;> simp only [
      Subst.vlift, <-Function.comp.assoc, <-vwk_comp, <-Nat.liftWk_comp, Nat.liftWk_comp_succ
    ]

theorem Subst.vliftn_comp (n : ℕ) (σ τ : Subst φ)
  : (σ.comp τ).vliftn n = (σ.vliftn n).comp (τ.vliftn n)
  := by
  funext m
  simp only [Function.comp_apply, comp, vlift, vliftn, Function.comp_apply]
  generalize τ m = t
  rw [vwk_lsubst]
  simp only [<-Function.comp.assoc, <-vwk_comp, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]

theorem Subst.vlift_comp (σ τ : Subst φ) : (σ.comp τ).vlift = σ.vlift.comp τ.vlift
  := σ.vliftn_comp 1 τ

theorem lsubst_comp (σ τ : Subst φ) (t : Terminator φ)
  : t.lsubst (σ.comp τ) = (t.lsubst τ).lsubst σ
  := by induction t generalizing σ τ with
  | br ℓ e => simp only [lsubst, Subst.comp, vsubst_subst0_lsubst_vlift]
  | case e s t Is It => simp only [lsubst, Subst.comp, Subst.vlift_comp, *]

theorem Subst.liftn_comp (n : ℕ) (σ τ : Subst φ) : (σ.comp τ).liftn n = (σ.liftn n).comp (τ.liftn n)
  := by
  funext k
  simp only [liftn, comp]
  split
  case inl h => simp [liftn, vlift, h]
  case inr h =>
    sorry

theorem Subst.lift_comp (σ τ : Subst φ) : (σ.comp τ).lift = σ.lift.comp τ.lift := by
  have h := Subst.liftn_comp 1 σ τ
  simp only [Subst.liftn_one] at h
  exact h
  -- funext n
  -- cases n with
  -- | zero => rfl
  -- | succ n =>
  --   simp only [lift, comp, <-Terminator.lsubst_lwk, <-Terminator.lsubst_comp]
  --   congr
  --   funext n
  --   simp only [
  --     comp, lift, Function.comp_apply, Terminator.lsubst, Nat.succ_eq_add_one,
  --     <-Terminator.vsubst_wk, <-Terminator.vsubst_comp, vlift]
  --   rw [
  --     <-Term.Subst.comp_assoc,
  --     Term.liftWk_succ_comp_subst0,
  --     Term.alpha_var,
  --     Term.Subst.id_comp]
  --   generalize σ n = t
  --   induction t <;> simp [*]
  --   sorry

end Terminator

/-- Substitute the free labels in this basic block -/
def Block.lsubst (σ : Terminator.Subst φ) (β : Block φ) : Block φ where
  body := β.body
  terminator := β.terminator.lsubst (σ.vliftn β.body.num_defs)

/-- Substitute the free labels in this region -/
def BBRegion.lsubst (σ : Terminator.Subst φ) : BBRegion φ → BBRegion φ
  | cfg β n f => cfg (β.lsubst (σ.liftn n)) n
    (λ i => (f i).lsubst ((σ.liftn n).vliftn β.body.num_defs))

/-- Substitute the free labels in this control-flow graph -/
def BBCFG.lsubst (σ : Terminator.Subst φ) (cfg : BBCFG φ) : BBCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).lsubst σ

/-- Substitute the free labels in this region -/
def TRegion.lsubst (σ : Terminator.Subst φ) : TRegion φ → TRegion φ
  | let1 e t => let1 e (t.lsubst σ.vlift)
  | let2 e t => let2 e (t.lsubst (σ.vliftn 2))
  | cfg β n f => cfg (β.lsubst (σ.liftn n)) n (λ i => (f i).lsubst (σ.liftn n))

/-- Substitute the free labels in this control-flow graph -/
def TCFG.lsubst (σ : Terminator.Subst φ) (cfg : TCFG φ) : TCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).lsubst σ

/-! ### Region substitutions
 -/
namespace Region

/-- A substitution mapping labels to regions -/
def Subst (φ : Type) := ℕ → Region φ -- TODO: Region.Subst?

/-- The identity substitution, which maps labels to themselves -/
def Subst.id : Subst φ := λn => Region.br n (Term.var 0)

theorem Subst.id_apply (n : ℕ) : @Subst.id φ n = Region.br n (Term.var 0) := rfl

/-- Lift a substitution under a label binder -/
def Subst.lift (σ : Subst φ) : Subst φ
  | 0 => Region.br 0 (Term.var 0)
  | n + 1 => (σ n).lwk Nat.succ

/-- Lift a substitution under `n` label binders -/
def Subst.liftn (n : ℕ) (σ : Subst φ) : Subst φ
  := λm => if m < n then Region.br m (Term.var 0) else (σ (m - n)).lwk (λv => v + n)

@[simp]
theorem Subst.liftn_zero (σ : Subst φ) : σ.liftn 0 = σ := by
  funext n
  simp only [liftn]
  split
  . rename_i H; cases H
  . exact (σ n).lwk_id

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
          . simp only [<-Region.lwk_lwk]
            apply congr
            apply congrArg
            funext v
            simp_arith
            simp_arith

theorem Subst.liftn_eq_iterate_lift_apply (n: ℕ) (σ: Subst φ) : σ.liftn n = (Subst.lift^[n] σ) := by
  induction n with
  | zero => exact σ.liftn_zero
  | succ n => simp only [Function.iterate_succ_apply', Subst.liftn_succ, *]

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

theorem Subst.liftn_add_apply (n m: ℕ) (σ: Subst φ): (σ.liftn n).liftn m = σ.liftn (m + n)
  := by simp [liftn_add]

theorem Subst.lift_succ (σ : Subst φ) (i : ℕ) : σ.lift (i + 1) = (σ i).lwk Nat.succ := rfl

/-- Lift a substitution under a variable binder -/
def Subst.vlift (σ : Subst φ) : Subst φ
  := Region.vwk (Nat.liftWk Nat.succ) ∘ σ

theorem Subst.vlift_id : (@id φ).vlift = id := by funext v; cases v <;> rfl

/-- Lift a substitution under `n` variable binders -/
def Subst.vliftn (n : ℕ) (σ : Subst φ) : Subst φ
  := Region.vwk (Nat.liftWk (λi => i + n)) ∘ σ

-- TODO: vliftn is iterate vlift

-- TODO: vliftn id is id

/-- Substitute the labels in a `Region` using `σ` -/
@[simp]
def lsubst (σ : Subst φ) : Region φ → Region φ
  | br n e => (σ n).vsubst e.subst0
  | case e s t => case e (lsubst σ.vlift s) (lsubst σ.vlift t)
  | let1 e t => let1 e (lsubst σ.vlift t)
  | let2 e t => let2 e (lsubst (σ.vliftn 2) t)
  | cfg β n f => cfg (lsubst (σ.liftn n) β) n (λ i => lsubst (σ.liftn n) (f i))

/-- Compose two label-substitutions to yield another -/
def Subst.comp (σ τ : Subst φ): Subst φ
  | n => (τ n).lsubst σ.vlift

end Region

/-- Substitute the free labels in this control-flow graph -/
def CFG.lsubst (σ : Region.Subst φ) (G : CFG φ) : CFG φ where
  length := G.length
  targets := λ i => (G.targets i).lsubst σ

end BinSyntax