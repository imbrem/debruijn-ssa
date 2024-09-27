import Discretion.Wk.Nat
import Discretion.Wk.Fin
import Discretion.Wk.Multiset
import Discretion.Wk.Multiset

import DeBruijnSSA.BinSyntax.Syntax.Subst.Term

namespace BinSyntax

/-! ### Terminator substitutions
 -/
namespace Terminator

/-- A substitution mapping labels to terminators -/
def Subst (φ : Type _) := ℕ → Terminator φ

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
  · rename_i H; cases H
  · exact (σ n).lwk_id

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
          · simp only [Terminator.lwk_lwk]
            apply congr
            apply congrArg
            funext v
            simp_arith
            simp_arith

theorem Subst.liftn_two (σ : Subst φ) : σ.liftn 2 = σ.lift.lift := by
  rw [Subst.liftn_succ, Subst.liftn_succ]; simp

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

theorem Subst.liftn_liftn (n m: ℕ) (σ: Subst φ): (σ.liftn n).liftn m = σ.liftn (m + n)
  := by simp [liftn_add]

theorem Subst.lift_succ (σ : Subst φ) (i : ℕ) : σ.lift (i + 1) = (σ i).lwk Nat.succ := rfl

/-- Lift a substitution under a variable binder -/
def Subst.vlift (σ : Subst φ) : Subst φ := vwk1 ∘ σ

@[simp]
theorem Subst.vlift_id : (@id φ).vlift = id := by funext v; cases v <;> rfl

theorem Subst.vlift_lift_comm (σ : Subst σ) : σ.lift.vlift = σ.vlift.lift := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [Subst.vlift, lift, vwk_lwk, vwk1]

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
  simp [vliftn, vlift, vwk1]

theorem Subst.vliftn_succ (σ : Subst φ) (i : ℕ) : σ.vliftn (i + 1) = (σ.vliftn i).vlift := by
  funext ℓ
  simp only [vliftn, Function.comp_apply, vlift, vwk_vwk, vwk1]
  congr
  funext n
  cases n <;> rfl

theorem Subst.vliftn_two (σ : Subst φ) : σ.vliftn 2 = σ.vlift.vlift := by
  rw [Subst.vliftn_succ, Subst.vliftn_succ]; simp

theorem Subst.vliftn_eq_iterate_vlift_apply (n: ℕ) (σ: Subst φ) : σ.vliftn n = (Subst.vlift^[n] σ)
  := by induction n with
  | zero => exact σ.vliftn_zero
  | succ n => simp only [Function.iterate_succ_apply', Subst.vliftn_succ, *]

theorem Subst.vliftn_eq_iterate_vlift (n: ℕ) : Subst.vliftn n = (@Subst.vlift φ)^[n] := by
  funext σ
  rw [vliftn_eq_iterate_vlift_apply]

theorem Subst.vliftn_succ' (σ : Subst φ) (i : ℕ) : σ.vliftn (i + 1) = σ.vlift.vliftn i
  := by simp [vliftn_eq_iterate_vlift]

theorem Subst.vliftn_add (σ : Subst φ) (n m: ℕ) : σ.vliftn (n + m) = (σ.vliftn m).vliftn n := by
  funext k
  simp [vliftn_eq_iterate_vlift, Function.iterate_add_apply]

theorem Subst.iterate_vlift_id : (n: ℕ) -> Subst.vlift^[n] (@id φ) = id
  | 0 => rfl
  | n + 1 => by simp [Subst.vlift_id, iterate_vlift_id n]

theorem Subst.vliftn_id (n: ℕ): (@id φ).vliftn n = id := by
  rw [vliftn_eq_iterate_vlift_apply, iterate_vlift_id]

theorem Subst.iterate_vlift_liftn_comm (k n : ℕ) (σ: Subst φ)
  : Subst.vlift^[k] (σ.liftn n) = (Subst.vlift^[k] σ).liftn n := by
  induction k generalizing σ with
  | zero => rfl
  | succ n I => simp [I, vlift_liftn_comm]

theorem Subst.vliftn_liftn (k n : ℕ) (σ: Subst φ)
  : (σ.liftn n).vliftn k = (σ.vliftn k).liftn n
  := by simp [vliftn_eq_iterate_vlift, iterate_vlift_liftn_comm]

theorem Subst.liftn_vliftn (k n : ℕ) (σ: Subst φ)
  : (σ.vliftn k).liftn n = (σ.liftn n).vliftn k
  := by simp [vliftn_eq_iterate_vlift, iterate_vlift_liftn_comm]

/-- Substitute the labels in a `Terminator` using `σ` -/
@[simp]
def lsubst (σ : Subst φ) : Terminator φ → Terminator φ
  | Terminator.br n e => (σ n).vsubst e.subst0
  | Terminator.case e s t => Terminator.case e (lsubst σ.vlift s) (lsubst σ.vlift t)

theorem lsubst_id_apply (t : Terminator φ) : t.lsubst Subst.id = t
  := by induction t <;> simp [*]

@[simp]
theorem lsubst_id : @lsubst φ (Subst.id) = id := funext lsubst_id_apply

theorem lsubst_id_apply' (t : Terminator φ) : t.lsubst (λi => Terminator.br i (Term.var 0)) = t
  := t.lsubst_id_apply

@[simp]
theorem lsubst_id' : @lsubst φ (λi => Terminator.br i (Term.var 0)) = id := funext lsubst_id_apply'

/-- Create a substitution from a label renaming -/
def Subst.fromLwk (ρ : ℕ -> ℕ): Subst φ := λn => Terminator.br (ρ n) (Term.var 0)

theorem Subst.vwk_lift_comp_fromLwk (ρ σ) : vwk (Nat.liftWk ρ) ∘ fromLwk σ = @fromLwk φ σ := rfl

theorem Subst.vwk1_comp_fromLwk (σ) : vwk1 ∘ fromLwk σ = @fromLwk φ σ := rfl

@[simp]
theorem Subst.fromLwk_vlift (ρ) : (@fromLwk φ ρ).vlift = fromLwk ρ := rfl

@[simp]
theorem Subst.fromLwk_iterate_vlift (n : ℕ) (ρ)
  : Subst.vlift^[n] (@fromLwk φ ρ) = fromLwk ρ
  := by induction n <;> simp [fromLwk_vlift, *]

@[simp]
theorem Subst.fromLwk_vliftn (n ρ) : (@fromLwk φ ρ).vliftn n = fromLwk ρ := by
  rw [vliftn_eq_iterate_vlift, fromLwk_iterate_vlift]

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

theorem lsubst_fromLwk_apply (ρ : ℕ -> ℕ) (t : Terminator φ)
  : t.lsubst (Subst.fromLwk ρ) = t.lwk ρ := by
  induction t generalizing ρ
  <;> simp [Terminator.lsubst, Terminator.lwk, Term.subst_fromWk_apply, *]

theorem lsubst_fromLwk (ρ : ℕ -> ℕ) : lsubst (Subst.fromLwk ρ) = @lwk φ ρ
  := funext (lsubst_fromLwk_apply ρ)

theorem lsubst_comp_fromLwk : @lsubst φ ∘ (@Subst.fromLwk φ) = lwk := funext lsubst_fromLwk

theorem lsubst_liftn (n : ℕ) (σ : Subst φ) (t : Terminator φ)
    : (t.lwk (Nat.liftnWk n Nat.succ)).lsubst (σ.liftn (n + 1))
      = (t.lsubst (σ.liftn n)).lwk (Nat.liftnWk n Nat.succ)
  := by induction t generalizing σ n with
  | br ℓ e =>
    simp only [lwk, lsubst, Nat.liftnWk, Subst.liftn]
    split
    · split
      · simp [lwk, Nat.liftnWk, *]
      · rename_i H C; exact (C (Nat.le_step H)).elim
    · rename_i C
      simp_arith only [ite_false]
      rw [Nat.succ_eq_add_one]
      have h : ℓ - n + 1 + n - (n + 1) = ℓ - n := by
        rw [Nat.add_assoc, Nat.add_comm 1 n, Nat.add_sub_cancel]
      rw [h, Terminator.lwk_vsubst, lwk_lwk]
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
  simp only [comp, Terminator.lsubst, Function.comp_apply, vlift, vwk1]
  rw [<-Terminator.vsubst_fromWk_apply, Terminator.vsubst_vsubst]
  simp

@[simp]
theorem Subst.id_comp (σ : Subst φ) : Subst.id.comp σ = σ
  := by funext n; exact lsubst_id_apply (σ n)

theorem Subst.vlift_comp_liftWk_stepn (σ : Subst φ) (n)
  : vlift (vwk (Nat.liftWk (· + n)) ∘ σ) = vwk (Nat.liftWk (· + n)) ∘ σ.vlift := by
  simp only [vlift, vwk1, <-Function.comp_assoc]
  apply congrArg₂
  funext i
  simp only [Function.comp_apply, vwk_vwk]
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
      lsubst, Subst.vliftn, <-Terminator.vsubst_fromWk, Terminator.vsubst_vsubst,
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
    Term.wk_wk, Nat.liftnWk_comp_succ, *]

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
      Subst.vlift, vwk1, <-Function.comp_assoc, <-vwk_comp, <-Nat.liftWk_comp, Nat.liftWk_comp_succ
    ]

theorem Subst.vliftn_comp (n : ℕ) (σ τ : Subst φ)
  : (σ.comp τ).vliftn n = (σ.vliftn n).comp (τ.vliftn n)
  := by
  funext m
  simp only [Function.comp_apply, comp, vlift, vliftn, vwk1, Function.comp_apply]
  generalize τ m = t
  rw [vwk_lsubst]
  simp only [<-Function.comp_assoc, <-vwk_comp, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]

theorem Subst.vlift_comp (σ τ : Subst φ) : (σ.comp τ).vlift = σ.vlift.comp τ.vlift
  := σ.vliftn_comp 1 τ

theorem lsubst_lsubst (σ τ : Subst φ) (t : Terminator φ)
  : (t.lsubst τ).lsubst σ = t.lsubst (σ.comp τ)
  := by induction t generalizing σ τ with
  | br ℓ e => simp only [lsubst, Subst.comp, vsubst_subst0_lsubst_vlift]
  | case e s t Is It => simp only [lsubst, Subst.comp, Subst.vlift_comp, *]

theorem lsubst_comp (σ τ : Subst φ)
  : Terminator.lsubst (σ.comp τ) = Terminator.lsubst σ ∘ Terminator.lsubst τ
  := Eq.symm $ funext $ lsubst_lsubst σ τ

theorem Subst.liftn_comp (n : ℕ) (σ τ : Subst φ) : (σ.comp τ).liftn n = (σ.liftn n).comp (τ.liftn n)
  := by
  funext k
  simp only [liftn, comp]
  split
  case isTrue h => simp [liftn, vlift, h]
  case isFalse h =>
    simp only [vlift, ←lsubst_fromLwk_apply, lsubst_lsubst]
    congr
    funext k
    simp only [comp, vlift, vwk1, vwk_lift_comp_fromLwk, Function.comp_apply, lsubst_fromLwk_apply,
      lsubst, Term.subst0_var0, liftn, Nat.add_sub_cancel, vwk_vwk, vsubst_fromWk_apply]
    rw [ite_cond_eq_false]
    simp only [vwk_lwk]
    congr
    funext k
    cases k <;> rfl
    simp_arith

theorem Subst.lift_comp (σ τ : Subst φ) : (σ.comp τ).lift = σ.lift.comp τ.lift := by
  have h := Subst.liftn_comp 1 σ τ
  simp only [Subst.liftn_one] at h
  exact h

end Terminator

/-- Substitute the free labels in this basic block -/
def Block.lsubst (σ : Terminator.Subst φ) (β : Block φ) : Block φ where
  body := β.body
  terminator := β.terminator.lsubst (σ.vliftn β.body.num_defs)

/-- Substitute the free labels in this region -/
def BBRegion.lsubst (σ : Terminator.Subst φ) : BBRegion φ → BBRegion φ
  | cfg β n f => cfg (β.lsubst (σ.liftn n)) n
    (λ i => (f i).lsubst ((σ.liftn n).vliftn (β.body.num_defs + 1)))

/-- Substitute the free labels in this control-flow graph -/
def BBCFG.lsubst (σ : Terminator.Subst φ) (cfg : BBCFG φ) : BBCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).lsubst σ

/-- Substitute the free labels in this region -/
def TRegion.lsubst (σ : Terminator.Subst φ) : TRegion φ → TRegion φ
  | let1 e t => let1 e (t.lsubst σ.vlift)
  | let2 e t => let2 e (t.lsubst (σ.vliftn 2))
  | cfg β n f => cfg (β.lsubst (σ.liftn n)) n (λ i => (f i).lsubst (σ.liftn n).vlift)

/-- Substitute the free labels in this control-flow graph -/
def TCFG.lsubst (σ : Terminator.Subst φ) (cfg : TCFG φ) : TCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).lsubst σ
