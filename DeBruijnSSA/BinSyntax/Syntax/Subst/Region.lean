import Discretion.Wk.Nat
import Discretion.Wk.Fin
import Discretion.Wk.Multiset
import Discretion.Wk.Multiset

import DeBruijnSSA.BinSyntax.Syntax.Subst.Term

namespace BinSyntax

/-! ### Region substitutions
 -/
namespace Region

/-- A substitution mapping labels to regions -/
def Subst (φ : Type _) := ℕ → Region φ -- TODO: Region.Subst?

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
          · simp only [Region.lwk_lwk]
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
  | succ n => simp [Subst.vlift, vwk1, lift, vwk_lwk]

theorem Subst.vlift_lift_comp_comm : Subst.vlift ∘ (@Subst.lift φ) = Subst.lift ∘ Subst.vlift
  := funext Subst.vlift_lift_comm

theorem Subst.vlift_liftn_comm (n : ℕ) (σ : Subst σ) : (σ.liftn n).vlift = σ.vlift.liftn n := by
  induction n generalizing σ with
  | zero => simp
  | succ _ I => rw [liftn_succ, vlift_lift_comm, I, liftn_succ]

/-- Lift a substitution under `n` variable binders -/
def Subst.vliftn (n : ℕ) (σ : Subst φ) : Subst φ
  := Region.vwk (Nat.liftWk (λi => i + n)) ∘ σ

@[simp]
theorem Subst.vliftn_zero (σ : Subst φ) : σ.vliftn 0 = σ := by
  funext n
  simp [vliftn]

theorem Subst.vliftn_one (σ : Subst φ) : σ.vliftn 1 = σ.vlift := by
  funext n
  simp [vliftn, vlift, vwk1]

theorem Subst.vliftn_succ (σ : Subst φ) (i : ℕ) : σ.vliftn (i + 1) = (σ.vliftn i).vlift := by
  funext ℓ
  simp only [vliftn, vwk1, Function.comp_apply, vlift, vwk_vwk]
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

@[simp]
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

/-- Substitute the labels in a `Region` using `σ` -/
@[simp]
def lsubst (σ : Subst φ) : Region φ → Region φ
  | br n e => (σ n).vsubst e.subst0
  | case e s t => case e (lsubst σ.vlift s) (lsubst σ.vlift t)
  | let1 e t => let1 e (lsubst σ.vlift t)
  | let2 e t => let2 e (lsubst (σ.vliftn 2) t)
  | cfg β n f => cfg (lsubst (σ.liftn n) β) n (λ i => lsubst (σ.liftn n).vlift (f i))

theorem lsubst_id_apply (t : Region φ) : t.lsubst Subst.id = t
  := by induction t <;> simp [*]

@[simp]
theorem lsubst_id : @lsubst φ (Subst.id) = id := funext lsubst_id_apply

theorem lsubst_id_apply' (t : Region φ) : t.lsubst (λi => Region.br i (Term.var 0)) = t
  := t.lsubst_id_apply

@[simp]
theorem lsubst_id' : @lsubst φ (λi => Region.br i (Term.var 0)) = id := funext lsubst_id_apply'

theorem lsubst_id_eq {t : Region φ} {σ : Subst φ} (hσ : σ = Subst.id)
  : t.lsubst σ = t := by cases hσ; simp

theorem lsubst_cfg
  : @lsubst φ σ (cfg β n G) = cfg (lsubst (σ.liftn n) β) n (lsubst (σ.liftn n).vlift ∘ G)
  := rfl

theorem lsubst_cfg1
  : @lsubst φ σ (cfg β 1 (Fin.elim1 G))
  = cfg (lsubst σ.lift β) 1 (Fin.elim1 $ lsubst σ.lift.vlift G) := by
  simp only [lsubst, cfg.injEq, heq_eq_eq, true_and, Subst.liftn_one]
  funext i; cases i using Fin.elim1; rfl

/-- Create a substitution from a label renaming -/
def Subst.fromLwk (ρ : ℕ -> ℕ): Subst φ := λn => Region.br (ρ n) (Term.var 0)

@[simp]
theorem Subst.vwk_lift_comp_fromLwk (ρ σ) : vwk (Nat.liftWk ρ) ∘ fromLwk σ = @fromLwk φ σ := rfl

@[simp]
theorem Subst.vwk1_comp_fromLwk (σ) : vwk1 ∘ fromLwk σ = @fromLwk φ σ := rfl

@[simp]
theorem Subst.vwk_lift_comp_id (ρ) : vwk (Nat.liftWk ρ) ∘ Subst.id = @Subst.id φ := rfl

@[simp]
theorem Subst.vsubst_lift_comp_id (σ : Term.Subst φ) : vsubst σ.lift ∘ Subst.id = Subst.id := rfl

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
  : (@fromLwk φ ρ) n = Region.br (ρ n) (Term.var 0) := rfl

theorem Subst.fromLwk_lift (ρ) : (@fromLwk φ ρ).lift = fromLwk (Nat.liftWk ρ) := by
  funext n; cases n <;> rfl

theorem Subst.fromLwk_iterate_lift (n : ℕ) (ρ)
  : Subst.lift^[n] (@fromLwk φ ρ) = fromLwk (Nat.liftWk^[n] ρ)
  := by induction n generalizing ρ <;> simp [fromLwk_lift, *]

theorem Subst.fromLwk_liftn (n ρ) : (@fromLwk φ ρ).liftn n = fromLwk (Nat.liftnWk n ρ) := by
  rw [liftn_eq_iterate_lift, Nat.liftnWk_eq_iterate_liftWk, fromLwk_iterate_lift]

theorem lsubst_fromLwk_apply (ρ : ℕ -> ℕ) (t : Region φ)
  : t.lsubst (Subst.fromLwk ρ) = t.lwk ρ := by
  induction t generalizing ρ
  <;> simp [Region.lsubst, Region.lwk, Term.subst_fromWk_apply, Subst.fromLwk_liftn, *]

theorem lsubst_fromLwk (ρ : ℕ -> ℕ) : lsubst (Subst.fromLwk ρ) = @lwk φ ρ
  := funext (lsubst_fromLwk_apply ρ)

theorem lsubst_comp_fromLwk : @lsubst φ ∘ (@Subst.fromLwk φ) = lwk := funext lsubst_fromLwk

theorem lsubst_liftn (n : ℕ) (σ : Subst φ) (t : Region φ)
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
      rw [h, Region.lwk_vsubst, lwk_lwk]
      congr
      funext n
      simp_arith [Nat.liftnWk]
  | cfg β k G Iβ IG => simp only [
    Subst.vlift_liftn_comm, lsubst, lwk, Subst.liftn_liftn,
    <-Nat.add_assoc, <-Nat.liftnWk_add_apply, *]
  | _ => simp [Subst.vlift_liftn_comm, Subst.vliftn_liftn, *]

theorem lsubst_iterate_lift (n : ℕ) (σ : Subst φ) (t : Region φ)
  : (t.lwk (Nat.liftWk^[n] Nat.succ)).lsubst (Subst.lift^[n + 1] σ)
    = (t.lsubst (Subst.lift^[n] σ)).lwk (Nat.liftWk^[n] Nat.succ)
  := by simp only [<-Subst.liftn_eq_iterate_lift, <-Nat.liftnWk_eq_iterate_liftWk, lsubst_liftn]

theorem lsubst_lift (t : Region φ) (σ : Subst φ)
  : (t.lwk Nat.succ).lsubst (σ.lift) = (t.lsubst σ).lwk Nat.succ := t.lsubst_iterate_lift 0 σ

/-- Compose two label-substitutions to yield another -/
def Subst.comp (σ τ : Subst φ): Subst φ
  | n => (τ n).lsubst σ.vlift

@[simp]
theorem Subst.comp_id (σ : Subst φ) : σ.comp Subst.id = σ := by
  funext n
  simp only [comp, Region.lsubst, Function.comp_apply, vlift, vwk1]
  rw [<-Region.vsubst_fromWk_apply, <-Region.vsubst_comp_apply]
  simp

@[simp]
theorem Subst.id_comp (σ : Subst φ) : Subst.id.comp σ = σ
  := by funext n; exact lsubst_id_apply (σ n)

theorem Subst.vlift_comp_liftWk_stepn (σ : Subst φ) (n)
    : vlift (vwk (Nat.liftWk (· + n)) ∘ σ) = vwk (Nat.liftWk (· + n)) ∘ σ.vlift := by
  simp only [vlift, vwk1, <-Function.comp.assoc]
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

theorem vsubst_substn_lsubst_vliftn (t : Region φ) (e : Term φ) (σ : Subst φ) (n)
  : (t.lsubst (σ.vliftn (n + 1))).vsubst (e.substn n)
  = (t.vsubst (e.substn n)).lsubst (σ.vliftn n)
  := by induction t generalizing σ e n with
  | br ℓ e' =>
    simp only [
      lsubst, Subst.vliftn, <-Region.vsubst_fromWk, <-Region.vsubst_comp_apply,
      Function.comp_apply]
    congr
    funext k
    cases k with
    | zero => rfl
    | succ k => simp_arith [Term.Subst.comp, Term.subst, Term.substn, Nat.liftWk]
  | _ => simp only [
    vsubst, lsubst,  <-Subst.vliftn_succ, <-Term.substn_succ,
    <-Subst.vliftn_add, <-Nat.add_assoc, <-Term.substn_add_right,
    <-Subst.vliftn_liftn, *
  ]

theorem vsubst_subst0_lsubst_vlift (t : Region φ) (e : Term φ) (σ : Subst φ)
    : (t.lsubst σ.vlift).vsubst e.subst0 = (t.vsubst e.subst0).lsubst σ := by
  have h := vsubst_substn_lsubst_vliftn t e σ 0
  simp only [Term.substn_zero, Subst.vliftn_zero, Subst.vliftn_one, Nat.zero_add] at h
  exact h

theorem vsubst_substn_vwk (t : Region φ) (e : Term φ) (ρ n)
  : (t.vsubst (e.substn n)).vwk (Nat.liftnWk n ρ)
  = (t.vwk (Nat.liftnWk (n + 1) ρ)).vsubst ((e.wk (Nat.liftnWk n ρ)).substn n)
  := by induction t generalizing e ρ n <;> simp [
        <-Nat.liftnWk_succ_apply', ← Nat.liftnWk_add_apply,
        <-Term.substn_succ, Term.subst_substn_wk,
        Term.wk_wk, Nat.liftnWk_comp_succ,  ← Term.substn_add_right,
        <-Nat.add_assoc, Nat.liftnWk_comp_add_right, *
      ]

theorem vsubst_subst0_vwk (t : Region φ) (e : Term φ) (ρ)
  : (t.vsubst e.subst0).vwk ρ = (t.vwk (Nat.liftWk ρ)).vsubst (e.wk ρ).subst0 := by
  have h := vsubst_substn_vwk t e ρ 0
  simp [Nat.liftnWk_one, Nat.liftnWk_zero, Term.substn_zero] at h
  exact h

theorem Subst.vwk_liftWk_comp_liftn (σ : Subst φ) (ρ)
    : vwk (Nat.liftWk ρ) ∘ σ.liftn n = liftn n (vwk (Nat.liftWk ρ) ∘ σ) := by
  funext k
  simp only [Function.comp_apply, liftn]
  split
  rfl
  rw [lwk_vwk]

theorem Subst.vwk_liftWk_liftWk_comp_vlift (σ : Subst φ) (ρ)
    : vwk (Nat.liftWk (Nat.liftWk ρ)) ∘ σ.vlift = vlift (vwk (Nat.liftWk ρ) ∘ σ) := by
  simp only [vlift, vwk1, ← Function.comp.assoc, ← vwk_comp, ← Nat.liftWk_comp, Nat.liftWk_comp_succ]

theorem Subst.vwk_liftWk_liftnWk_comp_vliftn (n : ℕ) (σ : Subst φ) (ρ)
    : vwk (Nat.liftWk (Nat.liftnWk n ρ)) ∘ σ.vliftn n = vliftn n (vwk (Nat.liftWk ρ) ∘ σ) := by
  simp only [vliftn, ← Function.comp.assoc, ← vwk_comp, ← Nat.liftWk_comp, Nat.liftnWk_comp_add]

theorem vwk_lsubst (σ ρ) (t : Region φ)
  : (t.lsubst σ).vwk ρ = (t.vwk ρ).lsubst (vwk (Nat.liftWk ρ) ∘ σ)
  := by induction t generalizing σ ρ with
  | br ℓ e => simp [vsubst_subst0_vwk]
  | _ =>
    simp only [
      vwk, lsubst,
      Subst.vwk_liftWk_liftWk_comp_vlift, Subst.vwk_liftWk_liftnWk_comp_vliftn,
      Subst.vwk_liftWk_comp_liftn, *]

theorem vwk1_lsubst (σ) (t : Region φ)
  : (t.lsubst σ).vwk1 = t.vwk1.lsubst (vwk2 ∘ σ)
  := by rw [vwk1, vwk_lsubst, vwk2, Nat.liftnWk_two]; rfl

theorem vwk1_lsubst_vlift (σ : Subst φ) (t : Region φ)
  : (t.lsubst σ.vlift).vwk1 = t.vwk1.lsubst σ.vlift.vlift
  := by simp only [Subst.vlift, vwk1_lsubst, ←Function.comp.assoc, vwk2_comp_vwk1]

theorem vwk2_lsubst_vlift₂ (σ : Subst φ) (t : Region φ)
  : (t.lsubst σ.vlift.vlift).vwk2 = t.vwk2.lsubst σ.vlift.vlift.vlift
  := by
  simp only [Subst.vlift, vwk2, vwk_lsubst, vwk1, <-vwk_comp, <-Function.comp.assoc]
  congr
  apply congrFun
  apply congrArg
  apply congrArg
  funext k; cases k using Nat.cases3 <;> rfl

theorem Subst.vliftn_comp (n : ℕ) (σ τ : Subst φ)
  : (σ.comp τ).vliftn n = (σ.vliftn n).comp (τ.vliftn n)
  := by
  funext m
  simp only [Function.comp_apply, comp, vlift, vliftn, vwk1, Function.comp_apply]
  generalize τ m = t
  rw [vwk_lsubst]
  simp only [<-Function.comp.assoc, <-vwk_comp, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]

theorem Subst.vlift_comp (σ τ : Subst φ) : (σ.comp τ).vlift = σ.vlift.comp τ.vlift
  := σ.vliftn_comp 1 τ

theorem Subst.lwk_comp_vlift (ρ) (σ : Subst φ) : lwk ρ ∘ σ.vlift = vlift (lwk ρ ∘ σ)
  := by simp only [vlift, vwk1, <-Function.comp.assoc, vwk_comp_lwk]

theorem Subst.lwk_comp_vliftn (ρ) (σ : Subst φ) (n) : lwk ρ ∘ σ.vliftn n = vliftn n (lwk ρ ∘ σ)
  := by simp only [vliftn, <-Function.comp.assoc, vwk_comp_lwk]

theorem Subst.vlift_comp_lwk (σ : Subst φ) (ρ) : vlift (σ ∘ ρ) = σ.vlift ∘ ρ := rfl

theorem Subst.vliftn_comp_lwk (σ : Subst φ) (ρ) (n) : vliftn n (σ ∘ ρ) = σ.vliftn n ∘ ρ := rfl

theorem Subst.liftn_comp_lwk (σ : Subst φ) (ρ) (n) : liftn n (σ ∘ ρ) = σ.liftn n ∘ Nat.liftnWk n ρ
  := by funext i; simp only [liftn, Function.comp_apply, Nat.liftnWk]; split <;> simp_arith

theorem Subst.liftn_lwk_comp (σ : Subst φ) (ρ) (n)
    : liftn n (lwk ρ ∘ σ) = lwk (Nat.liftnWk n ρ) ∘ σ.liftn n := by
  funext i
  simp only [liftn, Function.comp_apply, lwk, Nat.liftnWk]
  split
  · simp [Nat.liftnWk, *]
  · rw [lwk_lwk, lwk_lwk, Nat.liftnWk_comp_add]

theorem lwk_lsubst (σ ρ) (t : Region φ)
  : (t.lsubst σ).lwk ρ = t.lsubst (lwk ρ ∘ σ)
  := by induction t generalizing σ ρ with
  | br ℓ e => simp only [lsubst, Function.comp_apply, lwk_vsubst]
  | _ => simp [Subst.lwk_comp_vlift, Subst.lwk_comp_vliftn, Subst.liftn_lwk_comp , *]

theorem lsubst_lwk (σ ρ) (t : Region φ)
  : (t.lwk ρ).lsubst σ = t.lsubst (σ ∘ ρ) := by
  induction t generalizing σ ρ with
  | br ℓ e => rfl
  | _ => simp [Subst.vlift_comp_lwk, Subst.vliftn_comp_lwk, Subst.liftn_comp_lwk, *]

theorem Subst.liftn_comp_add (n) (σ : Subst φ) : σ.liftn n ∘ (· + n) = lwk (· + n) ∘ σ := by
  funext i; simp [liftn]

theorem Subst.liftn_comp (n : ℕ) (σ τ : Subst φ) : (σ.comp τ).liftn n = (σ.liftn n).comp (τ.liftn n)
  := by
  funext k
  simp only [liftn, comp]
  split
  case isTrue h => simp [liftn, vlift, h]
  case isFalse h =>
    rw [lwk_lsubst, lsubst_lwk]
    congr
    rw [lwk_comp_vlift, vlift, vlift, Function.comp.assoc, liftn_comp_add]

theorem Subst.lift_comp (σ τ : Subst φ) : (σ.comp τ).lift = σ.lift.comp τ.lift := by
  have h := Subst.liftn_comp 1 σ τ
  simp only [Subst.liftn_one] at h
  exact h

theorem lsubst_lsubst (σ τ : Subst φ) (t : Region φ)
  : (t.lsubst τ).lsubst σ = t.lsubst (σ.comp τ)
  := by induction t generalizing σ τ with
  | br ℓ e => simp only [lsubst, Subst.comp, vsubst_subst0_lsubst_vlift]
  | _ => simp only [lsubst, Subst.comp, Subst.vlift_comp, Subst.vliftn_comp, Subst.liftn_comp, *]

theorem lsubst_comp (σ τ : Subst φ)
  : Region.lsubst (σ.comp τ) = Region.lsubst σ ∘ Region.lsubst τ
  := Eq.symm $ funext $ lsubst_lsubst σ τ

/-- Substitute the labels in a `Region` using `σ` and let-bindings -/
@[simp]
def llsubst (σ : Subst φ) : Region φ → Region φ
  := lsubst (let1 (Term.var 0) ∘ σ.vlift)

/-- Compose two label-substitutions via let-bindings to yield another -/
def Subst.lcomp (σ τ : Subst φ): Subst φ
  | n => (τ n).llsubst σ.vlift

theorem Subst.vlift_let1_zero (σ : Subst φ)
    : vlift (let1 (Term.var 0) ∘ σ.vlift) = let1 (Term.var 0) ∘ σ.vlift.vlift :=
  by funext k; simp [vlift, vwk1, vwk_vwk, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]

theorem Subst.vliftn_let1_zero (σ : Subst φ)
    : vliftn n (let1 (Term.var 0) ∘ σ.vlift) = let1 (Term.var 0) ∘ (σ.vliftn n).vlift :=
  by induction n with
  | zero => simp
  | succ n I => rw [vliftn_succ, I, vlift_let1_zero, vliftn_succ]

theorem llsubst_lcomp (σ τ : Subst φ) : llsubst (σ.lcomp τ) = llsubst σ ∘ llsubst τ := by
  simp only [llsubst, <-lsubst_comp]
  apply congrArg
  funext k
  simp only [Subst.vlift, vwk1, Function.comp_apply, Subst.lcomp, llsubst, Subst.comp, lsubst, let1.injEq,
    true_and]
  rw [vwk_lsubst]
  congr
  funext k
  simp only [Function.comp_apply, vwk, Term.wk, Nat.liftWk_zero, let1.injEq, true_and, vwk_vwk]
  congr
  simp only [<-Nat.liftWk_comp, Nat.liftWk_comp_succ, <-Function.comp.assoc]
  rw [Function.comp.assoc, Nat.liftWk_comp_succ, Function.comp.assoc]

theorem llsubst_llsubst (σ τ : Subst φ) (t : Region φ)
  : (t.llsubst τ).llsubst σ = t.llsubst (σ.lcomp τ)
  := by rw [llsubst_lcomp]; simp

def let1V0 (r : Region φ) : Region φ := (r.vwk (Nat.liftWk Nat.succ)).let1 (Term.var 0)

theorem lsubst_let1V0_comp (σ : Subst φ) (r : Region φ)
  : (r.lsubst (let1V0 ∘ σ)) = r.llsubst σ
  := rfl

def let1Br : Subst φ := λℓ => (br ℓ (Term.var 0)).let1 (Term.var 0)

theorem Subst.let1V0_comp_id : @let1V0 φ ∘ id = let1Br := rfl

theorem lwk_lsubst_swap (σ σ' : Subst φ) (ρ ρ') (r : Region φ)
  (h : lwk ρ ∘ σ = σ' ∘ ρ')
  : (r.lsubst σ).lwk ρ = (r.lwk ρ').lsubst σ'
  := by rw [lwk_lsubst, lsubst_lwk, h]

theorem lsubst_lwk_swap (σ σ' : Subst φ) (ρ ρ') (r : Region φ)
  (h : σ ∘ ρ = lwk ρ' ∘ σ')
  : (r.lwk ρ).lsubst σ = (r.lsubst σ').lwk ρ'
  := by rw [lwk_lsubst, lsubst_lwk, h]

theorem lwk_lsubst_comm (σ : Subst φ) (ρ) (r : Region φ)
  (h : lwk ρ ∘ σ = σ ∘ ρ)
  : (r.lsubst σ).lwk ρ = (r.lwk ρ).lsubst σ
  := lwk_lsubst_swap σ σ ρ ρ r h

theorem lsubst_lwk_comm (σ : Subst φ) (ρ) (r : Region φ)
  (h : σ ∘ ρ = lwk ρ ∘ σ)
  : (r.lwk ρ).lsubst σ = (r.lsubst σ).lwk ρ
  := lsubst_lwk_swap σ σ ρ ρ r h

theorem Subst.liftn_comp_toNatWk {ρ : Fin k → Fin n}
  : (@liftn φ n σ) ∘ (Fin.toNatWk ρ) = (lwk $ Fin.toNatWk ρ) ∘ (@liftn φ k σ) := by
  funext i
  simp only [Function.comp_apply, liftn, Fin.toNatWk]
  split
  case isTrue h => simp [Fin.toNatWk, h]
  case isFalse h =>
    simp [Nat.sub_add_cancel (Nat.le_of_not_lt h), h, lwk_lwk, Fin.toNatWk_comp_add]

theorem lsubst_liftn_lwk_toNatWk {ρ : Fin k → Fin n}
    : (lsubst (@Subst.liftn φ n σ) (lwk (Fin.toNatWk ρ) r))
      = (lwk (Fin.toNatWk ρ) (lsubst (Subst.liftn k σ) r)) := by
  apply lsubst_lwk_swap
  apply Subst.liftn_comp_toNatWk

theorem lsubst_liftn_comp_lwk_toNatWk {ρ : Fin k → Fin n}
    : (lsubst (Subst.liftn n σ) ∘ lwk (Fin.toNatWk ρ))
      = (lwk (Fin.toNatWk ρ) ∘ lsubst (Subst.liftn k σ)) := by
  funext r
  apply lsubst_liftn_lwk_toNatWk

theorem vsubst_lift_lift_comp_vwk1 {ρ : Term.Subst φ}
  : (vsubst ρ.lift.lift ∘ vwk1) = (vwk1 ∘ vsubst ρ.lift) := by
  simp only [vwk1, <-vsubst_fromWk, vsubst_comp]
  apply congrArg
  funext k
  cases k with
  | zero => rfl
  | succ =>
    simp only [Term.Subst.comp, Term.subst, Nat.liftWk_succ, Nat.succ_eq_add_one,
      Term.Subst.lift_succ, Term.wk_wk, Term.subst_fromWk, Nat.liftWk_succ_comp_succ]
    rfl

theorem vsubst_lift₂_vwk1 {ρ : Term.Subst φ} {r : Region φ}
  : r.vwk1.vsubst ρ.lift.lift = (r.vsubst ρ.lift).vwk1 := congrFun vsubst_lift_lift_comp_vwk1 r

theorem vsubst_lift₃_vwk2 {ρ : Term.Subst φ} {r : Region φ}
  : r.vwk2.vsubst ρ.lift.lift.lift = (r.vsubst ρ.lift.lift).vwk2 := by
  simp only [vwk2, <-vsubst_fromWk, vsubst_vsubst]
  congr
  funext k; cases k using Nat.cases2 with
  | rest k =>
    simp_arith only [
      Term.Subst.comp, Term.Subst.lift, Term.subst, Nat.liftnWk, Term.subst_fromWk, Term.wk_wk
    ]
    rfl
  | _ => rfl

theorem vsubst_lift_lift_comp_vlift {ρ : Term.Subst φ} {σ : Subst φ}
  : (vsubst ρ.lift.lift ∘ σ.vlift) = Subst.vlift (vsubst ρ.lift ∘ σ) := by
  rw [Subst.vlift, <-Function.comp.assoc, vsubst_lift_lift_comp_vwk1]; rfl

theorem Subst.vsubst_lift_comp_liftn (σ : Subst φ) (ρ : Term.Subst φ)
    : vsubst ρ.lift ∘ σ.liftn n = liftn n (vsubst ρ.lift ∘ σ) := by
  funext k
  simp only [Function.comp_apply, liftn]
  split
  rfl
  rw [vsubst_lwk]

theorem vsubst_lsubst (σ ρ) (t : Region φ)
  : (t.lsubst σ).vsubst ρ = (t.vsubst ρ).lsubst (vsubst ρ.lift ∘ σ)
  := by induction t generalizing σ ρ with
  | br ℓ e =>
    simp only [lsubst, vsubst_vsubst, Function.comp_apply]
    congr
    funext k
    cases k <;> simp [Term.Subst.comp]
  | _ =>
    simp only [
      vsubst, lsubst, Term.Subst.liftn_two, Subst.vliftn_two, vsubst_lift_lift_comp_vlift,
      Subst.vsubst_lift_comp_liftn, *]

def lsubst0 (r : Region φ) : Subst φ
  | 0 => r
  | ℓ + 1 => br ℓ (Term.var 0)

def alpha (ℓ : ℕ) (r : Region φ) : Subst φ
  := Function.update Subst.id ℓ r

def Subst.toFCFG (σ : Subst φ) (n : ℕ) : Fin n → Region φ | i => σ i

def Subst.fromFCFG (k : ℕ) (σ : Fin n → Region φ) : Subst φ
  | i => if h : i < n then σ ⟨i, h⟩ else br (i - n + k) (Term.var 0)

def Subst.extend (σ : Subst φ) (n : ℕ) (k : ℕ) : Subst φ
  | i => if i < n then σ i else br (i - n + k) (Term.var 0)

@[simp]
theorem Subst.extend_lt {σ : Subst φ} {n k i} (hi : i < n)
  : σ.extend n k i = σ i := by simp [extend, *]

@[simp]
theorem Subst.extend_ge {σ : Subst φ} {n k i} (hi : i ≥ n)
  : σ.extend n k i = br (i - n + k) (Term.var 0) := by simp [extend, *]

@[simp]
theorem Subst.fromFCFG_lt {σ : Fin n → Region φ} {i : ℕ} (h : i < n)
  : Subst.fromFCFG k σ i = σ ⟨i, h⟩ := by simp [Subst.fromFCFG, h]

theorem Subst.fromFCFG_fin {σ : Fin n → Region φ} {i : Fin n}
  : Subst.fromFCFG k σ i = σ i := by simp

theorem Subst.fromFCFG_zero_zero {σ : Fin 0 → Region φ}
  : Subst.fromFCFG 0 σ = Subst.id := by funext i; rfl

theorem Subst.fromFCFG_zero_one {σ : Fin 1 → Region φ}
  : Subst.fromFCFG 0 σ = (σ 0).lsubst0 := by funext i; cases i <;> rfl

theorem Subst.fromFCFG_one_one {σ : Fin 1 → Region φ}
  : Subst.fromFCFG 1 σ = (σ 0).alpha 0 := by funext i; cases i <;> rfl

theorem Subst.fromFCFG_zero_elim1 {r : Region φ}
  : Subst.fromFCFG 0 (Fin.elim1 r) = r.lsubst0 := by rw [Subst.fromFCFG_zero_one]; rfl

theorem Subst.fromFCFG_one_elim1 {r : Region φ}
  : Subst.fromFCFG 1 (Fin.elim1 r) = r.alpha 0 := by rw [Subst.fromFCFG_one_one]; rfl

theorem Subst.toFCFG_fromFCFG (σ : Fin n → Region φ) : Subst.toFCFG (Subst.fromFCFG k σ) n = σ := by
  funext i
  cases i
  simp [fromFCFG, toFCFG, *]

theorem Subst.fromFCFG_toFCFG (σ : Subst φ) (n : ℕ)
  : Subst.fromFCFG k (Subst.toFCFG σ n) = σ.extend n k
  := by funext i; simp [fromFCFG, toFCFG, extend]

def Subst.trunc (σ : Subst φ) (n : ℕ) : Subst φ
  | i => if i < n then σ i else br i (Term.var 0)

@[simp]
theorem Subst.trunc_trunc {σ : Subst φ} {n m : ℕ}
  : (σ.trunc n).trunc m = σ.trunc (min n m) := by
  funext i
  simp only [trunc, lt_min_iff]
  split <;> split
  case isFalse.isTrue h h' => exact (h h'.right).elim
  all_goals simp [*]

theorem Subst.trunc_trunc_self {σ : Subst φ} {n : ℕ}
  : (σ.trunc n).trunc n = σ.trunc n := by simp

theorem Subst.trunc_comm {σ : Subst φ} {n m : ℕ}
  : (σ.trunc n).trunc m = (σ.trunc m).trunc n := by simp [min_comm]

theorem Subst.extend_same {σ : Subst φ} {n : ℕ}
  : σ.extend n n = σ.trunc n := by
  funext i
  simp only [extend, trunc]
  split
  case isTrue h => rfl
  case isFalse h => simp [Nat.ge_of_not_lt h]

theorem Subst.extend_eq_of_eq_on {σ τ : Subst φ} {n k : ℕ} (h : (Set.Iio n).EqOn σ τ)
  : σ.extend n k = τ.extend n k := by
  funext i
  simp only [extend]
  split
  case isTrue h' => exact h h'
  case isFalse h' => simp [Nat.ge_of_not_lt h']

theorem Subst.eq_on_of_extend_eq {σ τ : Subst φ} {n k : ℕ}
  (h : σ.extend n k = τ.extend n k)
  : (Set.Iio n).EqOn σ τ := λi hi => by
  have h := congrFun h i
  simp only [extend, Set.mem_Iio.mp hi, ↓reduceIte] at h
  exact h

theorem Subst.extend_eq_iff {σ τ : Subst φ} {n k : ℕ}
  : σ.extend n k = τ.extend n k ↔ (Set.Iio n).EqOn σ τ := ⟨
    Subst.eq_on_of_extend_eq,
    Subst.extend_eq_of_eq_on
  ⟩

theorem Subst.trunc_eq_iff {σ τ : Subst φ} {n : ℕ}
  : σ.trunc n = τ.trunc n ↔ (Set.Iio n).EqOn σ τ := by simp only [<-extend_same, extend_eq_iff]

theorem Subst.trunc_eq_of_eq_on {σ τ : Subst φ} {n : ℕ}
  (h : (Set.Iio n).EqOn σ τ) : σ.trunc n = τ.trunc n := trunc_eq_iff.mpr h

theorem Subst.eq_on_of_trunc_eq {σ τ : Subst φ} {n : ℕ}
  (h : σ.trunc n = τ.trunc n) : (Set.Iio n).EqOn σ τ := trunc_eq_iff.mp h

def csubst (r : Region φ) : Subst φ := λ_ => r

@[simp]
theorem Subst.csubst_apply {r : Region φ} {i : ℕ} : r.csubst i = r := rfl

theorem Subst.extend_alphan {r : Region φ}
  : (r.alpha n).extend (k + n + 1) (k + n + 1) = r.alpha n := by
  funext i
  simp [extend, Subst.id, alpha, Function.update]
  intro h
  rw [ite_cond_eq_false]
  simp only [br.injEq, and_true]
  omega
  simp only [eq_iff_iff, iff_false]
  omega

theorem Subst.extend_alpha0 {r : Region φ} : (r.alpha 0).extend (k + 1) (k + 1) = r.alpha 0
  := by rw [extend_alphan]

end Region

/-- Substitute the free labels in this control-flow graph -/
def CFG.lsubst (σ : Region.Subst φ) (G : CFG φ) : CFG φ where
  length := G.length
  targets := λ i => (G.targets i).lsubst σ

end BinSyntax
