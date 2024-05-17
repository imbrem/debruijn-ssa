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

theorem Subst.lift_succ (σ : Subst φ) (i : ℕ) : σ.lift (i + 1) = (σ i).wk Nat.succ := rfl

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
      simp_arith only [ite_false, <-wk_comp]
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
@[simp]
def subst0 (t : Term φ) : Subst φ
  | 0 => t
  | n + 1 => var n

@[simp]
theorem wk_succ_comp_subst0 (e : Term φ) : e.subst0.comp (Subst.fromWk Nat.succ) = Subst.id
  := by funext n; cases n <;> rfl

@[simp]
theorem wk_succ_subst_subst0 (e s : Term φ) : (e.wk Nat.succ).subst s.subst0 = e := by
  rw [<-subst_wk, <-subst_comp, wk_succ_comp_subst0, subst_id]

/-- Substitute a term for the smallest variable, leaving the rest unchanged -/
def alpha0 (t : Term φ) : Subst φ
  | 0 => t
  | n => var n

@[simp]
theorem wk_lift_succ_comp_subst0 (e : Term φ)
  : e.subst0.comp (Subst.fromWk (Nat.liftWk Nat.succ)) = e.alpha0
  := by funext n; cases n <;> rfl

@[simp]
theorem alpha0_var0 : (var 0).alpha0 = @Subst.id φ := by funext n; cases n <;> rfl

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

theorem Terminator.vsubst_wk (ρ : ℕ -> ℕ) (r : Terminator φ)
  : r.vsubst (Term.Subst.fromWk ρ) = r.vwk ρ := by
  induction r generalizing ρ
  <;> simp [Term.subst_wk, Term.Subst.fromWk_liftn, Term.Subst.fromWk_lift, *]

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
          . simp only [<-Terminator.lwk_comp]
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
  | succ n => simp [Subst.vlift, lift]; sorry

theorem Subst.vlift_lift_comp_comm : Subst.vlift ∘ (@Subst.lift φ) = Subst.lift ∘ Subst.vlift
  := funext Subst.vlift_lift_comm

theorem Subst.vlift_liftn_comm (n : ℕ) (σ : Subst σ) : (σ.liftn n).vlift = σ.vlift.liftn n := by
  induction n generalizing σ with
  | zero => simp
  | succ _ I => rw [liftn_succ, vlift_lift_comm, I, liftn_succ]

/-- Lift a substitution under `n` variable binders -/
def Subst.vliftn (n : ℕ) (σ : Subst φ) : Subst φ
  := Terminator.vwk (Nat.liftWk (λi => i + n)) ∘ σ

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
      rw [h, Terminator.vsubst_lwk_comm, <-lwk_comp]
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
  | n => (τ n).lsubst (Terminator.vwk (Nat.liftWk Nat.succ) ∘ σ)

@[simp]
theorem Subst.comp_id (σ : Subst φ) : σ.comp Subst.id = σ := by
  funext n
  simp only [comp, Terminator.lsubst, Function.comp_apply]
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
    simp only [Function.comp_apply, ←vwk_comp]
    apply congrArg₂
    funext i
    simp only [Function.comp_apply, Nat.liftWk]
    cases i <;> simp_arith
    rfl
    rfl

theorem Subst.vlift_comp_liftWk_step (σ : Subst φ)
  : vlift (vwk (Nat.liftWk Nat.succ) ∘ σ) = vwk (Nat.liftWk Nat.succ) ∘ σ.vlift
  := vlift_comp_liftWk_stepn σ 1

theorem Subst.vlift_comp (σ τ : Subst φ) : (σ.comp τ).vlift = σ.vlift.comp τ.vlift := by
  funext n
  simp only [vlift, Function.comp_apply, comp]
  generalize τ n = t
  induction t generalizing σ with
  | br ℓ e => simp; sorry
  | case e s t Is It => stop
    rw [lsubst, vwk, vlift_comp_liftWk_step, Is]
    sorry

theorem vsubst_subst0_lsubst_wk1 (t : Terminator φ) (e : Term φ) (σ : Subst φ)
  : (t.lsubst (vwk (Nat.liftWk Nat.succ) ∘ σ)).vsubst e.subst0
  = (t.vsubst e.subst0).lsubst σ
  := sorry

theorem lsubst_comp (σ τ : Subst φ) (t : Terminator φ)
  : t.lsubst (σ.comp τ) = (t.lsubst τ).lsubst σ
  := by induction t generalizing σ τ with
  | br ℓ e => simp only [lsubst, Subst.comp, vsubst_subst0_lsubst_wk1]
  | _ => simp only [lsubst, Subst.comp, Subst.vlift_comp, *]

theorem Subst.lift_comp (σ τ : Subst φ) : (σ.comp τ).lift = σ.lift.comp τ.lift := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    stop
    simp only [lift, comp, <-Terminator.lsubst_lwk, <-Terminator.lsubst_comp]
    congr
    funext n
    simp only [
      comp, lift, Function.comp_apply, Terminator.lsubst, Nat.succ_eq_add_one,
      <-Terminator.vsubst_wk, <-Terminator.vsubst_comp]
    rw [
      <-Term.Subst.comp_assoc,
      Term.wk_lift_succ_comp_subst0,
      Term.alpha0_var0,
      Term.Subst.id_comp]
    generalize σ n = t
    induction t <;> simp [*]

theorem Subst.iterate_lift_comp
  : (n : ℕ) -> ∀σ τ : Subst φ, Subst.lift^[n] (σ.comp τ)
    = (Subst.lift^[n] σ).comp (Subst.lift^[n] τ)
  | 0, σ, τ => rfl
  | n + 1, σ, τ => by simp [Subst.lift_comp, iterate_lift_comp n]

theorem Subst.liftn_comp (n : ℕ) (σ τ : Subst φ)
  : (σ.comp τ).liftn n = (σ.liftn n).comp (τ.liftn n)
  := by rw [liftn_eq_iterate_lift, iterate_lift_comp]

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
          . simp only [<-Region.lwk_comp]
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
  | n => (τ n).lsubst (Region.vwk (Nat.liftWk Nat.succ) ∘ σ)

end Region

/-- Substitute the free labels in this control-flow graph -/
def CFG.lsubst (σ : Region.Subst φ) (G : CFG φ) : CFG φ where
  length := G.length
  targets := λ i => (G.targets i).lsubst σ

end BinSyntax
