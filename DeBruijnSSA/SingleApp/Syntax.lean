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

-- TODO: label-substitution (TSubst)

/-- A basic block body -/
inductive Body (φ : Type) : Type
  | nil : Body φ
  | let1 : Term φ → Body φ → Body φ
  | let2 : Term φ → Body φ → Body φ

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
def Body.ltimes (b b' : Body φ) : Body φ := b.append (b'.wk (λn => n + b.num_defs))

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

/-- Weaken the variables in this basic block -/
@[simp]
def Block.vwk (ρ : ℕ → ℕ) (β : Block φ) : Block φ where
  body := β.body.wk ρ
  terminator := β.terminator.vwk (Nat.liftnWk β.body.num_defs ρ)

@[simp]
theorem Block.vwk_id (β : Block φ) : β.vwk id = β := by simp

theorem Block.vwk_comp (σ τ : ℕ → ℕ) (β : Block φ) : β.vwk (σ ∘ τ) = (β.vwk τ).vwk σ
  := by simp [Body.wk_comp, Terminator.vwk_comp, Body.num_defs_wk, Nat.liftnWk_comp, *]

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

-- TODO: label-substitution (TSubst)

/-- Prepend a body of instructions to this basic block -/
def Block.prepend (b : Body φ) (β : Block φ) : Block φ where
  body := b.append β.body
  terminator := β.terminator

theorem Block.prepend_append (b b' : Body φ) (β : Block φ)
  : β.prepend (b.append b') = (β.prepend b').prepend b := by
  simp only [Block.prepend, Body.append_assoc]

-- TODO: prepend_vwk

-- TODO: prepend_lwk

/-- Precompose a body of instructions to this basic block, while weakening the block so that
they share the same inputs -/
def Block.ltimes (b : Body φ) (β : Block φ) : Block φ where
  body := b.ltimes β.body
  terminator := β.terminator.vwk (λx => x + b.num_defs)

theorem Block.ltimes_ltimes (b b' : Body φ) (β : Block φ)
  : β.ltimes (b.ltimes b') = (β.ltimes b').ltimes b := by
  simp only [Block.ltimes, Body.ltimes_assoc, <-Terminator.vwk_comp]
  congr
  funext x
  simp_arith [Body.ltimes_num_defs]

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
  simp [Body.wk_comp, Terminator.vwk_comp, Body.num_defs_wk, Nat.liftnWk_comp, *]

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

-- TODO: label-substitution (TSubst)

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

-- TODO: label-substitution (TSubst)

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

-- TODO: label-substitution (TSubst, RSubst)

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
