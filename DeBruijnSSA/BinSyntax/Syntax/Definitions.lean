import Discretion.Wk.Nat
import Discretion.Wk.Fin

namespace BinSyntax

/-! ### Basic syntax definitions

Free variables and simple coercions are given immediately after each definition to give an idea of how
the de-Bruijn indices are supposed to be interpreted.
 -/
section Definitions

/-- A simple term, consisting of variables, operations, pairs, units, and booleans -/
inductive Term (φ : Type _) where
  | var : ℕ → Term φ
  | op : φ → Term φ → Term φ
  | let1 : Term φ → Term φ → Term φ
  | pair : Term φ → Term φ → Term φ
  | unit : Term φ
  | let2 : Term φ → Term φ → Term φ
  | inl : Term φ → Term φ
  | inr : Term φ → Term φ
  | case: Term φ → Term φ → Term φ → Term φ
  | abort : Term φ → Term φ

/-- Rename the variables in a `Term` using `ρ` -/
@[simp]
def Term.wk (ρ : ℕ → ℕ) : Term φ → Term φ
  | var x => var (ρ x)
  | op f a => op f (wk ρ a)
  | let1 a e => let1 (wk ρ a) (wk (Nat.liftWk ρ) e)
  | pair l r => pair (wk ρ l) (wk ρ r)
  | unit => unit
  | let2 a e => let2 (wk ρ a) (wk (Nat.liftnWk 2 ρ) e)
  | inl a => inl (wk ρ a)
  | inr a => inr (wk ρ a)
  | case a l r => case (wk ρ a) (wk (Nat.liftWk ρ) l) (wk (Nat.liftWk ρ) r)
  | abort a => abort (wk ρ a)

/-- A basic block body, which consists of a sequence of variable definitions -/
inductive Body (φ : Type _) : Type
  | nil : Body φ
  | let1 : Term φ → Body φ → Body φ
  | let2 : Term φ → Body φ → Body φ

/-- The number of variables defined in a body -/
@[simp]
def Body.num_defs : Body φ → ℕ
  | nil => 0
  | let1 _ t => t.num_defs + 1
  | let2 _ t => t.num_defs + 2

/-- Rename the variables referenced in a `Body` using `ρ` -/
@[simp]
def Body.wk (ρ : ℕ → ℕ) : Body φ → Body φ
  | nil => nil
  | let1 e t => let1 (e.wk ρ) (t.wk (Nat.liftWk ρ))
  | let2 e t => let2 (e.wk ρ) (t.wk (Nat.liftnWk 2 ρ))

/-- A terminator, which either branches to a label with a parameter, or conditionally branches
to one of two sub-terminators.
 -/
inductive Terminator (φ : Type _) : Type
  | br : Nat → Term φ → Terminator φ
  | case : Term φ → Terminator φ → Terminator φ → Terminator φ

/-- Rename the variables referenced in a `Terminator` using `ρ` -/
@[simp]
def Terminator.vwk (ρ : ℕ → ℕ) : Terminator φ → Terminator φ
  | br n e => br n (e.wk ρ)
  | case e s t => case (e.wk ρ) (vwk (Nat.liftWk ρ) s) (vwk (Nat.liftWk ρ) t)

/-- Rename the labels in a `Region` using `ρ` -/
@[simp]
def Terminator.lwk (ρ : ℕ → ℕ) : Terminator φ → Terminator φ
  | br n e => br (ρ n) e
  | case e s t => case e (lwk ρ s) (lwk ρ t)

/-- A basic block, which consists of a sequence of instructions followed by a terminator -/
structure Block (φ : Type _) : Type where
  /-- The body of this basic block, containing the instructions and variable definitions within -/
  body : Body φ
  /-- The terminator of this basic block, determining where control flow goes to after the body
  is finished executing -/
  terminator : Terminator φ

/-- Rename the variables referenced in a `Block` using `ρ` -/
@[simp]
def Block.vwk (ρ : ℕ → ℕ) (β : Block φ) : Block φ where
  body := β.body.wk ρ
  terminator := β.terminator.vwk (Nat.liftnWk β.body.num_defs ρ)

/-- Rename the labels referenced in a `Block` using `ρ` -/
@[simp]
def Block.lwk (ρ : ℕ → ℕ) (β : Block φ) : Block φ where
  body := β.body
  terminator := β.terminator.lwk ρ

/-- Coerce a terminator into a block -/
def Terminator.toBlock (t : Terminator φ) : Block φ := ⟨Body.nil, t⟩

theorem Terminator.toBlock_injective : Function.Injective (@Terminator.toBlock φ) := by
  intro t₁ t₂ H
  cases t₁ <;> cases t₂ <;> cases H <;> rfl

theorem Terminator.toBlock_inj {t₁ t₂ : Terminator φ} : t₁.toBlock = t₂.toBlock ↔ t₁ = t₂ :=
    Terminator.toBlock_injective.eq_iff

instance coeTerminatorToBlock : Coe (Terminator φ) (Block φ) := ⟨Terminator.toBlock⟩

theorem Terminator.coe_toBlock_inj {t₁ t₂ : Terminator φ} : (t₁ : Block φ) = t₂ ↔ t₁ = t₂ :=
    Terminator.toBlock_injective.eq_iff

/-- A basic block-based single-entry multiple-exit region -/
inductive BBRegion (φ : Type _) : Type
  | cfg (β : Block φ) (n : Nat) : (Fin n → BBRegion φ) → BBRegion φ

/-- Rename the variables referenced in a `BBRegion` using `ρ` -/
@[simp]
def BBRegion.vwk (ρ : ℕ → ℕ) : BBRegion φ → BBRegion φ
  | cfg β n f => cfg (β.vwk ρ) n (λ i => (f i).vwk (Nat.liftnWk (β.body.num_defs + 1) ρ))

/-- Rename the labels referenced in a `BBRegion` using `ρ` -/
@[simp]
def BBRegion.lwk (ρ : ℕ → ℕ) : BBRegion φ → BBRegion φ
  | cfg β n f => cfg (β.lwk (Nat.liftnWk n ρ)) n (λ i => (f i).lwk (Nat.liftnWk n ρ))

/-- A basic-block based control-flow graph with `length` entry-point regions -/
structure BBCFG (φ : Type _) : Type where
  /-- The number of entry points to this CFG -/
  length : Nat
  /-- The number of exits for this CFG -/
  targets : Fin length → BBRegion φ

/-- Rename the variables in a `BBCFG` using `ρ` -/
@[simp]
def BBCFG.vwk (ρ : ℕ → ℕ) (cfg : BBCFG φ) : BBCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).vwk ρ

/-- Rename the labels in a `BBCFG` using `ρ` -/
@[simp]
def BBCFG.lwk (ρ : ℕ → ℕ) (cfg : BBCFG φ) : BBCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).lwk ρ

/-- A terminator-based single-entry multiple-exit region -/
inductive TRegion (φ : Type _) : Type
  | let1 : Term φ → TRegion φ → TRegion φ
  | let2 : Term φ → TRegion φ → TRegion φ
  | cfg (β : Terminator φ) (n : Nat) : (Fin n → TRegion φ) → TRegion φ

/-- Rename the variables referenced in a `TRegion` using `ρ` -/
@[simp]
def TRegion.vwk (ρ : ℕ → ℕ) : TRegion φ → TRegion φ
  | let1 e t => let1 (e.wk ρ) (t.vwk (Nat.liftWk ρ))
  | let2 e t => let2 (e.wk ρ) (t.vwk (Nat.liftnWk 2 ρ))
  | cfg β n f => cfg (β.vwk ρ) n (λ i => (f i).vwk (Nat.liftWk ρ))

/-- Rename the labels referenced in a `TRegion` using `ρ` -/
@[simp]
def TRegion.lwk (ρ : ℕ → ℕ) : TRegion φ → TRegion φ
  | let1 e t => let1 e (t.lwk ρ)
  | let2 e t => let2 e (t.lwk ρ)
  | cfg β n f => cfg (β.lwk (Nat.liftnWk n ρ)) n (λ i => (f i).lwk (Nat.liftnWk n ρ))

/-- A terminator-block based control-flow graph with `length` entry-point regions -/
structure TCFG (φ : Type _) : Type where
  /-- The number of entry points to this CFG -/
  length : Nat
  /-- The number of exits for this CFG -/
  targets : Fin length → TRegion φ

/-- Rename the variables referenced in a `TCFG` using `ρ` -/
@[simp]
def TCFG.vwk (ρ : ℕ → ℕ) (cfg : TCFG φ) : TCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).vwk ρ

/-- Rename the labels referenced in a `TRegion` using `ρ` -/
@[simp]
def TCFG.lwk (ρ : ℕ → ℕ) (cfg : TCFG φ) : TCFG φ where
  length := cfg.length
  targets := λi => (cfg.targets i).lwk (Nat.liftnWk cfg.length ρ)

/-- A single-entry multiple-exit region, similar to [A-normal
  form](https://en.wikipedia.org/wiki/A-normal_form) -/
inductive Region (φ : Type _) : Type _
  | br : Nat → Term φ → Region φ
  | case : Term φ → Region φ → Region φ → Region φ
  | let1 : Term φ → Region φ → Region φ
  | let2 : Term φ → Region φ → Region φ
  | cfg (β : Region φ) (n : Nat) : (Fin n → Region φ) → Region φ

/-- Convert this `Terminator` to a `Region` -/
@[simp]
def Terminator.toRegion : Terminator φ → Region φ
  | Terminator.br n e => Region.br n e
  | Terminator.case e s t => Region.case e s.toRegion t.toRegion

theorem Terminator.toRegion_inj {t₁ t₂ : Terminator φ} : t₁.toRegion = t₂.toRegion ↔ t₁ = t₂ := by
  induction t₁ generalizing t₂ <;> cases t₂ <;> simp [*]

theorem Terminator.toRegion_injective : Function.Injective (@Terminator.toRegion φ)
  := λ_ _ h => toRegion_inj.mp h

instance coeTerminatorToRegion : Coe (Terminator φ) (Region φ) := ⟨Terminator.toRegion⟩

/-- Convert this `TRegion` to a `Region` -/
@[simp]
def TRegion.toRegion : TRegion φ → Region φ
  | let1 e t => Region.let1 e t.toRegion
  | let2 e t => Region.let2 e t.toRegion
  | cfg β n f => Region.cfg β.toRegion n (λ i => (f i).toRegion)

theorem TRegion.toRegion_inj {t₁ t₂ : TRegion φ} : t₁.toRegion = t₂.toRegion ↔ t₁ = t₂ := by
  induction t₁ generalizing t₂ <;> cases t₂
  case cfg.cfg =>
    simp only [toRegion, Region.cfg.injEq, Terminator.toRegion_inj, cfg.injEq, and_congr_right_iff]
    intro hβ hn
    cases hβ; cases hn
    simp only [heq_eq_eq, funext_iff, *]
  all_goals simp [Terminator.toRegion_inj, *]

theorem TRegion.toRegion_injective : Function.Injective (@TRegion.toRegion φ)
  := λ_ _ h => toRegion_inj.mp h

instance coeTRegionToRegion : Coe (TRegion φ) (Region φ) := ⟨TRegion.toRegion⟩

/-- Rename the variables in a `Region` using `ρ` -/
@[simp]
def Region.vwk (ρ : ℕ → ℕ) : Region φ → Region φ
  | br n e => br n (e.wk ρ)
  | case e s t => case (e.wk ρ) (vwk (Nat.liftWk ρ) s) (vwk (Nat.liftWk ρ) t)
  | let1 e t => let1 (e.wk ρ) (vwk (Nat.liftWk ρ) t)
  | let2 e t => let2 (e.wk ρ) (vwk (Nat.liftnWk 2 ρ) t)
  | cfg β n f => cfg (vwk ρ β) n (λ i => (f i).vwk (Nat.liftWk ρ))

theorem Region.vwk_cfg (ρ : ℕ → ℕ) (β : Region φ) (n : ℕ) (G : Fin n → Region φ)
  : (cfg β n G).vwk ρ = cfg (β.vwk ρ) n (λ i => (G i).vwk (Nat.liftWk ρ))
  := rfl

theorem Region.vwk_cfg1 (ρ : ℕ → ℕ) (β : Region φ) (G : Region φ)
  : (cfg β 1 (Fin.elim1 G)).vwk ρ = cfg (β.vwk ρ) 1 (Fin.elim1 $ G.vwk (Nat.liftWk ρ))
  := by simp only [vwk, cfg.injEq, heq_eq_eq, true_and]; funext i; cases i using Fin.elim1; rfl

/-- Rename the labels in a `Region` using `ρ` -/
@[simp]
def Region.lwk (ρ : ℕ → ℕ) : Region φ → Region φ
  | br n e => br (ρ n) e
  | case e s t => case e (lwk ρ s) (lwk ρ t)
  | let1 e t => let1 e (lwk ρ t)
  | let2 e t => let2 e (lwk ρ t)
  | cfg β n f => cfg (lwk (Nat.liftnWk n ρ) β) n (λ i => (f i).lwk (Nat.liftnWk n ρ))

theorem Region.lwk_cfg (ρ : ℕ → ℕ) (β : Region φ) (n : ℕ) (G : Fin n → Region φ)
  : (cfg β n G).lwk ρ = cfg (β.lwk (Nat.liftnWk n ρ)) n (λ i => (G i).lwk (Nat.liftnWk n ρ))
  := rfl

theorem Region.lwk_cfg1 (ρ : ℕ → ℕ) (β : Region φ) (G : Region φ)
  : (cfg β 1 (Fin.elim1 G)).lwk ρ = cfg (β.lwk (Nat.liftWk ρ)) 1 (Fin.elim1 $ G.lwk (Nat.liftWk ρ))
  := by
  simp only [lwk, cfg.injEq, heq_eq_eq, true_and, Nat.liftnWk_one];
  funext i; cases i using Fin.elim1; rfl

/-- A control-flow graph with `length` entry-point regions -/
structure CFG (φ : Type _) : Type _ where
  /-- The number of entry points to this CFG -/
  length : Nat
  /-- The number of exits for this CFG -/
  targets : Fin length → Region φ

-- TODO: ∅ cfg; represent as 0?

/-- Convert a terminator CFG to a plain CFG -/
def TCFG.toCFG (G : TCFG φ) : CFG φ where
  length := G.length
  targets := λ i => (G.targets i).toRegion

instance : Coe (TCFG φ) (CFG φ) := ⟨λ G => ⟨G.length, λi => G.targets i⟩⟩

/-- Rename the variables in a `CFG` using `ρ` -/
@[simp]
def CFG.vwk (ρ : ℕ → ℕ) (G : CFG φ) : CFG φ where
  length := G.length
  targets := λ i => (G.targets i).vwk ρ

/-- Rename the labels in a `CFG` using `ρ` -/
@[simp]
def CFG.lwk (ρ : ℕ → ℕ) (G : CFG φ) : CFG φ where
  length := G.length
  targets := λ i => (G.targets i).lwk (Nat.liftnWk G.length ρ)

end Definitions

/-! ### Lemmas about weakening
 -/
section Weakening

theorem Term.wk_id (t : Term φ) : t.wk id = t := by induction t <;> simp [*]

@[simp]
theorem Term.wk_of_id : @wk φ id = id := funext wk_id

theorem Term.wk_id' : (t : Term φ) -> t.wk (λx => x) = t := wk_id

@[simp]
theorem Term.wk_of_id' : @wk φ (λx => x) = id := funext wk_id

theorem Term.wk_wk (ρ : ℕ → ℕ) (σ : ℕ → ℕ) (t : Term φ) : (t.wk σ).wk ρ  = t.wk (ρ ∘ σ)
  := by induction t generalizing σ ρ <;> simp [Nat.liftWk_comp, Nat.liftnWk_comp, *]

theorem Term.comp_wk (ρ σ)
  : wk ρ ∘ wk σ = @wk φ (ρ ∘ σ) := funext (Term.wk_wk ρ σ)

theorem Term.wk_comp (ρ σ)
  : @wk φ (ρ ∘ σ) = wk ρ ∘ wk σ := (comp_wk ρ σ).symm

theorem Term.wk_injective {ρ} (hρ : Function.Injective ρ) : Function.Injective (wk (φ := φ) ρ) := by
  intro a a' heq
  induction a generalizing a' ρ <;> cases a'
  case var.var =>
    simp only [wk, var.injEq] at heq
    simp [hρ heq]
  case op.op _ _ I _ _ =>
    simp only [wk, op.injEq] at heq
    simp [heq.1, I hρ heq.2]
  case let1.let1 _ Ia Ib _ _ =>
    simp only [wk, let1.injEq] at heq
    simp [Ia hρ heq.1, Ib (Nat.liftWk_injective_of_injective hρ) heq.2]
  case pair.pair _ Ia Ib _ _ =>
    simp only [wk, pair.injEq] at heq
    simp [Ia hρ heq.1, Ib hρ heq.2]
  case let2.let2 _ Ia Ib _ _ =>
    simp only [wk, let2.injEq] at heq
    simp [Ia hρ heq.1, Ib (Nat.liftnWk_injective_of_injective hρ) heq.2]
  case inl.inl _ I _ =>
    simp only [wk, inl.injEq] at heq
    simp [I hρ heq]
  case inr.inr _ I _ =>
    simp only [wk, inr.injEq] at heq
    simp [I hρ heq]
  case case.case _ Ie Il Ir _ _ _ =>
    simp only [wk, case.injEq] at heq
    have hρ' := Nat.liftWk_injective_of_injective hρ
    simp [Ie hρ heq.1, Il hρ' heq.2.1, Ir hρ' heq.2.2]
  case abort.abort _ I _ =>
    simp only [wk, abort.injEq] at heq
    simp [I hρ heq]
  all_goals (cases heq <;> rfl)

def Term.wk0 : Term φ → Term φ := wk Nat.succ

def Term.wk1 : Term φ → Term φ := wk (Nat.liftWk Nat.succ)

def Term.wk2 : Term φ → Term φ := wk (Nat.liftnWk 2 Nat.succ)

def Term.wk3 : Term φ → Term φ := wk (Nat.liftnWk 3 Nat.succ)

def Term.wk4 : Term φ → Term φ := wk (Nat.liftnWk 4 Nat.succ)

def Term.swap01 : Term φ → Term φ := wk (Nat.swap0 1)

def Term.swap02 : Term φ → Term φ := wk (Nat.swap0 2)

theorem Term.wk0_injective : Function.Injective (@Term.wk0 φ)
  := Term.wk_injective Nat.succ_injective

theorem Term.wk1_injective : Function.Injective (@Term.wk1 φ)
  := Term.wk_injective (Nat.liftWk_injective_of_injective Nat.succ_injective)

theorem Term.wk2_injective : Function.Injective (@Term.wk2 φ)
  := Term.wk_injective (Nat.liftnWk_injective_of_injective Nat.succ_injective)

theorem Term.wk3_injective : Function.Injective (@Term.wk3 φ)
  := Term.wk_injective (Nat.liftnWk_injective_of_injective Nat.succ_injective)

theorem Term.wk4_injective : Function.Injective (@Term.wk4 φ)
  := Term.wk_injective (Nat.liftnWk_injective_of_injective Nat.succ_injective)

theorem Term.wk0_let1 (e r : Term φ) : (let1 e r).wk0 = let1 e.wk0 r.wk1 := rfl

theorem Term.wk1_let1 (e r : Term φ) : (let1 e r).wk1 = let1 e.wk1 r.wk2
  := by simp [wk1, wk2, Nat.liftnWk_two]

theorem Term.wk0_let2 (e r : Term φ) : (let2 e r).wk0 = let2 e.wk0 r.wk2 := rfl

theorem Term.wk0_case (e l r : Term φ) : (case e l r).wk0 = case e.wk0 l.wk1 r.wk1 := rfl

theorem Term.wk1_case (e l r : Term φ) : (case e l r).wk1 = case e.wk1 l.wk2 r.wk2
  := by simp [wk1, wk2, Nat.liftnWk_two]

theorem Term.wk0_var (n : ℕ) : (var n).wk0 (φ := φ) = var (n + 1) := rfl

theorem Term.wk0_pair (l r : Term φ) : (pair l r).wk0 = pair l.wk0 r.wk0 := rfl

theorem Term.wk0_inl (e : Term φ) : (inl e).wk0 = inl e.wk0 := rfl

theorem Term.wk0_inr (e : Term φ) : (inr e).wk0 = inr e.wk0 := rfl

theorem Term.wk0_abort (e : Term φ) : (abort e).wk0 = abort e.wk0 := rfl

theorem Term.wk0_unit : unit.wk0 (φ := φ) = unit := rfl

theorem Term.wk1_pair (l r : Term φ) : (pair l r).wk1 = pair l.wk1 r.wk1 := rfl

theorem Term.wk1_inl (e : Term φ) : (inl e).wk1 = inl e.wk1 := rfl

theorem Term.wk1_inr (e : Term φ) : (inr e).wk1 = inr e.wk1 := rfl

theorem Term.wk1_abort (e : Term φ) : (abort e).wk1 = abort e.wk1 := rfl

theorem Term.wk1_unit : unit.wk1 (φ := φ) = unit := rfl

theorem Term.wk2_pair (l r : Term φ) : (pair l r).wk2 = pair l.wk2 r.wk2 := rfl

theorem Term.wk2_inl (e : Term φ) : (inl e).wk2 = inl e.wk2 := rfl

theorem Term.wk2_inr (e : Term φ) : (inr e).wk2 = inr e.wk2 := rfl

theorem Term.wk2_abort (e : Term φ) : (abort e).wk2 = abort e.wk2 := rfl

theorem Term.wk2_unit : unit.wk2 (φ := φ) = unit := rfl

theorem Term.wk_wk1 (r : Term φ) : r.wk1.wk ρ = r.wk (ρ ∘ Nat.liftWk Nat.succ)
  := by simp only [wk1, wk_wk, <-Nat.liftWk_comp]

theorem Term.wk0_wk1 (r : Term φ) : r.wk0.wk1 = r.wk0.wk0
  := by simp only [wk1, wk0, wk_wk, Nat.liftWk_comp_succ]

theorem Term.wk1_wk2 (r : Term φ) : r.wk1.wk2 = r.wk1.wk1
  := by simp only [wk1, wk2, wk_wk]; congr; funext k; cases k <;> rfl

theorem Term.wk1_wk0 (r : Term φ) : r.wk1.wk0 = r.wk0.wk2
  := by simp only [wk1, wk0, wk2, wk_wk]; congr; funext k; cases k <;> rfl

theorem Term.wk0_wk2 (r : Term φ) : r.wk0.wk2 = r.wk1.wk0
  := r.wk1_wk0.symm

theorem Term.wk_liftWk₂_wk1_to_wk (r : Term φ)
  : r.wk1.wk (Nat.liftWk (Nat.liftWk ρ)) = r.wk (Nat.liftWk (Nat.succ ∘ ρ))
  := by rw [wk_wk1, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]

theorem Term.wk_liftWk₂_wk1 (r : Term φ)
  : r.wk1.wk (Nat.liftWk (Nat.liftWk ρ)) = (r.wk (Nat.liftWk ρ)).wk1
  := by rw [wk_liftWk₂_wk1_to_wk, wk1, wk_wk, Nat.liftWk_comp]

theorem Term.wk_liftnWk₂_wk1 (r : Term φ)
  : r.wk1.wk (Nat.liftnWk 2 ρ) = (r.wk (Nat.liftWk ρ)).wk1
  := by rw [Nat.liftnWk_two, <-wk_liftWk₂_wk1]; rfl

theorem Term.wk1_wk_liftWk (r : Term φ)
  : (r.wk (Nat.liftWk ρ)).wk1 = r.wk1.wk (Nat.liftnWk 2 ρ)
  := r.wk_liftnWk₂_wk1.symm

theorem Term.wk_liftWk_wk_succ (r : Term φ)
  :  (r.wk Nat.succ).wk (Nat.liftWk ρ) = (r.wk ρ).wk Nat.succ
  := by simp only [wk_wk, Nat.liftWk_comp_succ]

theorem Term.wk_liftnWk_wk_add (r : Term φ) (n : ℕ)
  :  (r.wk (· + n)).wk (Nat.liftnWk n ρ) = (r.wk ρ).wk (· + n)
  := by simp only [wk_wk, Nat.liftnWk_comp_add]

def Term.wkn (n : ℕ) : Term φ → Term φ := wk (Nat.liftWk (· + n))

theorem Body.wk_id (b : Body φ) : b.wk id = b := by induction b <;> simp [*]

@[simp]
theorem Body.wk_of_id : @wk φ id = id := funext wk_id

theorem Body.wk_id' : (b : Body φ) → b.wk (λx => x) = b := wk_id

@[simp]
theorem Body.wk_of_id' : @wk φ (λx => x) = id := funext wk_id

theorem Body.wk_wk (σ τ : ℕ → ℕ) (b : Body φ)
  : (b.wk τ).wk σ = b.wk (σ ∘ τ) := by
  induction b generalizing σ τ
  <;> simp [Term.wk_wk, Nat.liftWk_comp, Nat.liftnWk_comp, *]

theorem Body.comp_wk (ρ σ)
  : wk ρ ∘ wk σ = @wk φ (ρ ∘ σ) := funext (Body.wk_wk ρ σ)

theorem Body.wk_comp (ρ σ)
  : @wk φ (ρ ∘ σ) = wk ρ ∘ wk σ := Eq.symm $ funext (Body.wk_wk ρ σ)

def Body.wk1 : Body φ → Body φ := wk (Nat.liftWk Nat.succ)

def Body.wkn (n : ℕ) : Body φ → Body φ := wk (Nat.liftWk (· + n))

@[simp]
theorem Body.num_defs_wk (ρ : ℕ → ℕ) (b : Body φ) : (b.wk ρ).num_defs = b.num_defs := by
  induction b generalizing ρ <;> simp [*]

theorem Terminator.vwk_id (r : Terminator φ) : r.vwk id = r := by
  induction r <;> simp [Nat.liftnWk_id, *]

@[simp]
theorem Terminator.vwk_of_id : @vwk φ id = id := funext vwk_id

theorem Terminator.vwk_id' : (r : Terminator φ) → r.vwk (λx => x) = r := vwk_id

@[simp]
theorem Terminator.vwk_of_id' : @vwk φ (λx => x) = id := funext vwk_id

theorem Terminator.vwk_vwk (σ τ : ℕ → ℕ) (r : Terminator φ)
  : (r.vwk τ).vwk σ = r.vwk (σ ∘ τ) := by
  induction r generalizing σ τ
  <;> simp [Term.wk_wk, Nat.liftWk_comp, Nat.liftnWk_comp, *]

theorem Terminator.comp_vwk (ρ σ)
  : vwk ρ ∘ vwk σ = @vwk φ (ρ ∘ σ) := funext (Terminator.vwk_vwk ρ σ)

theorem Terminator.vwk_comp (ρ σ)
  : @vwk φ (ρ ∘ σ) = vwk ρ ∘ vwk σ := Eq.symm $ funext (Terminator.vwk_vwk ρ σ)

def Terminator.vwk0 : Terminator φ → Terminator φ := vwk Nat.succ

def Terminator.vwk1 : Terminator φ → Terminator φ := vwk (Nat.liftWk Nat.succ)

def Terminator.vwkn (n : ℕ) : Terminator φ → Terminator φ := vwk (Nat.liftWk (· + n))

theorem Terminator.toBlock_vwk (ρ : ℕ → ℕ) (t : Terminator φ) : (t.vwk ρ).toBlock = t.toBlock.vwk ρ
  := rfl

theorem Terminator.coe_toBlock_vwk (ρ : ℕ → ℕ) (t : Terminator φ)
  : (t.vwk ρ : Block φ) = (t : Block φ).vwk ρ := rfl

theorem Terminator.toRegion_vwk (ρ : ℕ → ℕ) (t : Terminator φ)
  : (t.vwk ρ).toRegion = t.toRegion.vwk ρ := by induction t generalizing ρ <;> simp [*]

theorem Terminator.coe_toRegion_vwk (ρ : ℕ → ℕ) (t : Terminator φ)
  : (t.vwk ρ : Region φ) = (t : Region φ).vwk ρ := toRegion_vwk ρ t

theorem Terminator.toRegion_lwk (ρ : ℕ → ℕ) (t : Terminator φ)
  : (t.lwk ρ).toRegion = t.toRegion.lwk ρ := by induction t <;> simp [*]

theorem Terminator.coe_toRegion_lwk (ρ : ℕ → ℕ) (t : Terminator φ)
  : (t.lwk ρ : Region φ) = (t : Region φ).lwk ρ := toRegion_lwk ρ t

theorem Terminator.lwk_id (r : Terminator φ) : r.lwk id = r := by
  induction r <;> simp [Nat.liftnWk_id, *]

@[simp]
theorem Terminator.lwk_of_id : @lwk φ id = id := funext lwk_id

theorem Terminator.lwk_id' : (t : Terminator φ) → t.lwk (λx => x) = t := lwk_id

@[simp]
theorem Terminator.lwk_of_id' : @lwk φ (λx => x) = id := funext lwk_id

theorem Terminator.lwk_lwk (σ τ : ℕ → ℕ) (t : Terminator φ)
  : (t.lwk τ).lwk σ = t.lwk (σ ∘ τ) := by
  induction t generalizing σ τ <;> simp [Nat.liftnWk_comp, *]

theorem Terminator.comp_lwk (ρ σ)
  : lwk ρ ∘ lwk σ = @lwk φ (ρ ∘ σ) := funext (Terminator.lwk_lwk ρ σ)

theorem Terminator.lwk_comp (ρ σ)
  : @lwk φ (ρ ∘ σ) = lwk ρ ∘ lwk σ := Eq.symm $ funext (Terminator.lwk_lwk ρ σ)

theorem Terminator.toBlock_lwk (ρ : ℕ → ℕ) (t : Terminator φ) : (t.lwk ρ).toBlock = t.toBlock.lwk ρ
  := rfl

theorem Terminator.coe_toBlock_lwk (ρ : ℕ → ℕ) (t : Terminator φ)
  : (t.lwk ρ : Block φ) = (t : Block φ).lwk ρ := rfl

theorem Terminator.lwk_vwk (t : Terminator φ) : (t.vwk ρ).lwk σ = (t.lwk σ).vwk ρ := by
  induction t generalizing ρ σ <;> simp [*]

theorem Terminator.vwk_lwk (t : Terminator φ) : (t.lwk σ).vwk ρ = (t.vwk ρ).lwk σ := t.lwk_vwk.symm

theorem Terminator.lwk_comp_vwk : @lwk φ ρ ∘ vwk σ = vwk σ ∘ lwk ρ := funext Terminator.lwk_vwk

theorem Terminator.vwk_comp_lwk : @vwk φ σ ∘ lwk ρ = lwk ρ ∘ vwk σ := funext Terminator.vwk_lwk

theorem Block.vwk_id (β : Block φ) : β.vwk id = β := by simp

@[simp]
theorem Block.vwk_of_id : @vwk φ id = id := funext vwk_id

theorem Block.vwk_id' : (β : Block φ) → β.vwk (λx => x) = β := vwk_id

@[simp]
theorem Block.vwk_of_id' : @vwk φ (λx => x) = id := funext vwk_id

theorem Block.vwk_vwk (σ τ : ℕ → ℕ) (β : Block φ) : (β.vwk τ).vwk σ = β.vwk (σ ∘ τ)
  := by simp [Body.wk_wk, Terminator.vwk_vwk, Nat.liftnWk_comp, *]

theorem Block.comp_vwk (ρ σ)
  : vwk ρ ∘ vwk σ = @vwk φ (ρ ∘ σ) := funext (Block.vwk_vwk ρ σ)

theorem Block.vwk_comp (ρ σ)
  : @vwk φ (ρ ∘ σ) = vwk ρ ∘ vwk σ := Eq.symm $ funext (Block.vwk_vwk ρ σ)

def Block.wk1 : Block φ → Block φ := vwk (Nat.liftWk Nat.succ)

def Block.vwkn (n : ℕ) : Block φ → Block φ := vwk (Nat.liftWk (· + n))

theorem Block.lwk_id (β : Block φ) : β.lwk id = β := by simp

@[simp]
theorem Block.lwk_of_id : @lwk φ id = id := funext lwk_id

theorem Block.lwk_id' : (β : Block φ) → β.lwk (λx => x) = β := lwk_id

@[simp]
theorem Block.lwk_of_id' : @lwk φ (λx => x) = id := funext lwk_id

theorem Block.lwk_lwk (σ τ : ℕ → ℕ) (β : Block φ) : (β.lwk τ).lwk σ = β.lwk (σ ∘ τ)
  := by simp [Terminator.lwk_lwk]

theorem Block.comp_lwk (ρ σ)
  : lwk ρ ∘ lwk σ = @lwk φ (ρ ∘ σ) := funext (Block.lwk_lwk ρ σ)

theorem Block.lwk_comp (ρ σ)
  : @lwk φ (ρ ∘ σ) = lwk ρ ∘ lwk σ := Eq.symm $ funext (Block.lwk_lwk ρ σ)

theorem BBRegion.vwk_id (r : BBRegion φ) : r.vwk id = r := by
  induction r; simp [*]

@[simp]
theorem BBRegion.vwk_of_id : @vwk φ id = id := funext vwk_id

theorem BBRegion.vwk_id' : (r : BBRegion φ) → r.vwk (λx => x) = r := vwk_id

@[simp]
theorem BBRegion.vwk_of_id' : @vwk φ (λx => x) = id := funext vwk_id

theorem BBRegion.vwk_vwk (σ τ : ℕ → ℕ) (r : BBRegion φ)
  : (r.vwk τ).vwk σ = r.vwk (σ ∘ τ) := by
  induction r generalizing σ τ
  simp [Body.wk_wk, Terminator.vwk_vwk, Body.num_defs_wk, Nat.liftWk_comp, Nat.liftnWk_comp, *]

theorem BBRegion.comp_vwk (ρ σ)
  : vwk ρ ∘ vwk σ = @vwk φ (ρ ∘ σ) := funext (BBRegion.vwk_vwk ρ σ)

theorem BBRegion.vwk_comp (ρ σ)
  : @vwk φ (ρ ∘ σ) = vwk ρ ∘ vwk σ := Eq.symm $ funext (BBRegion.vwk_vwk ρ σ)

def BBRegion.vwk1 : BBRegion φ → BBRegion φ := vwk (Nat.liftWk Nat.succ)

def BBRegion.vwkn (n : ℕ) : BBRegion φ → BBRegion φ := vwk (Nat.liftWk (· + n))

theorem BBRegion.lwk_id (r : BBRegion φ) : r.lwk id = r := by
  induction r; simp [*]

@[simp]
theorem BBRegion.lwk_of_id : @lwk φ id = id := funext lwk_id

theorem BBRegion.lwk_id' : (r : BBRegion φ) → r.lwk (λx => x) = r := lwk_id

@[simp]
theorem BBRegion.lwk_of_id' : @lwk φ (λx => x) = id := funext lwk_id

theorem BBRegion.lwk_lwk (σ τ : ℕ → ℕ) (r : BBRegion φ)
  : (r.lwk τ).lwk σ = r.lwk (σ ∘ τ) := by
  induction r generalizing σ τ
  simp [Body.wk_wk, Terminator.lwk_lwk, Nat.liftnWk_comp, *]

theorem BBRegion.comp_lwk (ρ σ)
  : lwk ρ ∘ lwk σ = @lwk φ (ρ ∘ σ) := funext (BBRegion.lwk_lwk ρ σ)

theorem BBRegion.lwk_comp (ρ σ)
  : @lwk φ (ρ ∘ σ) = lwk ρ ∘ lwk σ := Eq.symm $ funext (BBRegion.lwk_lwk ρ σ)

theorem BBCFG.vwk_id (cfg : BBCFG φ) : cfg.vwk id = cfg := by
  cases cfg; simp [*]

@[simp]
theorem BBCFG.vwk_of_id : @vwk φ id = id := funext vwk_id

theorem BBCFG.vwk_id' : (cfg : BBCFG φ) → cfg.vwk (λx => x) = cfg := vwk_id

@[simp]
theorem BBCFG.vwk_of_id' : @vwk φ (λx => x) = id := funext vwk_id

theorem BBCFG.vwk_vwk (σ τ : ℕ → ℕ) (cfg : BBCFG φ) : (cfg.vwk τ).vwk σ = cfg.vwk (σ ∘ τ) := by
  cases cfg; simp [BBRegion.vwk_vwk, *]

def BBCFG.vwk1 : BBCFG φ → BBCFG φ := vwk (Nat.liftWk Nat.succ)

def BBCFG.vwkn (n : ℕ) : BBCFG φ → BBCFG φ := vwk (Nat.liftWk (· + n))

theorem BBCFG.lwk_id (cfg : BBCFG φ) : cfg.lwk id = cfg := by
  cases cfg; simp [*]

@[simp]
theorem BBCFG.lwk_of_id : @lwk φ id = id := funext lwk_id

theorem BBCFG.lwk_id' : (cfg : BBCFG φ) → cfg.lwk (λx => x) = cfg := lwk_id

@[simp]
theorem BBCFG.lwk_of_id' : @lwk φ (λx => x) = id := funext lwk_id

theorem BBCFG.lwk_lwk (σ τ : ℕ → ℕ) (cfg : BBCFG φ) : (cfg.lwk τ).lwk σ = cfg.lwk (σ ∘ τ) := by
  cases cfg; simp [BBRegion.lwk_lwk, *]

theorem BBCFG.comp_lwk (ρ σ)
  : lwk ρ ∘ lwk σ = @lwk φ (ρ ∘ σ) := funext (BBCFG.lwk_lwk ρ σ)

theorem BBCFG.lwk_comp (ρ σ)
  : @lwk φ (ρ ∘ σ) = lwk ρ ∘ lwk σ := Eq.symm $ funext (BBCFG.lwk_lwk ρ σ)

theorem TRegion.vwk_id (r : TRegion φ) : r.vwk id = r := by
  induction r <;> simp [TRegion.vwk, *]

@[simp]
theorem TRegion.vwk_of_id : @vwk φ id = id := funext vwk_id

theorem TRegion.vwk_id' : (r : TRegion φ) → r.vwk (λx => x) = r := vwk_id

@[simp]
theorem TRegion.vwk_of_id' : @vwk φ (λx => x) = id := funext vwk_id

theorem TRegion.vwk_vwk (σ τ : ℕ → ℕ) (r : TRegion φ)
  : (r.vwk τ).vwk σ = r.vwk (σ ∘ τ) := by
  induction r generalizing σ τ
  <;> simp [Term.wk_wk, Terminator.vwk_vwk, Nat.liftWk_comp, Nat.liftnWk_comp, *]

theorem TRegion.comp_vwk (ρ σ)
  : vwk ρ ∘ vwk σ = @vwk φ (ρ ∘ σ) := funext (TRegion.vwk_vwk ρ σ)

theorem TRegion.vwk_comp (ρ σ)
  : @vwk φ (ρ ∘ σ) = vwk ρ ∘ vwk σ := Eq.symm $ funext (TRegion.vwk_vwk ρ σ)

def TRegion.vwk1 : TRegion φ → TRegion φ := vwk (Nat.liftWk Nat.succ)

def TRegion.vwkn (n : ℕ) : TRegion φ → TRegion φ := vwk (Nat.liftWk (· + n))

theorem TRegion.toRegion_vwk (ρ : ℕ → ℕ) (t : TRegion φ) : (t.vwk ρ).toRegion = t.toRegion.vwk ρ
  := by induction t generalizing ρ <;> simp [Terminator.toRegion_vwk, *]

theorem TRegion.coe_toRegion_vwk (ρ : ℕ → ℕ) (t : TRegion φ)
  : (t.vwk ρ : Region φ) = (t : Region φ).vwk ρ := toRegion_vwk ρ t

theorem TRegion.lwk_id (r : TRegion φ) : r.lwk id = r := by
  induction r <;> simp [TRegion.lwk, *]

@[simp]
theorem TRegion.lwk_of_id : @lwk φ id = id := funext lwk_id

theorem TRegion.lwk_id' : (r : TRegion φ) → r.lwk (λx => x) = r := lwk_id

@[simp]
theorem TRegion.lwk_of_id' : @lwk φ (λx => x) = id := funext lwk_id

theorem TRegion.lwk_lwk (σ τ : ℕ → ℕ) (r : TRegion φ)
  : (r.lwk τ).lwk σ = r.lwk (σ ∘ τ) := by
  induction r generalizing σ τ
  <;> simp [Term.wk_wk, Terminator.lwk_lwk, Nat.liftnWk_comp, *]

theorem TRegion.comp_lwk (ρ σ)
  : lwk ρ ∘ lwk σ = @lwk φ (ρ ∘ σ) := funext (TRegion.lwk_lwk ρ σ)

theorem TRegion.lwk_comp (ρ σ)
  : @lwk φ (ρ ∘ σ) = lwk ρ ∘ lwk σ := Eq.symm $ funext (TRegion.lwk_lwk ρ σ)

theorem TRegion.toRegion_lwk (ρ : ℕ → ℕ) (t : TRegion φ) : (t.lwk ρ).toRegion = t.toRegion.lwk ρ
  := by induction t generalizing ρ <;> simp [Terminator.toRegion_lwk, *]

theorem TRegion.coe_toRegion_lwk (ρ : ℕ → ℕ) (t : TRegion φ)
  : (t.lwk ρ : Region φ) = (t : Region φ).lwk ρ := toRegion_lwk ρ t

theorem TCFG.vwk_id (cfg : TCFG φ) : cfg.vwk id = cfg := by
  cases cfg; simp [*]

@[simp]
theorem TCFG.vwk_of_id : @vwk φ id = id := funext vwk_id

theorem TCFG.vwk_id' : (cfg : TCFG φ) → cfg.vwk (λx => x) = cfg := vwk_id

@[simp]
theorem TCFG.vwk_of_id' : @vwk φ (λx => x) = id := funext vwk_id

theorem TCFG.vwk_vwk (σ τ : ℕ → ℕ) (cfg : TCFG φ) : (cfg.vwk τ).vwk σ = cfg.vwk (σ ∘ τ) := by
  cases cfg; simp [TRegion.vwk_vwk, *]

theorem TCFG.comp_vwk (ρ σ)
  : vwk ρ ∘ vwk σ = @vwk φ (ρ ∘ σ) := funext (TCFG.vwk_vwk ρ σ)

theorem TCFG.vwk_comp (ρ σ)
  : @vwk φ (ρ ∘ σ) = vwk ρ ∘ vwk σ := Eq.symm $ funext (TCFG.vwk_vwk ρ σ)

theorem TCFG.lwk_id (cfg : TCFG φ) : cfg.lwk id = cfg := by
  cases cfg; simp [TCFG.lwk, *]

@[simp]
theorem TCFG.lwk_of_id : @lwk φ id = id := funext lwk_id

theorem TCFG.lwk_id' : (cfg : TCFG φ) → cfg.lwk (λx => x) = cfg := lwk_id

@[simp]
theorem TCFG.lwk_of_id' : @lwk φ (λx => x) = id := funext lwk_id

theorem TCFG.lwk_lwk (σ τ : ℕ → ℕ) (cfg : TCFG φ) : (cfg.lwk τ).lwk σ = cfg.lwk (σ ∘ τ) := by
  cases cfg; simp [TCFG.lwk, TRegion.lwk_lwk, Nat.liftnWk_comp, *]

theorem TCFG.comp_lwk (ρ σ)
  : lwk ρ ∘ lwk σ = @lwk φ (ρ ∘ σ) := funext (TCFG.lwk_lwk ρ σ)

theorem TCFG.lwk_comp (ρ σ)
  : @lwk φ (ρ ∘ σ) = lwk ρ ∘ lwk σ := Eq.symm $ funext (TCFG.lwk_lwk ρ σ)

def TCFG.vwk1 : TCFG φ → TCFG φ := vwk (Nat.liftWk Nat.succ)

def TCFG.vwkn (n : ℕ) : TCFG φ → TCFG φ := vwk (Nat.liftWk (· + n))

theorem Region.vwk_id (r : Region φ) : r.vwk id = r := by
  induction r <;> simp [Region.vwk, Nat.liftnWk_id, *]

@[simp]
theorem Region.vwk_of_id : @vwk φ id = id := funext vwk_id

theorem Region.vwk_id' : (r : Region φ) → r.vwk (λx => x) = r := vwk_id

@[simp]
theorem Region.vwk_of_id' : @vwk φ (λx => x) = id := funext vwk_id

theorem Region.vwk_vwk (σ τ : ℕ → ℕ) (r : Region φ)
  : (r.vwk τ).vwk σ = r.vwk (σ ∘ τ) := by
  induction r generalizing σ τ
  <;> simp [vwk, Term.wk_wk, Nat.liftWk_comp, Nat.liftnWk_comp, *]

theorem Region.comp_vwk (ρ σ)
  : vwk ρ ∘ vwk σ = @vwk φ (ρ ∘ σ) := funext (Region.vwk_vwk ρ σ)

theorem Region.vwk_comp (ρ σ)
  : @vwk φ (ρ ∘ σ) = vwk ρ ∘ vwk σ := Eq.symm $ funext (Region.vwk_vwk ρ σ)

def Region.vwk0 : Region φ → Region φ := vwk Nat.succ

def Region.vwk1 : Region φ → Region φ := vwk (Nat.liftWk Nat.succ)

def Region.vwk2 : Region φ → Region φ := vwk (Nat.liftnWk 2 Nat.succ)

def Region.vwk3 : Region φ → Region φ := vwk (Nat.liftnWk 3 Nat.succ)

def Region.vwk4 : Region φ → Region φ := vwk (Nat.liftnWk 4 Nat.succ)

theorem Region.vwk1_vwk1 (r : Region φ) : r.vwk1.vwk1 = r.vwk1.vwk2 := by
  simp only [vwk1, vwk2, vwk_vwk]; congr; funext k; cases k <;> rfl

theorem Region.vwk2_vwk1 (r : Region φ) : r.vwk1.vwk2 = r.vwk1.vwk1 := by rw [vwk1_vwk1]

theorem Region.vwk1_comp_vwk1 : vwk1 (φ := φ) ∘ vwk1 = vwk2 ∘ vwk1 := funext Region.vwk1_vwk1

theorem Region.vwk2_comp_vwk1 : vwk2 (φ := φ) ∘ vwk1 = vwk1 ∘ vwk1 := funext Region.vwk2_vwk1

def Region.vswap01 : Region φ → Region φ := vwk (Nat.swap0 1)

def Region.vswap02 : Region φ → Region φ := vwk (Nat.swap0 2)

def Region.vswap03 : Region φ → Region φ := vwk (Nat.swap0 3)

theorem Region.vwk_vwk1 (r : Region φ) : r.vwk1.vwk ρ = r.vwk (ρ ∘ Nat.liftWk Nat.succ)
  := by simp only [vwk1, vwk_vwk, <-Nat.liftWk_comp]

theorem Region.vwk_liftWk₂_vwk1_to_vwk (r : Region φ)
  : r.vwk1.vwk (Nat.liftWk (Nat.liftWk ρ)) = r.vwk (Nat.liftWk (Nat.succ ∘ ρ))
  := by rw [vwk_vwk1, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]

theorem Region.vwk_liftWk₂_vwk1 (r : Region φ)
  : r.vwk1.vwk (Nat.liftWk (Nat.liftWk ρ)) = (r.vwk (Nat.liftWk ρ)).vwk1
  := by rw [vwk_liftWk₂_vwk1_to_vwk, vwk1, vwk_vwk, Nat.liftWk_comp]

theorem Region.vwk_liftnWk₂_vwk1 (r : Region φ)
  : r.vwk1.vwk (Nat.liftnWk 2 ρ) = (r.vwk (Nat.liftWk ρ)).vwk1
  := by rw [Nat.liftnWk_two, <-vwk_liftWk₂_vwk1]; rfl

theorem Region.vwk1_vwk_liftWk (r : Region φ)
  : (r.vwk (Nat.liftWk ρ)).vwk1 = r.vwk1.vwk (Nat.liftnWk 2 ρ)
  := r.vwk_liftnWk₂_vwk1.symm

theorem Region.vwk_liftnWk₂_liftWk_vwk2 (r : Region φ)
  : (r.vwk (Nat.liftnWk 2 Nat.succ)).vwk (Nat.liftnWk 2 (Nat.liftWk ρ))
  = (r.vwk (Nat.liftnWk 2 ρ)).vwk (Nat.liftnWk 2 Nat.succ)
  := by simp only [vwk_vwk, <-Nat.liftnWk_comp, Nat.liftWk_comp_succ]

theorem Region.vwk_liftnWk₂_vwk2 (r : Region φ)
  : r.vwk2.vwk (Nat.liftnWk 2 (Nat.liftWk ρ))
  = (r.vwk (Nat.liftnWk 2 ρ)).vwk2
  := vwk_liftnWk₂_liftWk_vwk2 r

def Region.vwk1n (n : ℕ) : Region φ → Region φ := vwk (Nat.liftWk (· + n))

theorem Region.lwk_id (r : Region φ) : r.lwk id = r := by induction r <;> simp [*]

@[simp]
theorem Region.lwk_of_id : @lwk φ id = id := funext lwk_id

theorem Region.lwk_id' : (r : Region φ) → r.lwk (λx => x) = r := lwk_id

@[simp]
theorem Region.lwk_of_id' : @lwk φ (λx => x) = id := funext lwk_id

theorem Region.lwk_lwk (σ τ : ℕ → ℕ) (r : Region φ) : (r.lwk τ).lwk σ = r.lwk (σ ∘ τ) := by
  induction r generalizing σ τ <;> simp [Nat.liftnWk_comp, *]

theorem Region.comp_lwk (ρ σ)
  : lwk ρ ∘ lwk σ = @lwk φ (ρ ∘ σ) := funext (Region.lwk_lwk ρ σ)

theorem Region.lwk_comp (ρ σ)
  : @lwk φ (ρ ∘ σ) = lwk ρ ∘ lwk σ := Eq.symm $ funext (Region.lwk_lwk ρ σ)

theorem Region.lwk_vwk (t : Region φ) : (t.vwk ρ).lwk σ = (t.lwk σ).vwk ρ := by
  induction t generalizing ρ σ <;> simp [*]

theorem Region.vwk_lwk (t : Region φ) : (t.lwk σ).vwk ρ = (t.vwk ρ).lwk σ := t.lwk_vwk.symm

theorem Region.lwk_comp_vwk : @lwk φ ρ ∘ vwk σ = vwk σ ∘ lwk ρ := funext Region.lwk_vwk

theorem Region.vwk_comp_lwk : @vwk φ σ ∘ lwk ρ = lwk ρ ∘ vwk σ := funext Region.vwk_lwk

theorem Region.lwk_vwk1 (t : Region φ) : t.vwk1.lwk ρ = (t.lwk ρ).vwk1 := lwk_vwk t

theorem Region.vwk1_lwk (t : Region φ) : (t.lwk ρ).vwk1 = t.vwk1.lwk ρ := t.lwk_vwk1.symm

def Region.lwk0 : Region φ → Region φ := lwk Nat.succ

def Region.lwk1 : Region φ → Region φ := lwk (Nat.liftWk Nat.succ)

theorem Region.lwk0_vwk1 (r : Region φ) : r.vwk1.lwk0 = r.lwk0.vwk1 := by rw [vwk1, lwk0, vwk_lwk]

theorem Region.vwk1_lwk0 (r : Region φ) : r.lwk0.vwk1 = r.vwk1.lwk0 := r.lwk0_vwk1.symm

theorem Region.lwk1_vwk1 (r : Region φ) : r.vwk1.lwk1= r.lwk1.vwk1 := by rw [vwk1, lwk1, vwk_lwk]

theorem Region.vwk1_lwk1 (r : Region φ) : r.lwk1.vwk1 = r.vwk1.lwk1 := r.lwk1_vwk1.symm

theorem Region.lwk1_vwk (r : Region φ) : (r.vwk ρ).lwk1 = r.lwk1.vwk ρ := by rw [lwk1, vwk_lwk]

theorem Region.vwk_lwk1 (r : Region φ) : r.lwk1.vwk ρ = (r.vwk ρ).lwk1 := r.lwk1_vwk.symm

theorem Region.lwk_addCases (i : Fin (n + m)) (G : Fin n → Region φ) (G' : Fin m → Region φ)
  : (Fin.addCases (motive := λ_ => Region φ) G G' i).lwk ρ
  = Fin.addCases (motive := λ_ => Region φ) (lwk ρ ∘ G) (lwk ρ ∘ G') i
  := by simp only [Fin.addCases]; split <;> simp

theorem Region.lwk_addCases' (i : Fin (n + m)) (G : Fin n → Region φ) (G' : Fin m → Region φ)
  : (Fin.addCases (motive := λ_ => Region φ) G G' i).lwk ρ
  = Fin.addCases (motive := λ_ => Region φ) (λi => (G i).lwk ρ) (λi => (G' i).lwk ρ) i
  := by simp only [Fin.addCases]; split <;> simp

theorem Region.vwk_addCases (i : Fin (n + m)) (G : Fin n → Region φ) (G' : Fin m → Region φ)
  : (Fin.addCases (motive := λ_ => Region φ) G G' i).vwk ρ
  = Fin.addCases (motive := λ_ => Region φ) (vwk ρ ∘ G) (vwk ρ ∘ G') i
  := by simp only [Fin.addCases]; split <;> simp

theorem Region.vwk_addCases' (i : Fin (n + m)) (G : Fin n → Region φ) (G' : Fin m → Region φ)
  : (Fin.addCases (motive := λ_ => Region φ) G G' i).vwk ρ
  = Fin.addCases (motive := λ_ => Region φ) (λi => (G i).vwk ρ) (λi => (G' i).vwk ρ) i
  := by simp only [Fin.addCases]; split <;> simp

theorem CFG.vwk_id (G : CFG φ) : G.vwk id = G := by cases G; simp [vwk]

@[simp]
theorem CFG.vwk_of_id : @vwk φ id = id := funext vwk_id

theorem CFG.vwk_id' : (G : CFG φ) → G.vwk (λx => x) = G := vwk_id

@[simp]
theorem CFG.vwk_of_id' : @vwk φ (λx => x) = id := funext vwk_id

theorem CFG.vwk_vwk (σ τ : ℕ → ℕ) (G : CFG φ) : (G.vwk τ).vwk σ = G.vwk (σ ∘ τ)
  := by cases G; simp only [CFG.vwk, Region.vwk_vwk, *]

theorem CFG.comp_vwk (ρ σ)
  : vwk ρ ∘ vwk σ = @vwk φ (ρ ∘ σ) := funext (CFG.vwk_vwk ρ σ)

theorem CFG.vwk_comp (ρ σ)
  : @vwk φ (ρ ∘ σ) = vwk ρ ∘ vwk σ := Eq.symm $ funext (CFG.vwk_vwk ρ σ)

def CFG.vwk1 : CFG φ → CFG φ := vwk (Nat.liftWk Nat.succ)

def CFG.vwkn (n : ℕ) : CFG φ → CFG φ := vwk (Nat.liftWk (· + n))

theorem CFG.lwk_id (G : CFG φ) : G.lwk id = G := by cases G; simp [lwk]

@[simp]
theorem CFG.lwk_of_id : @lwk φ id = id := funext lwk_id

theorem CFG.lwk_id' : (G : CFG φ) → G.lwk (λx => x) = G := lwk_id

@[simp]
theorem CFG.lwk_of_id' : @lwk φ (λx => x) = id := funext lwk_id

theorem CFG.lwk_lwk (σ τ : ℕ → ℕ) (G : CFG φ) : (G.lwk τ).lwk σ = G.lwk (σ ∘ τ)
  := by cases G; simp only [CFG.lwk, Nat.liftnWk_comp, Region.lwk_lwk, *]

theorem CFG.comp_lwk (ρ σ)
  : lwk ρ ∘ lwk σ = @lwk φ (ρ ∘ σ) := funext (CFG.lwk_lwk ρ σ)

theorem CFG.lwk_comp (ρ σ)
  : @lwk φ (ρ ∘ σ) = lwk ρ ∘ lwk σ := Eq.symm $ funext (CFG.lwk_lwk ρ σ)

theorem TCFG.toCFG_vwk (ρ : ℕ → ℕ) (G : TCFG φ) : (G.vwk ρ).toCFG = G.toCFG.vwk ρ
  := by cases G; simp [toCFG, TRegion.toRegion_vwk]

theorem TCFG.coe_toCFG_vwk (ρ : ℕ → ℕ) (G : TCFG φ)
  : (G.vwk ρ : CFG φ) = (G : CFG φ).vwk ρ := toCFG_vwk ρ G

theorem TCFG.toCFG_lwk (ρ : ℕ → ℕ) (G : TCFG φ) : (G.lwk ρ).toCFG = G.toCFG.lwk ρ
  := by cases G; simp [toCFG, TRegion.toRegion_lwk]

theorem TCFG.coe_toCFG_lwk (ρ : ℕ → ℕ) (G : TCFG φ)
  : (G.lwk ρ : CFG φ) = (G : CFG φ).lwk ρ := toCFG_lwk ρ G

end Weakening

/-
CLEANUP CORNER:
- Coercion naming
-/

/-
SPECULATION CORNER:
- Term φ could make φ into the usual higher-ert/discretion style parametrized calculus
- Body φ could have let and dlet; or a more general PBody which could be a list of patterned-lets
  - PBody could just be a list of patterned-lets, too
  - A single-let variant with projections is also a good idea...
-/
