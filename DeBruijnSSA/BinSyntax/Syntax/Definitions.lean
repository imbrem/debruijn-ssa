import Discretion.Wk.Fun

namespace BinSyntax

/-! ### Basic syntax definitions

Free variables and simple coercions are given immediately after each definition to give an idea of how
the de-Bruijn indices are supposed to be interpreted.
 -/
section Definitions

/-- A simple term, consisting of variables, operations, pairs, units, and booleans -/
inductive Term (φ : Type) where
  | var : ℕ → Term φ
  | op : φ → Term φ → Term φ
  | pair : Term φ → Term φ → Term φ
  | unit : Term φ
  | inl : Term φ → Term φ
  | inr : Term φ → Term φ

/-- Rename the variables in a `Term` using `ρ` -/
@[simp]
def Term.wk (ρ : ℕ → ℕ) : Term φ → Term φ
  | var x => var (ρ x)
  | op f e => op f (wk ρ e)
  | pair l r => pair (wk ρ l) (wk ρ r)
  | unit => unit
  | inl a => inl (wk ρ a)
  | inr a => inr (wk ρ a)

/-- A basic block body, which consists of a sequence of variable definitions -/
inductive Body (φ : Type) : Type
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
inductive Terminator (φ : Type) : Type
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
structure Block (φ : Type) : Type where
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
inductive BBRegion (φ : Type) : Type
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
structure BBCFG (φ : Type) : Type where
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
inductive TRegion (φ : Type) : Type
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
structure TCFG (φ : Type) : Type where
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
inductive Region (φ : Type) : Type
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
    simp only [heq_eq_eq, Function.funext_iff, *]
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

/-- Rename the labels in a `Region` using `ρ` -/
@[simp]
def Region.lwk (ρ : ℕ → ℕ) : Region φ → Region φ
  | br n e => br (ρ n) e
  | case e s t => case e (lwk ρ s) (lwk ρ t)
  | let1 e t => let1 e (lwk ρ t)
  | let2 e t => let2 e (lwk ρ t)
  | cfg β n f => cfg (lwk (Nat.liftnWk n ρ) β) n (λ i => (f i).lwk (Nat.liftnWk n ρ))

/-- A control-flow graph with `length` entry-point regions -/
structure CFG (φ : Type) : Type where
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

@[simp]
theorem Term.wk_id (t : Term φ) : t.wk id = t := by induction t <;> simp [*]

@[simp]
theorem Term.wk_id' : (t : Term φ) -> t.wk (λx => x) = t := wk_id

theorem Term.wk_wk (σ : ℕ → ℕ) (ρ : ℕ → ℕ) (t : Term φ)
  : t.wk (ρ ∘ σ) = (t.wk σ).wk ρ := by induction t <;> simp [*]

@[simp]
theorem Body.wk_id (b : Body φ) : b.wk id = b := by induction b <;> simp [*]

@[simp]
theorem Body.wk_id' : (b : Body φ) → b.wk (λx => x) = b := wk_id

theorem Body.wk_wk (σ τ : ℕ → ℕ) (b : Body φ)
  : b.wk (σ ∘ τ) = (b.wk τ).wk σ := by
  induction b generalizing σ τ
  <;> simp [Term.wk_wk, Nat.liftWk_comp, Nat.liftnWk_comp, *]

@[simp]
theorem Body.num_defs_wk (ρ : ℕ → ℕ) (b : Body φ) : (b.wk ρ).num_defs = b.num_defs := by
  induction b generalizing ρ <;> simp [*]

@[simp]
theorem Terminator.vwk_id (r : Terminator φ) : r.vwk id = r := by
  induction r <;> simp [Nat.liftnWk_id, *]

@[simp]
theorem Terminator.vwk_id' : (r : Terminator φ) → r.vwk (λx => x) = r := vwk_id

theorem Terminator.vwk_vwk (σ τ : ℕ → ℕ) (r : Terminator φ)
  : r.vwk (σ ∘ τ) = (r.vwk τ).vwk σ := by
  induction r generalizing σ τ
  <;> simp [Term.wk_wk, Nat.liftWk_comp, Nat.liftnWk_comp, *]

theorem Terminator.vwk_comp (ρ σ)
  : @vwk φ (ρ ∘ σ) = vwk ρ ∘ vwk σ := funext (Terminator.vwk_vwk ρ σ)

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

@[simp]
theorem Terminator.lwk_id (r : Terminator φ) : r.lwk id = r := by
  induction r <;> simp [Nat.liftnWk_id, *]

@[simp]
theorem Terminator.lwk_id' : (t : Terminator φ) → t.lwk (λx => x) = t := lwk_id

theorem Terminator.lwk_lwk (σ τ : ℕ → ℕ) (t : Terminator φ)
  : t.lwk (σ ∘ τ) = (t.lwk τ).lwk σ := by
  induction t generalizing σ τ <;> simp [Nat.liftnWk_comp, *]

theorem Terminator.toBlock_lwk (ρ : ℕ → ℕ) (t : Terminator φ) : (t.lwk ρ).toBlock = t.toBlock.lwk ρ
  := rfl

theorem Terminator.coe_toBlock_lwk (ρ : ℕ → ℕ) (t : Terminator φ)
  : (t.lwk ρ : Block φ) = (t : Block φ).lwk ρ := rfl

theorem Terminator.lwk_vwk (t : Terminator φ) : (t.vwk ρ).lwk σ = (t.lwk σ).vwk ρ := by
  induction t generalizing ρ σ <;> simp [*]

theorem Terminator.vwk_lwk (t : Terminator φ) : (t.lwk σ).vwk ρ = (t.vwk ρ).lwk σ := t.lwk_vwk.symm

theorem Terminator.lwk_comp_vwk : @lwk φ ρ ∘ vwk σ = vwk σ ∘ lwk ρ := funext Terminator.lwk_vwk

theorem Terminator.vwk_comp_lwk : @vwk φ σ ∘ lwk ρ = lwk ρ ∘ vwk σ := funext Terminator.vwk_lwk

@[simp]
theorem Block.vwk_id (β : Block φ) : β.vwk id = β := by simp

@[simp]
theorem Block.vwk_id' : (β : Block φ) → β.vwk (λx => x) = β := vwk_id

theorem Block.vwk_vwk (σ τ : ℕ → ℕ) (β : Block φ) : β.vwk (σ ∘ τ) = (β.vwk τ).vwk σ
  := by simp [Body.wk_wk, Terminator.vwk_vwk, Nat.liftnWk_comp, *]

@[simp]
theorem Block.lwk_id (β : Block φ) : β.lwk id = β := by simp

@[simp]
theorem Block.lwk_id' : (β : Block φ) → β.lwk (λx => x) = β := lwk_id

theorem Block.lwk_lwk (σ τ : ℕ → ℕ) (β : Block φ) : β.lwk (σ ∘ τ) = (β.lwk τ).lwk σ
  := by simp [Terminator.lwk_lwk]

@[simp]
theorem BBRegion.vwk_id (r : BBRegion φ) : r.vwk id = r := by
  induction r; simp [*]

@[simp]
theorem BBRegion.vwk_id' : (r : BBRegion φ) → r.vwk (λx => x) = r := vwk_id

theorem BBRegion.vwk_vwk (σ τ : ℕ → ℕ) (r : BBRegion φ)
  : r.vwk (σ ∘ τ) = (r.vwk τ).vwk σ := by
  induction r generalizing σ τ
  simp [Body.wk_wk, Terminator.vwk_vwk, Body.num_defs_wk, Nat.liftWk_comp, Nat.liftnWk_comp, *]

@[simp]
theorem BBRegion.lwk_id (r : BBRegion φ) : r.lwk id = r := by
  induction r; simp [*]

@[simp]
theorem BBRegion.lwk_id' : (r : BBRegion φ) → r.lwk (λx => x) = r := lwk_id

theorem BBRegion.lwk_lwk (σ τ : ℕ → ℕ) (r : BBRegion φ)
  : r.lwk (σ ∘ τ) = (r.lwk τ).lwk σ := by
  induction r generalizing σ τ
  simp [Body.wk_wk, Terminator.lwk_lwk, Nat.liftnWk_comp, *]

@[simp]
theorem BBCFG.vwk_id (cfg : BBCFG φ) : cfg.vwk id = cfg := by
  cases cfg; simp [*]

@[simp]
theorem BBCFG.vwk_id' : (cfg : BBCFG φ) → cfg.vwk (λx => x) = cfg := vwk_id

theorem BBCFG.vwk_vwk (σ τ : ℕ → ℕ) (cfg : BBCFG φ) : cfg.vwk (σ ∘ τ) = (cfg.vwk τ).vwk σ := by
  cases cfg; simp [BBRegion.vwk_vwk, *]

@[simp]
theorem BBCFG.lwk_id (cfg : BBCFG φ) : cfg.lwk id = cfg := by
  cases cfg; simp [*]

@[simp]
theorem BBCFG.lwk_id' : (cfg : BBCFG φ) → cfg.lwk (λx => x) = cfg := lwk_id

theorem BBCFG.lwk_lwk (σ τ : ℕ → ℕ) (cfg : BBCFG φ) : cfg.lwk (σ ∘ τ) = (cfg.lwk τ).lwk σ := by
  cases cfg; simp [BBRegion.lwk_lwk, *]

@[simp]
theorem TRegion.vwk_id (r : TRegion φ) : r.vwk id = r := by
  induction r <;> simp [TRegion.vwk, *]

@[simp]
theorem TRegion.vwk_id' : (r : TRegion φ) → r.vwk (λx => x) = r := vwk_id

theorem TRegion.vwk_vwk (σ τ : ℕ → ℕ) (r : TRegion φ)
  : r.vwk (σ ∘ τ) = (r.vwk τ).vwk σ := by
  induction r generalizing σ τ
  <;> simp [Term.wk_wk, Terminator.vwk_vwk, Nat.liftWk_comp, Nat.liftnWk_comp, *]

theorem TRegion.toRegion_vwk (ρ : ℕ → ℕ) (t : TRegion φ) : (t.vwk ρ).toRegion = t.toRegion.vwk ρ
  := by induction t generalizing ρ <;> simp [Terminator.toRegion_vwk, *]

theorem TRegion.coe_toRegion_vwk (ρ : ℕ → ℕ) (t : TRegion φ)
  : (t.vwk ρ : Region φ) = (t : Region φ).vwk ρ := toRegion_vwk ρ t

@[simp]
theorem TRegion.lwk_id (r : TRegion φ) : r.lwk id = r := by
  induction r <;> simp [TRegion.lwk, *]

@[simp]
theorem TRegion.lwk_id' : (r : TRegion φ) → r.lwk (λx => x) = r := lwk_id

theorem TRegion.lwk_lwk (σ τ : ℕ → ℕ) (r : TRegion φ)
  : r.lwk (σ ∘ τ) = (r.lwk τ).lwk σ := by
  induction r generalizing σ τ
  <;> simp [Term.wk_wk, Terminator.lwk_lwk, Nat.liftnWk_comp, *]

theorem TRegion.toRegion_lwk (ρ : ℕ → ℕ) (t : TRegion φ) : (t.lwk ρ).toRegion = t.toRegion.lwk ρ
  := by induction t generalizing ρ <;> simp [Terminator.toRegion_lwk, *]

theorem TRegion.coe_toRegion_lwk (ρ : ℕ → ℕ) (t : TRegion φ)
  : (t.lwk ρ : Region φ) = (t : Region φ).lwk ρ := toRegion_lwk ρ t

@[simp]
theorem TCFG.vwk_id (cfg : TCFG φ) : cfg.vwk id = cfg := by
  cases cfg; simp [*]

@[simp]
theorem TCFG.vwk_id' : (cfg : TCFG φ) → cfg.vwk (λx => x) = cfg := vwk_id

theorem TCFG.vwk_vwk (σ τ : ℕ → ℕ) (cfg : TCFG φ) : cfg.vwk (σ ∘ τ) = (cfg.vwk τ).vwk σ := by
  cases cfg; simp [TRegion.vwk_vwk, *]

@[simp]
theorem TCFG.lwk_id (cfg : TCFG φ) : cfg.lwk id = cfg := by
  cases cfg; simp [TCFG.lwk, *]

@[simp]
theorem TCFG.lwk_id' : (cfg : TCFG φ) → cfg.lwk (λx => x) = cfg := lwk_id

theorem TCFG.lwk_lwk (σ τ : ℕ → ℕ) (cfg : TCFG φ) : cfg.lwk (σ ∘ τ) = (cfg.lwk τ).lwk σ := by
  cases cfg; simp [TCFG.lwk, TRegion.lwk_lwk, Nat.liftnWk_comp, *]

@[simp]
theorem Region.vwk_id (r : Region φ) : r.vwk id = r := by
  induction r <;> simp [Region.vwk, Nat.liftnWk_id, *]

@[simp]
theorem Region.vwk_id' : (r : Region φ) → r.vwk (λx => x) = r := vwk_id

theorem Region.vwk_vwk (σ τ : ℕ → ℕ) (r : Region φ)
  : r.vwk (σ ∘ τ) = (r.vwk τ).vwk σ := by
  induction r generalizing σ τ
  <;> simp [vwk, Term.wk_wk, Nat.liftWk_comp, Nat.liftnWk_comp, *]

@[simp]
theorem Region.lwk_id (r : Region φ) : r.lwk id = r := by induction r <;> simp [*]

@[simp]
theorem Region.lwk_id' : (r : Region φ) → r.lwk (λx => x) = r := lwk_id

theorem Region.lwk_lwk (σ τ : ℕ → ℕ) (r : Region φ) : r.lwk (σ ∘ τ) = (r.lwk τ).lwk σ := by
  induction r generalizing σ τ <;> simp [Nat.liftnWk_comp, *]

@[simp]
theorem CFG.vwk_id (G : CFG φ) : G.vwk id = G := by cases G; simp [vwk]

@[simp]
theorem CFG.vwk_id' : (G : CFG φ) → G.vwk (λx => x) = G := vwk_id

theorem CFG.vwk_vwk (σ τ : ℕ → ℕ) (G : CFG φ) : G.vwk (σ ∘ τ) = (G.vwk τ).vwk σ
  := by cases G; simp only [CFG.vwk, Region.vwk_vwk, *]

@[simp]
theorem CFG.lwk_id (G : CFG φ) : G.lwk id = G := by cases G; simp [lwk]

@[simp]
theorem CFG.lwk_id' : (G : CFG φ) → G.lwk (λx => x) = G := lwk_id

theorem CFG.lwk_lwk (σ τ : ℕ → ℕ) (G : CFG φ) : G.lwk (σ ∘ τ) = (G.lwk τ).lwk σ
  := by cases G; simp only [CFG.lwk, Nat.liftnWk_comp, Region.lwk_lwk, *]

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
