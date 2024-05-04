import Discretion.Discrete
import DeBruijnSSA.SingleApp.Syntax
import DeBruijnSSA.InstSet

namespace SingleApp

inductive Ty (α : Type u) where
| base : α → Ty α
| pair : Ty α → Ty α → Ty α
| unit : Ty α
| bool : Ty α
deriving Repr, DecidableEq

inductive Ty.LE [PartialOrder α] : Ty α → Ty α → Prop where
| base {x y} : x ≤ y → LE (base x) (base y)
| pair {x₁ x₂ y₁ y₂} : LE x₁ y₁ → LE x₂ y₂ → LE (pair x₁ x₂) (pair y₁ y₂)
| unit : LE unit unit
| bool : LE bool bool

theorem Ty.LE.refl [PartialOrder α] : ∀{A : Ty α}, LE A A
| Ty.base x => base (le_refl x)
| Ty.pair _ _ => pair refl refl
| Ty.unit => unit
| Ty.bool => bool

theorem Ty.LE.trans [PartialOrder α] : ∀{A B C : Ty α}, LE A B → LE B C → LE A C
| _, _, _, base h, base h' => base (le_trans h h')
| _, _, _, pair h₁ h₂, pair h₁' h₂' => pair (h₁.trans h₁') (h₂.trans h₂')
| _, _, _, unit, unit => unit
| _, _, _, bool, bool => bool

theorem Ty.LE.antisymm [PartialOrder α] : ∀{A B : Ty α}, LE A B → LE B A → A = B
| _, _, base h, base h' => by rw [le_antisymm h h']
| _, _, pair h₁ h₂, pair h₁' h₂' => by rw [Ty.LE.antisymm h₁ h₁', Ty.LE.antisymm h₂ h₂']
| _, _, unit, unit => rfl
| _, _, bool, bool => rfl

instance [PartialOrder α] : PartialOrder (Ty α) where
  le := Ty.LE
  le_refl _ := Ty.LE.refl
  le_trans _ _ _ := Ty.LE.trans
  le_antisymm _ _ := Ty.LE.antisymm

-- TODO: Ty.LE is decidable if α is

-- TODO: Ty.LE is a discrete order if α is

def Ctx (α ε) := List (Ty α × ε)

def Ctx.var {α ε} [PartialOrder α] [PartialOrder ε] (Γ : Ctx α ε) (n : ℕ) (A : Ty α) (e : ε) : Prop
  := ∃h : n < Γ.length, Γ.get ⟨n, h⟩ ≤ ⟨A, e⟩

instance : Append (Ctx α ε) := (inferInstance : Append (List (Ty α × ε)))

def FCtx (α ε) := Σn, Fin n → Ty α × ε

-- TODO: FCtx append

inductive Term.Wf [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε]
  : Ctx α ε → Term φ → Ty α → ε → Prop
| var {Γ n A e} : Γ.var n A e → Wf Γ (var n) A e
| op {f : φ} {a e A B} : Φ.fn f A B e → Wf Γ a A e → Wf Γ (op f a) B e
| pair {a b A B e} : Wf Γ a A e → Wf Γ b B e → Wf Γ (pair a b) (Ty.pair A B) e
| unit (e) : Wf Γ unit Ty.unit e
| bool (b e) : Wf Γ (bool b) Ty.bool e

inductive Term.WfD [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε]
  : Ctx α ε → Term φ → Ty α → ε → Type _
| var : Γ.var n A e → WfD Γ (var n) A e
| op : Φ.fn f A B e → WfD Γ a A e → WfD Γ (op f a) B e
| pair : WfD Γ a A e → WfD Γ b B e → WfD Γ (pair a b) (Ty.pair A B) e
| unit (e) : WfD Γ unit Ty.unit e
| bool (b e) : WfD Γ (bool b) Ty.bool e

-- TODO: WfD ==> Wf

-- TODO: Wf ==> ∃WfD

-- TODO: effect and type weakening

-- TODO: Weakening

-- TODO: for a discrete order on α, WfD unique, Wf ==> WfD

-- TODO: FWfD, FWf, associated lore

-- TODO: label contexts; should these just be regular contexts with inverse weakening?

def LCtx (α) := List (Ty α)

def LCtx.trg {α} [PartialOrder α] (L : LCtx α) (n : ℕ) (A : Ty α) : Prop
  := ∃h : n < L.length, A ≤ L.get ⟨n, h⟩

instance : Append (LCtx α) := (inferInstance : Append (List (Ty α)))

def FLCtx (α) := Σn, Fin n → Ty α

-- TODO: FLCtx append

inductive Terminator.WfD [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Zero ε]
    : Ctx α ε → Terminator φ → LCtx α → Type _
  | br : L.trg n A → a.WfD Γ A 0 → WfD Γ (br n a) L
  | ite : e.WfD Γ Ty.bool 0 → s.WfD Γ L → t.WfD Γ L → WfD Γ (ite e s t) L

inductive Body.WfD [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε]
    : Ctx α ε → Body φ → Ctx α ε → Type _
  | nil : WfD Γ nil []
  | let1 : a.WfD Γ A e → b.WfD (⟨A, e⟩::Γ) Δ → (let1 a b).WfD Γ (⟨A, e⟩::Δ)
  | let2 : a.WfD Γ (Ty.pair A B) e
    → b.WfD (⟨A, e⟩::⟨B, e⟩::Γ) Δ
    → (let2 a b).WfD Γ (⟨A, e⟩::⟨B, e⟩::Δ)

structure Block.WfD [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Zero ε]
    (Γ : Ctx α ε) (β : Block φ) (L : LCtx α) where
    defs : Ctx α ε
    body : β.body.WfD Γ defs
    terminator : β.terminator.WfD (defs ++ Γ) L

inductive Region.WfD [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Zero ε]
    : Ctx α ε → Region φ → LCtx α → Type _
  | br : L.trg n A → a.WfD Γ A 0 → WfD Γ (br n a) L
  | ite : e.WfD Γ Ty.bool 0 → s.WfD Γ L → t.WfD Γ L → WfD Γ (ite e s t) L
  -- TODO: rest

-- TODO: "2D" label contexts

-- TODO: substitution-terminator typing

-- TODO: substitution-CFG typing

-- TODO: _partial_ substitutions for more standard SSA? parameter tagging?

-- TODO: 3 address code via var-only substitution; everything trivially SSA with preserved vars
-- via id-substitution.

end SingleApp
