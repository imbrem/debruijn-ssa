import Discretion.Discrete
import DeBruijnSSA.SingleApp.Syntax
import DeBruijnSSA.InstSet

namespace SingleApp

variable [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Zero ε]

  inductive Ty (α : Type u) where
  | base : α → Ty α
  | pair : Ty α → Ty α → Ty α
  | unit : Ty α
  | bool : Ty α
  deriving Repr, DecidableEq

inductive Ty.LE : Ty α → Ty α → Prop where
  | base {x y} : x ≤ y → LE (base x) (base y)
  | pair {x₁ x₂ y₁ y₂} : LE x₁ y₁ → LE x₂ y₂ → LE (pair x₁ x₂) (pair y₁ y₂)
  | unit : LE unit unit
  | bool : LE bool bool

theorem Ty.LE.refl : ∀{A : Ty α}, LE A A
  | Ty.base x => base (le_refl x)
  | Ty.pair _ _ => pair refl refl
  | Ty.unit => unit
  | Ty.bool => bool

theorem Ty.LE.trans : ∀{A B C : Ty α}, LE A B → LE B C → LE A C
  | _, _, _, base h, base h' => base (le_trans h h')
  | _, _, _, pair h₁ h₂, pair h₁' h₂' => pair (h₁.trans h₁') (h₂.trans h₂')
  | _, _, _, unit, unit => unit
  | _, _, _, bool, bool => bool

theorem Ty.LE.antisymm : ∀{A B : Ty α}, LE A B → LE B A → A = B
  | _, _, base h, base h' => by rw [le_antisymm h h']
  | _, _, pair h₁ h₂, pair h₁' h₂' => by rw [Ty.LE.antisymm h₁ h₁', Ty.LE.antisymm h₂ h₂']
  | _, _, unit, unit => rfl
  | _, _, bool, bool => rfl

instance : PartialOrder (Ty α) where
  le := Ty.LE
  le_refl _ := Ty.LE.refl
  le_trans _ _ _ := Ty.LE.trans
  le_antisymm _ _ := Ty.LE.antisymm

-- TODO: Ty.LE is decidable if α is

-- TODO: Ty.LE is a discrete order if α is

def Ctx (α ε) := List (Ty α × ε)

structure Ctx.Var (Γ : Ctx α ε) (n : ℕ) (A : Ty α) (e : ε) : Prop where
  length : n < Γ.length
  get : Γ.get ⟨n, length⟩ ≤ ⟨A, e⟩

theorem Ctx.Var.wk_eff
  {Γ : Ctx α ε} {n : ℕ} {A : Ty α} {e e' : ε}
  (h : e ≤ e') (hΓ : Γ.Var n A e) : Γ.Var n A e' where
  length := hΓ.length
  get := le_trans hΓ.get (by simp [h])

instance : Append (Ctx α ε) := (inferInstance : Append (List (Ty α × ε)))

def FCtx (α ε) := Σn, Fin n → Ty α × ε

-- TODO: FCtx append

inductive Term.Wf : Ctx α ε → Term φ → Ty α → ε → Prop
| var {Γ n A e} : Γ.Var n A e → Wf Γ (var n) A e
| op {f : φ} {a e A B} : Φ.Fn f A B e → Wf Γ a A e → Wf Γ (op f a) B e
| pair {a b A B e} : Wf Γ a A e → Wf Γ b B e → Wf Γ (pair a b) (Ty.pair A B) e
| unit (e) : Wf Γ unit Ty.unit e
| bool (b e) : Wf Γ (bool b) Ty.bool e

inductive Term.WfD : Ctx α ε → Term φ → Ty α → ε → Type _
| var : Γ.Var n A e → WfD Γ (var n) A e
| op : Φ.Fn f A B e → WfD Γ a A e → WfD Γ (op f a) B e
| pair : WfD Γ a A e → WfD Γ b B e → WfD Γ (pair a b) (Ty.pair A B) e
| unit (e) : WfD Γ unit Ty.unit e
| bool (b e) : WfD Γ (bool b) Ty.bool e

-- TODO: WfD ==> Wf

-- TODO: Wf ==> ∃WfD

/-- Weaken the effect of a term -/
def Term.WfD.wk_eff
  {Γ : Ctx α ε} {a : Term φ} {A e} (h : e ≤ e') : WfD Γ a A e → WfD Γ a A e'
  | var dv => var (dv.wk_eff h)
  | op df de => op (df.wk_eff h) (de.wk_eff h)
  | pair dl dr => pair (dl.wk_eff h) (dr.wk_eff h)
  | unit e => unit e'
  | bool b e => bool b e'

-- TODO: effect and type weakening

-- TODO: Weakening

-- TODO: for a discrete order on α, WfD unique, Wf ==> WfD

-- TODO: FWfD, FWf, associated lore

-- TODO: label contexts; should these just be regular contexts with inverse weakening?

def LCtx (α) := List (Ty α)

structure LCtx.Trg (L : LCtx α) (n : ℕ) (A : Ty α) : Prop where
  length : n < L.length
  get : A ≤ L.get ⟨n, length⟩

instance : Append (LCtx α) := (inferInstance : Append (List (Ty α)))

def FLCtx (α) := Σn, Fin n → Ty α

-- TODO: FLCtx append

inductive Terminator.WfD : Ctx α ε → Terminator φ → LCtx α → Type _
  | br : L.Trg n A → a.WfD Γ A 0 → WfD Γ (br n a) L
  | ite : e.WfD Γ Ty.bool 0 → s.WfD Γ L → t.WfD Γ L → WfD Γ (ite e s t) L

-- TODO: weakening

-- TODO: label-weakening

inductive Body.WfD : Ctx α ε → Body φ → Ctx α ε → Type _
  | nil : WfD Γ nil []
  | let1 : a.WfD Γ A e → b.WfD (⟨A, e⟩::Γ) Δ → (let1 a b).WfD Γ (⟨A, e⟩::Δ)
  | let2 : a.WfD Γ (Ty.pair A B) e
    → b.WfD (⟨A, e⟩::⟨B, e⟩::Γ) Δ
    → (let2 a b).WfD Γ (⟨A, e⟩::⟨B, e⟩::Δ)

-- TODO: weakening

structure Block.WfD (Γ : Ctx α ε) (β : Block φ) (Δ : Ctx α ε) (L : LCtx α) where
  body : β.body.WfD Γ Δ
  terminator : β.terminator.WfD (Δ ++ Γ) L

-- TODO: weakening

-- TODO: label-weakening

inductive BBRegion.WfD : Ctx α ε → BBRegion φ → LCtx α → Type _
  | cfg {Δ} : β.WfD Γ Δ K → (∀i : Fin n, (G i).WfD (Δ ++ Γ) K)
    → L = K.drop n → BBRegion.WfD Γ (cfg β n G) L

-- TODO: weakening

-- TODO: label-weakening

inductive TRegion.WfD : Ctx α ε → TRegion φ → LCtx α → Type _
  | let1 : a.WfD Γ A e → t.WfD (⟨A, e⟩::Γ) L → (let1 a t).WfD Γ L
  | let2 : a.WfD Γ (Ty.pair A B) e → t.WfD (⟨A, e⟩::⟨B, e⟩::Γ) L → (let2 a t).WfD Γ L
  | cfg : t.WfD Γ K → (∀i : Fin n, (G i).WfD Γ K) → L = K.drop n → WfD Γ (cfg t n G) L

-- TODO: weakening

-- TODO: label-weakening

inductive Region.WfD [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Zero ε]
    : Ctx α ε → Region φ → LCtx α → Type _
  | br : L.Trg n A → a.WfD Γ A 0 → WfD Γ (br n a) L
  | ite : e.WfD Γ Ty.bool 0 → s.WfD Γ L → t.WfD Γ L → WfD Γ (ite e s t) L
  | let1 : a.WfD Γ A e → t.WfD (⟨A, e⟩::Γ) L → (let1 a t).WfD Γ L
  | let2 : a.WfD Γ (Ty.pair A B) e → t.WfD (⟨A, e⟩::⟨B, e⟩::Γ) L → (let2 a t).WfD Γ L
  | cfg : β.WfD Γ K → (∀i : Fin n, (G i).WfD Γ K) → L = K.drop n → WfD Γ (cfg β n G) L

-- TODO: weakening

-- TODO: label-weakening

-- TODO: normalize region to TRegion; type preservation

-- TODO: normalize TRegion to BBRegion; type preservation

-- == SPECULATIVE ==

-- TODO: substitution-terminator typing

-- TODO: substitution-CFG typing

-- TODO: _partial_ substitutions for more standard SSA? parameter tagging?

-- TODO: 3 address code via var-only substitution; everything trivially SSA with preserved vars
-- via id-substitution.

end SingleApp
