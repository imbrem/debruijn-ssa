
import Discretion.Wk.List
import Discretion.Basic
import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Fv.Basic
import DeBruijnSSA.BinSyntax.Syntax.Effect.Definitions

namespace BinSyntax

-- TODO: assert effect for e.g. terminators is pure rather than use 0?

-- Can we even do centrality? Propositional parametrization?

inductive Ty (α : Type u) where
  | base : α → Ty α
  | prod : Ty α → Ty α → Ty α
  | coprod : Ty α → Ty α → Ty α
  | unit : Ty α
  | empty : Ty α
  deriving Repr, DecidableEq

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]

inductive Ty.IsInitial : Ty α → Prop
  | prod_left : ∀{A}, IsInitial A → IsInitial (prod A B)
  | prod_right : ∀{B}, IsInitial B → IsInitial (prod A B)
  | coprod : ∀{A B}, IsInitial A → IsInitial B → IsInitial (coprod A B)
  | empty : IsInitial empty

inductive Ty.LE : Ty α → Ty α → Prop where
  | base {x y} : x ≤ y → LE (base x) (base y)
  | prod {x₁ x₂ y₁ y₂} : LE x₁ y₁ → LE x₂ y₂ → LE (prod x₁ x₂) (prod y₁ y₂)
  | coprod {x₁ x₂ y₁ y₂} : LE x₁ y₁ → LE x₂ y₂ → LE (coprod x₁ x₂) (coprod y₁ y₂)
  | unit : LE unit unit
  | empty : LE empty empty

theorem Ty.LE.prod_left {A A' B B' : Ty α} (h : LE (Ty.prod A B) (Ty.prod A' B')) : LE A A'
  := by cases h; assumption

theorem Ty.LE.prod_right {A A' B B' : Ty α} (h : LE (Ty.prod A B) (Ty.prod A' B')) : LE B B'
  := by cases h; assumption

theorem Ty.LE.coprod_left {A A' B B' : Ty α} (h : LE (Ty.coprod A B) (Ty.coprod A' B')) : LE A A'
  := by cases h; assumption

theorem Ty.LE.coprod_right {A A' B B' : Ty α} (h : LE (Ty.coprod A B) (Ty.coprod A' B')) : LE B B'
  := by cases h; assumption

theorem Ty.LE.refl : ∀{A : Ty α}, LE A A
  | Ty.base x => base (le_refl x)
  | Ty.prod _ _ => prod refl refl
  | Ty.coprod _ _ => coprod refl refl
  | Ty.unit => unit
  | Ty.empty => empty

theorem Ty.LE.trans : ∀{A B C : Ty α}, LE A B → LE B C → LE A C
  | _, _, _, base h, base h' => base (le_trans h h')
  | _, _, _, prod h₁ h₂, prod h₁' h₂' => prod (h₁.trans h₁') (h₂.trans h₂')
  | _, _, _, coprod h₁ h₂, coprod h₁' h₂' => coprod (h₁.trans h₁') (h₂.trans h₂')
  | _, _, _, unit, unit => unit
  | _, _, _, empty, empty => empty

theorem Ty.LE.antisymm : ∀{A B : Ty α}, LE A B → LE B A → A = B
  | _, _, base h, base h' => by rw [le_antisymm h h']
  | _, _, prod h₁ h₂, prod h₁' h₂' => by rw [Ty.LE.antisymm h₁ h₁', Ty.LE.antisymm h₂ h₂']
  | _, _, coprod h₁ h₂, coprod h₁' h₂' => by rw [Ty.LE.antisymm h₁ h₁', Ty.LE.antisymm h₂ h₂']
  | _, _, unit, unit => rfl
  | _, _, empty, empty => rfl

instance : PartialOrder (Ty α) where
  le := Ty.LE
  le_refl _ := Ty.LE.refl
  le_trans _ _ _ := Ty.LE.trans
  le_antisymm _ _ := Ty.LE.antisymm

-- TODO: Ty.LE is decidable if ≤ on α is

theorem Ty.LE.eq [d : DiscreteOrder α] {A B : Ty α} : LE A B → A = B
  | base h => by rw [d.le_eq _ _ h]
  | prod h₁ h₂ => by rw [eq h₁, eq h₂]
  | coprod h₁ h₂ => by rw [eq h₁, eq h₂]
  | unit => rfl
  | empty => rfl

instance [DiscreteOrder α] : DiscreteOrder (Ty α) where
  le_eq _ _ := Ty.LE.eq

theorem Ty.IsInitial.mono {A B : Ty α} (h : A ≤ B) (hi : IsInitial A) : IsInitial B
  := by induction h with
  | prod _ _ Il Ir => cases hi with
    | prod_left hl => exact prod_left (Il hl)
    | prod_right hr => exact prod_right (Ir hr)
  | coprod _ _ Il Ir => cases hi with | coprod hl hr => exact coprod (Il hl) (Ir hr)
  | _ => cases hi <;> constructor

theorem Ty.IsInitial.anti {A B : Ty α} (h : A ≤ B) (hi : IsInitial B) : IsInitial A
  := by induction h with
  | prod _ _ Il Ir => cases hi with
    | prod_left hl => exact prod_left (Il hl)
    | prod_right hr => exact prod_right (Ir hr)
  | coprod _ _ Il Ir => cases hi with | coprod hl hr => exact coprod (Il hl) (Ir hr)
  | _ => cases hi <;> constructor
