
import Discretion.Wk.List
import Discretion.Order.Discrete
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

variable [Φ: EffInstSet φ (Ty α) ε]

inductive Ty.IsInitial : Ty α → Prop
  | prod_left : ∀{A}, IsInitial A → IsInitial (prod A B)
  | prod_right : ∀{B}, IsInitial B → IsInitial (prod A B)
  | coprod : ∀{A B}, IsInitial A → IsInitial B → IsInitial (coprod A B)
  | empty : IsInitial empty

theorem Ty.IsInitial.of_prod {A B : Ty α} : IsInitial (Ty.prod A B) → IsInitial A ∨ IsInitial B
  | prod_left hi => Or.inl hi
  | prod_right hi => Or.inr hi

@[simp]
theorem Ty.IsInitial.prod_iff {A B : Ty α} : IsInitial (Ty.prod A B) ↔ IsInitial A ∨ IsInitial B
  := ⟨of_prod, λ| Or.inl hi => prod_left hi | Or.inr hi => prod_right hi⟩

theorem Ty.IsInitial.coprod_left {A B : Ty α} (hi : IsInitial (Ty.coprod A B)) : IsInitial A
  := match hi with | coprod hi _ => hi

theorem Ty.IsInitial.coprod_right {A B : Ty α} (hi : IsInitial (Ty.coprod A B)) : IsInitial B
  := match hi with | coprod _ hi => hi

theorem Ty.IsInitial.of_coprod {A B : Ty α} : IsInitial (Ty.coprod A B) → IsInitial A ∧ IsInitial B
  | coprod hi₁ hi₂ => ⟨hi₁, hi₂⟩

@[simp]
theorem Ty.IsInitial.coprod_iff {A B : Ty α} : IsInitial (Ty.coprod A B) ↔ IsInitial A ∧ IsInitial B
  := ⟨of_coprod, λ| ⟨hi₁, hi₂⟩ => coprod hi₁ hi₂⟩

@[simp]
theorem Ty.IsInitial.empty' : IsInitial (Ty.empty (α := α))
  := empty

@[simp]
theorem Ty.IsInitial.unit : ¬IsInitial (Ty.unit (α := α))
  := λh => by cases h

@[simp]
theorem Ty.IsInitial.base {x : α} : ¬IsInitial (Ty.base x)
  := λh => by cases h

inductive Ty.IsTerminal : Ty α → Prop
  | prod : IsTerminal A → IsTerminal B → IsTerminal (prod A B)
  | coprod_left : IsTerminal A → IsInitial B → IsTerminal (coprod A B)
  | coprod_right : IsInitial A → IsTerminal B → IsTerminal (coprod A B)
  | unit : IsTerminal unit

theorem Ty.IsTerminal.prod_left {A B : Ty α} (h : IsTerminal (Ty.prod A B)) : IsTerminal A
  := match h with | prod ht _ => ht

theorem Ty.IsTerminal.prod_right {A B : Ty α} (h : IsTerminal (Ty.prod A B)) : IsTerminal B
  := match h with | prod _ ht => ht

theorem Ty.IsTerminal.of_prod {A B : Ty α} : IsTerminal (Ty.prod A B) → IsTerminal A ∧ IsTerminal B
  | prod ht₁ ht₂ => ⟨ht₁, ht₂⟩

@[simp]
theorem Ty.IsTerminal.prod_iff {A B : Ty α} : IsTerminal (Ty.prod A B) ↔ IsTerminal A ∧ IsTerminal B
  := ⟨Ty.IsTerminal.of_prod, λ| ⟨ht₁, ht₂⟩ => prod ht₁ ht₂⟩

theorem Ty.IsTerminal.coprod_terminal {A B : Ty α}
  (h : IsTerminal (Ty.coprod A B)) : IsTerminal A ∨ IsTerminal B
  := match h with
  | coprod_left ht _ => Or.inl ht
  | coprod_right _ ht => Or.inr ht

theorem Ty.IsTerminal.coprod_initial {A B : Ty α}
  (h : IsTerminal (Ty.coprod A B)) : IsInitial A ∨ IsInitial B
  := match h with
  | coprod_left _ hi => Or.inr hi
  | coprod_right hi _ => Or.inl hi

theorem Ty.IsTerminal.of_coprod {A B : Ty α}
  : IsTerminal (Ty.coprod A B) → (IsTerminal A ∧ IsInitial B) ∨ (IsInitial A ∧ IsTerminal B)
  | coprod_left ht hi => Or.inl ⟨ht, hi⟩
  | coprod_right hi ht => Or.inr ⟨hi, ht⟩

theorem Ty.IsInitial.not_terminal {A : Ty α} (h : IsInitial A) : ¬IsTerminal A := by
  intro c
  induction h with
  | prod_left _ I => exact I c.prod_left
  | prod_right _ I => exact I c.prod_right
  | coprod _ _ IA IB =>
    cases c.coprod_terminal with
    | inl c => exact IA c
    | inr c => exact IB c
  | empty => cases c

theorem Ty.IsTerminal.not_initial {A : Ty α} (h : IsTerminal A) : ¬IsInitial A :=
  λc => c.not_terminal h

theorem Ty.IsTerminal.coprod' {A B : Ty α}
  (terminal : IsTerminal A ∨ IsTerminal B) (initial : IsInitial A ∨ IsInitial B)
  : IsTerminal (Ty.coprod A B)
  := by
  cases terminal <;> cases initial
  case inl.inl t i => exact (t.not_initial i).elim
  case inl.inr t i => exact coprod_left t i
  case inr.inl t i => exact coprod_right i t
  case inr.inr t i => exact (t.not_initial i).elim

@[simp]
theorem Ty.IsTerminal.coprod_iff {A B : Ty α}
  : IsTerminal (Ty.coprod A B) ↔ (IsTerminal A ∨ IsTerminal B) ∧ (IsInitial A ∨ IsInitial B)
  := ⟨λh => ⟨h.coprod_terminal, h.coprod_initial⟩, λ⟨t, i⟩ => coprod' t i⟩

@[simp]
theorem Ty.IsTerminal.unit' : IsTerminal (Ty.unit (α := α))
  := unit

@[simp]
theorem Ty.IsTerminal.empty : ¬IsTerminal (Ty.empty (α := α))
  := λh => by cases h

@[simp]
theorem Ty.IsTerminal.base {x : α} : ¬IsTerminal (Ty.base x)
  := λh => by cases h

variable [PartialOrder α] [PartialOrder ε] [Bot ε]

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

theorem Ty.IsInitial.mono {A B : Ty α} (h : Ty.LE A B) (hi : IsInitial A) : IsInitial B
  := by induction h with
  | prod _ _ Il Ir => cases hi with
    | prod_left hl => exact prod_left (Il hl)
    | prod_right hr => exact prod_right (Ir hr)
  | coprod _ _ Il Ir => cases hi with | coprod hl hr => exact coprod (Il hl) (Ir hr)
  | _ => cases hi <;> constructor

theorem Ty.IsInitial.anti {A B : Ty α} (h : Ty.LE A B) (hi : IsInitial B) : IsInitial A
  := by induction h with
  | prod _ _ Il Ir => cases hi with
    | prod_left hl => exact prod_left (Il hl)
    | prod_right hr => exact prod_right (Ir hr)
  | coprod _ _ Il Ir => cases hi with | coprod hl hr => exact coprod (Il hl) (Ir hr)
  | _ => cases hi <;> constructor
