import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Order.Lattice

/--
A type which can be interpreted as an effect, which may be _central_, _relevant_, or _affine_

A pure morphism is one which is central, relevant, and affine, though the set of pure morphisms
may be arbitrarily shrunk further.

Note this is essentially just a set equipped with a semilattice-hom to transparency, i.e.
(central, relevant, affine, pure); this might be nicer to state that way...
-/
class EffectSet (ε : Type u) [SemilatticeSup ε] where
  central : ε → Bool
  relevant : ε → Bool
  affine : ε → Bool
  pure (e : ε) : Bool
  -- TODO: naming
  central_of_le : Antitone central
  relevant_of_le : Antitone relevant
  affine_of_le : Antitone affine
  pure_of_le : Antitone pure
  sup_central : ∀ e e', central e → central e' → central (e ⊔ e')
  sup_relevant : ∀ e e', relevant e → relevant e' → relevant (e ⊔ e')
  sup_affine : ∀ e e', affine e → affine e' → affine (e ⊔ e')
  sup_pure : ∀ e e', pure e → pure e' → pure (e ⊔ e')
  central_of_pure : ∀ e, pure e → central e
  relevant_of_pure : ∀ e, pure e → relevant e
  affine_of_pure : ∀ e, pure e → affine e

inductive Impurity where
  | is_pure : Impurity
  | is_impure : Impurity
  deriving Repr, DecidableEq

instance : OfNat Impurity 0 where
  ofNat := Impurity.is_pure

instance : OfNat Impurity 1 where
  ofNat := Impurity.is_impure

instance : LinearOrder Impurity where
  le x y := x = y ∨ x = Impurity.is_pure
  le_refl _ := Or.inl rfl
  le_trans _ _ _ h h' := by cases h <;> cases h' <;> simp [*]
  le_antisymm _ _ h h' := by cases h <;> simp only [*]; cases h' <;> simp [*]
  le_total x y := by cases x <;> cases y <;> simp
  decidableLE x y := decidable_of_iff (x = y ∨ x = Impurity.is_pure) Iff.rfl
  decidableEq := inferInstance

instance : EffectSet Impurity where
  pure := λ | Impurity.is_pure => true | _ => false
  central := λ | Impurity.is_pure => true | _ => false
  relevant := λ | Impurity.is_pure => true | _ => false
  affine := λ | Impurity.is_pure => true | _ => false
  central_of_le e e' h := by cases h <;> simp [*]
  relevant_of_le e e' h := by cases h <;> simp [*]
  affine_of_le e e' h := by cases h <;> simp [*]
  pure_of_le e e' h := by cases h <;> simp [*]
  sup_central e e' := by cases e <;> cases e' <;> simp
  sup_relevant e e' := by cases e <;> cases e' <;> simp
  sup_affine e e' := by cases e <;> cases e' <;> simp
  sup_pure e e' := by cases e <;> cases e' <;> simp
  central_of_pure e h := h
  relevant_of_pure e h := h
  affine_of_pure e h := h

class InstSet (φ : Type u) (α : Type v) (ε : Type w) where
  src : φ → α
  trg : φ → α
  effect : φ → ε

def InstSet.fn {φ α ε} [Φ : InstSet φ α ε] [PartialOrder α] [PartialOrder ε]
  (f : φ) (A B : α) (e : ε) :=
  A ≤ Φ.src f ∧ Φ.trg f ≤ B ∧ Φ.effect f ≤ e
