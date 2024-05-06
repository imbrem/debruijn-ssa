import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Order.Lattice

/--
A type equipped with a purity predicate
-/
class HasPurity (ε : Type u) [SemilatticeSup ε] where
  isPure : ε → Bool
  sup_isPure : ∀ e e', isPure e → isPure e' → isPure (e ⊔ e')
  isPure_of_le : Antitone isPure

/--
A type equipped with a centrality predicate
-/
class HasCentrality (ε : Type u) [SemilatticeSup ε] where
  isCentral : ε → Bool
  sup_isCentral : ∀ e e', isCentral e → isCentral e' → isCentral (e ⊔ e')
  isCentral_of_le : Antitone isCentral

/--
A type equipped with a relevance predicate
-/
class HasRelevance (ε : Type u) [SemilatticeSup ε] where
  isRelevant : ε → Bool
  sup_isRelevant : ∀ e e', isRelevant e → isRelevant e' → isRelevant (e ⊔ e')
  isRelevant_of_le : Antitone isRelevant

/--
A type equippd with an affinity predicate
-/
class HasAffinity (ε : Type u) [SemilatticeSup ε] where
  isAffine : ε → Bool
  sup_isAffine : ∀ e e', isAffine e → isAffine e' → isAffine (e ⊔ e')
  isAffine_of_le : Antitone isAffine

/--
A type which can be interpreted as an effect, which may be _central_, _relevant_, or _affine_

A pure morphism is one which is central, relevant, and affine, though the set of pure morphisms
may be arbitrarily shrunk further.

Note this is essentially just a set equipped with a semilattice-hom to transparency, i.e.
(central, relevant, affine, pure); this might be nicer to state that way...
-/
class EffectSet (ε : Type u) [SemilatticeSup ε]
  extends HasPurity ε, HasCentrality ε, HasRelevance ε, HasAffinity ε where
  isCentral_of_isPure : ∀ e, isPure e ≤ isCentral e
  isRelevant_of_isPure : ∀ e, isPure e ≤ isRelevant e
  isAffine_of_isPure : ∀ e, isPure e ≤ isAffine e

inductive Impurity where
  | none : Impurity
  | impure : Impurity
  deriving Repr, DecidableEq

instance : OfNat Impurity 0 where
  ofNat := Impurity.none

instance : OfNat Impurity 1 where
  ofNat := Impurity.impure

instance : LinearOrder Impurity where
  le x y := x = y ∨ x = Impurity.none
  le_refl _ := Or.inl rfl
  le_trans _ _ _ h h' := by cases h <;> cases h' <;> simp [*]
  le_antisymm _ _ h h' := by cases h <;> simp only [*]; cases h' <;> simp [*]
  le_total x y := by cases x <;> cases y <;> simp
  decidableLE x y := decidable_of_iff (x = y ∨ x = Impurity.none) Iff.rfl
  decidableEq := inferInstance

instance : EffectSet Impurity where
  isPure := λ | Impurity.none => true | _ => false
  isCentral := λ | Impurity.none => true | _ => false
  isRelevant := λ | Impurity.none => true | _ => false
  isAffine := λ | Impurity.none => true | _ => false
  isCentral_of_le e e' h := by cases h <;> simp [*]
  isRelevant_of_le e e' h := by cases h <;> simp [*]
  isAffine_of_le e e' h := by cases h <;> simp [*]
  isPure_of_le e e' h := by cases h <;> simp [*]
  sup_isCentral e e' := by cases e <;> cases e' <;> simp
  sup_isRelevant e e' := by cases e <;> cases e' <;> simp
  sup_isAffine e e' := by cases e <;> cases e' <;> simp
  sup_isPure e e' := by cases e <;> cases e' <;> simp
  isCentral_of_isPure e h := h
  isRelevant_of_isPure e h := h
  isAffine_of_isPure e h := h

class InstSet (φ : Type u) (α : Type v) (ε : Type w) where
  src : φ → α
  trg : φ → α
  effect : φ → ε

def InstSet.fn {φ α ε} [Φ : InstSet φ α ε] [PartialOrder α] [PartialOrder ε]
  (f : φ) (A B : α) (e : ε) :=
  A ≤ Φ.src f ∧ Φ.trg f ≤ B ∧ Φ.effect f ≤ e
