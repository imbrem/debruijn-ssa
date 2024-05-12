import Mathlib.Order.Monotone.Basic
import Mathlib.Order.BoundedOrder
import Mathlib.Data.Bool.Basic
import Mathlib.Order.Lattice

/--
A type equipped with a purity predicate
-/
class HasPurity (ε : Type u) [SemilatticeSup ε] [Bot ε] where
  isPure : ε → Bool
  sup_isPure : ∀ e e', isPure e → isPure e' → isPure (e ⊔ e')
  isPure_of_le : Antitone isPure
  bot_isPure : isPure ⊥

-- If there exists something impure, then ⊤ is impure

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
A type equipped with an affinity predicate
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
class EffectSet (ε : Type u) [SemilatticeSup ε] [Bot ε]
  extends HasPurity ε, HasCentrality ε, HasRelevance ε, HasAffinity ε where
  isCentral_of_isPure : ∀ e, isPure e ≤ isCentral e
  isRelevant_of_isPure : ∀ e, isPure e ≤ isRelevant e
  isAffine_of_isPure : ∀ e, isPure e ≤ isAffine e

-- TODO: ⊥ is central, relevant, affine

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

instance : Bot Impurity where
  bot := Impurity.none

instance : Top Impurity where
  top := Impurity.impure

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
  bot_isPure := rfl
  isCentral_of_isPure e h := h
  isRelevant_of_isPure e h := h
  isAffine_of_isPure e h := h

class InstSet (φ : Type u) (α : Type v) (ε : Type w) where
  src : φ → α
  trg : φ → α
  effect : φ → ε

structure InstSet.Fn {φ α ε} [Φ : InstSet φ α ε] [PartialOrder α] [PartialOrder ε]
  (f : φ) (A B : α) (e : ε) : Prop where
  src : A ≤ Φ.src f
  trg : Φ.trg f ≤ B
  effect : Φ.effect f ≤ e

theorem InstSet.fn_iff {φ α ε} [Φ : InstSet φ α ε] [PartialOrder α] [PartialOrder ε]
  {f : φ} {A B : α} {e : ε} : Φ.Fn f A B e ↔ A ≤ Φ.src f ∧ Φ.trg f ≤ B ∧ Φ.effect f ≤ e := ⟨
  λ h => ⟨h.src, h.trg, h.effect⟩,
  λ ⟨hsrc, htrg, heff⟩ => ⟨hsrc, htrg, heff⟩⟩

theorem InstSet.Fn.wk_src {φ α ε} [Φ : InstSet φ α ε] [PartialOrder α] [PartialOrder ε]
  {f : φ} {A A' B : α} {e : ε} (h : A' ≤ A) (hf : Φ.Fn f A B e) : Φ.Fn f A' B e where
  src := le_trans h hf.src
  trg := hf.trg
  effect := hf.effect

theorem InstSet.Fn.wk_trg {φ α ε} [Φ : InstSet φ α ε] [PartialOrder α] [PartialOrder ε]
  {f : φ} {A B B' : α} {e : ε} (h : B ≤ B') (hf : Φ.Fn f A B e) : Φ.Fn f A B' e where
  src := hf.src
  trg := le_trans hf.trg h
  effect := hf.effect

theorem InstSet.Fn.wk_eff {φ α ε} [Φ : InstSet φ α ε] [PartialOrder α] [PartialOrder ε]
  {f : φ} {A B : α} {e e' : ε} (h : e ≤ e') (hf : Φ.Fn f A B e) : Φ.Fn f A B e' where
  src := hf.src
  trg := hf.trg
  effect := le_trans hf.effect h
