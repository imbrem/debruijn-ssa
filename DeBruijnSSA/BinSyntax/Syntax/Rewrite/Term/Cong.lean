import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.CategoryTheory.PathCategory
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Discretion.Correspondence.Definitions

import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Effect.Subst
import DeBruijnSSA.BinSyntax.Syntax.Fv

namespace BinSyntax

variable {φ : Type u} {ε : Type v} [Φ: EffectSet φ ε] [SemilatticeSup ε] [OrderBot ε]

-- -- TODO: define as Subst.cons or smt...
-- def Term.subst₂ (a b: Term φ) : Subst φ
--   | 0 => a
--   | 1 => b
--   | n + 2 => Term.var n

namespace Term

inductive Cong (P : Term φ → Term φ → Sort _) : Term φ → Term φ → Prop
  | op (f) : Cong P e e' → Cong P (op f e) (op f e')
  | let1 (e) : Cong P r r' → Cong P (let1 e r) (let1 e r')
  | pair_left : Cong P l l' → (r : Term φ) → Cong P (pair l r) (pair l' r)
  | pair_right (l) : Cong P r r' → Cong P (pair l r) (pair l r')
  | let2 (e) : Cong P r r' → Cong P (let2 e r) (let2 e r')
  | inl : Cong P l l' → Cong P (inl l) (inl l')
  | inr : Cong P r r' → Cong P (inr r) (inr r')
  | case_disc : Cong P e e' → (r s : Term φ) → Cong P (case e r s) (case e' r s)
  | case_left (e) : Cong P r r' → (s : Term φ)
    → Cong P (case e r s) (case e r' s)
  | case_right (e r) : Cong P s s' → Cong P (case e r s) (case e r s')
  | abort : Cong P e e' → Cong P (abort e) (abort e')
  | rel : P r r' → Cong P r r'

theorem Cong.map {P P' : Term φ → Term φ → Sort _}
  (f : ∀r r', P r r' → P' r r') {r r'} (d : Cong P r r') : Cong P' r r'
  := by induction d with
  | rel p => exact Cong.rel (f _ _ p)
  | _ => constructor; assumption

end Term
