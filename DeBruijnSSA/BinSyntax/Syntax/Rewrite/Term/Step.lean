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

namespace Term

-- -- TODO: define as Subst.cons or smt...
-- def subst₂ (a b: Term φ) : Subst φ
--   | 0 => a
--   | 1 => b
--   | n + 2 => var n

inductive Rewrite : Term φ → Term φ → Prop
  | let1_op (f e r) :
    Rewrite (let1 (op f e) r) (let1 e $ let1 (op f (var 0)) $ r.wk1)
  | let1_let1 (a b r) :
    Rewrite (let1 (let1 a b) r) (let1 a $ let1 b $ r.wk1)
  | let1_pair (a b r) :
    Rewrite (let1 (pair a b) r)
    (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) $ r.wk1.wk1)
  | let1_let2 (a b r) :
    Rewrite (let1 (let2 a b) r) (let2 a $ let1 b $ r.wk1.wk1)
  | let1_inl (e r) :
    Rewrite (let1 (inl e) r) (let1 e $ let1 (inl (var 0)) $ r.wk1)
  | let1_inr (e r) :
    Rewrite (let1 (inr e) r) (let1 e $ let1 (inr (var 0)) $ r.wk1)
  | let1_case (a l r s) :
    Rewrite (let1 (case a l r) s) (case a (let1 l $ s.wk1) (let1 r $ s.wk1))
  | let1_abort (e r) :
    Rewrite (let1 (abort e) r) (let1 e $ let1 (abort (var 0)) $ r.wk1)
  | let2_eta (a) : Rewrite (let2 a (pair (var 1) (var 0))) a
  | let1_eta (a) : Rewrite (let1 a (var 0)) a
  | let2_bind (e r) :
    Rewrite (let2 e r) (let1 e $ (let2 (var 0) (r.wk (Nat.liftnWk 2 Nat.succ))))
  | case_bind (e r s) :
    Rewrite (case e r s) (let1 e $ case (var 0) (r.wk1) (s.wk1))
  -- TODO: case_let1, case_let2, case_case, case_eta

-- TODO: Cong.Rewrite induces a Setoid on Term

inductive Reduce : Term φ → Term φ → Prop
  | case_inl (e r s) : Reduce (case (inl e) r s) (let1 e r)
  | case_inr (e r s) : Reduce (case (inr e) r s) (let1 e s)

-- TODO: Reduce

-- TODO: Step, FStep, friends...
