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
  | let2_pair (a b r) : Rewrite (let2 (pair a b) r) (let1 a $ let1 b.wk0 $ r)
  | let1_eta (a) : Rewrite (let1 a (var 0)) a
  | let2_bind (e r) :
    Rewrite (let2 e r) (let1 e $ (let2 (var 0) (r.wk (Nat.liftnWk 2 Nat.succ))))
  | case_bind (e r s) :
    Rewrite (case e r s) (let1 e $ case (var 0) (r.wk1) (s.wk1))
  | case_eta (a) : Rewrite (case a (inl (var 0)) (inr (var 0))) a
  | let1_let1_case (a b r s) :
    Rewrite
      (let1 a $ let1 b $ case (var 1) r s)
      (let1 a $ case (var 0) (let1 b.wk0 r.swap01) (let1 b.wk0 s.swap01))
  | let1_let2_case (a b r s) :
    Rewrite
      (let1 a $ let2 b $ case (var 2) r s)
      (let1 a $ case (var 0) (let2 b.wk0 r.swap02) (let2 b.wk0 s.swap02))
  | let1_case_case (a d ll lr rl rr) :
    Rewrite
      (let1 a $ case d (case (var 1) ll lr) (case (var 1) rl rr))
      (let1 a $ case (var 0)
        (case d.wk0 ll.swap01 rl.swap01)
        (case d.wk0 lr.swap01 rr.swap01))
  | case_op_op (e f r s) : Rewrite (case e (op f r) (op f s)) (op f (case e r s))
  | case_inl_inl (e r s) : Rewrite (case e (inl r) (inl s)) (inl (case e r s))
  | case_inr_inr (e r s) : Rewrite (case e (inr r) (inr s)) (inr (case e r s))
  | case_abort_abort (e r s) : Rewrite (case e (abort r) (abort s)) (abort (case e r s))
  | case_pair_pair (e al bl ar br) :
    Rewrite
      (case e (pair al bl) (pair ar br))
      (let1 e $ pair (case (var 0) al.wk1 ar.wk1) (case (var 0) bl.wk1 br.wk1))
  | case_wk0_wk0 (e r) : Rewrite (case e (wk0 r) (wk0 r)) (let1 e r.wk0)

theorem Rewrite.wk {e e' : Term φ} (h : e.Rewrite e') (ρ) : (e.wk ρ).Rewrite (e'.wk ρ)
  := sorry

theorem Rewrite.subst {e e' : Term φ} (h : e.Rewrite e') (σ) : (e.subst σ).Rewrite (e'.subst σ)
  := sorry

-- TODO: Cong.Rewrite induces a Setoid on Term... but we should maybe add more stuff?

inductive Reduce : Term φ → Term φ → Prop
  | case_inl (e r s) : Reduce (case (inl e) r s) (let1 e r)
  | case_inr (e r s) : Reduce (case (inr e) r s) (let1 e s)

theorem Reduce.wk {e e' : Term φ} (h : e.Reduce e') (ρ) : (e.wk ρ).Reduce (e'.wk ρ)
  := sorry

theorem Reduce.subst {e e' : Term φ} (h : e.Reduce e') (σ) : (e.subst σ).Reduce (e'.subst σ)
  := sorry

-- TODO: Step, FStep, friends...
