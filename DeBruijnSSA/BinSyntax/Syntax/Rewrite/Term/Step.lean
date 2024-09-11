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
    Rewrite (let2 e r) (let1 e $ (let2 (var 0) (r.wk2)))
  | case_bind (e r s) :
    Rewrite (case e r s) (let1 e $ case (var 0) (r.wk1) (s.wk1))
  | case_eta (a) : Rewrite (case a (inl (var 0)) (inr (var 0))) a
  | let1_let1_case (a b r s) :
    Rewrite
      (let1 a $ let1 b $ case (var 1) r s)
      (let1 a $ case (var 0) (let1 b.wk0 r.swap01) (let1 b.wk0 s.swap01))
  -- | let1_let2_case (a b r s) :
  --   Rewrite
  --     (let1 a $ let2 b $ case (var 2) r s)
  --     (let1 a $ case (var 0) (let2 b.wk0 r.swap02) (let2 b.wk0 s.swap02))
  -- | let1_case_case (a d ll lr rl rr) :
  --   Rewrite
  --     (let1 a $ case d (case (var 1) ll lr) (case (var 1) rl rr))
  --     (let1 a $ case (var 0)
  --       (case d.wk0 ll.swap01 rl.swap01)
  --       (case d.wk0 lr.swap01 rr.swap01))
  -- | case_wk0_wk0 (e r) : Rewrite (case e (wk0 r) (wk0 r)) (let1 e r.wk0)

theorem Rewrite.subst {e e' : Term φ} (h : e.Rewrite e') (σ) : (e.subst σ).Rewrite (e'.subst σ)
  := by induction h with
  | let1_op f e r =>
    simp only [Term.subst, Subst.lift_zero, <-wk1_subst_lift]
    exact let1_op f (e.subst σ) (r.subst (σ.lift))
  | let1_let1 a b r =>
    simp only [Term.subst, <-wk1_subst_lift]
    exact let1_let1 (a.subst σ) (b.subst (σ.lift)) (r.subst (σ.lift))
  | let1_pair a b r =>
    simp only [Term.subst, Subst.lift_succ, wk, Nat.succ_eq_add_one, zero_add,
      Subst.lift_zero, <-Term.wk1_subst_lift, Term.subst_lift]
    exact let1_pair (a.subst σ) (b.subst σ) (r.subst (σ.lift))
  | let1_let2 a b r =>
    simp only [Term.subst, <-wk1_subst_lift, Subst.liftn_two]
    exact let1_let2 (a.subst σ) (b.subst σ.lift.lift) (r.subst σ.lift)
  | let1_inl e r =>
    simp only [Term.subst, <-wk1_subst_lift]
    exact let1_inl (e.subst σ) (r.subst (σ.lift))
  | let1_inr e r =>
    simp only [Term.subst, <-wk1_subst_lift]
    exact let1_inr (e.subst σ) (r.subst (σ.lift))
  | let1_case a l r s =>
    simp only [Term.subst, <-wk1_subst_lift]
    exact let1_case (a.subst σ) (l.subst σ.lift) (r.subst σ.lift) (s.subst σ.lift)
  | let1_abort e r =>
    simp only [Term.subst, <-wk1_subst_lift]
    exact let1_abort (e.subst σ) (r.subst σ.lift)
  | let2_eta a => exact let2_eta (a.subst σ)
  | let2_pair a b r =>
    simp only [Term.subst, <-wk1_subst_lift, Subst.liftn_two, <-wk0_subst]
    exact let2_pair (a.subst σ) (b.subst σ) (r.subst σ.lift.lift)
  | let1_eta a => exact let1_eta (a.subst σ)
  | let2_bind e r =>
    simp only [Term.subst, <-wk1_subst_lift, Subst.liftn_two, <-wk2_subst_lift_lift]
    exact let2_bind (e.subst σ) (r.subst (σ.lift.lift))
  | case_bind e r s =>
    simp only [Term.subst, <-wk1_subst_lift]
    exact case_bind (e.subst σ) (r.subst σ.lift) (s.subst σ.lift)
  | case_eta a => exact case_eta (a.subst σ)
  | let1_let1_case a b r s =>
    simp only [Term.subst, <-wk1_subst_lift, <-wk0_subst, <-swap01_subst_lift_lift]
    exact let1_let1_case (a.subst σ) (b.subst σ.lift)
      (r.subst σ.lift.lift.lift) (s.subst σ.lift.lift.lift)
  -- | let1_let2_case a b r s =>
  --   simp only [
  --     Term.subst, <-wk1_subst_lift, <-wk0_subst, <-swap02_subst_lift_lift_lift, Subst.liftn_two]
  --   exact let1_let2_case (a.subst σ) (b.subst σ.lift)
  --     (r.subst σ.lift.lift.lift.lift) (s.subst σ.lift.lift.lift.lift)
  -- | let1_case_case a d ll lr rl rr =>
  --   simp only [
  --     Term.subst, <-wk1_subst_lift, <-swap01_subst_lift_lift, <-swap01_subst_lift_lift,
  --     <-wk0_subst
  --   ]
  --   exact let1_case_case (a.subst σ) (d.subst σ.lift)
  --     (ll.subst σ.lift.lift.lift) (lr.subst σ.lift.lift.lift)
  --     (rl.subst σ.lift.lift.lift) (rr.subst σ.lift.lift.lift)
  -- | case_wk0_wk0 e r =>
  --   simp only [Term.subst, <-wk1_subst_lift, <-wk0_subst]
  --   exact case_wk0_wk0 (e.subst σ) (r.subst σ)

theorem Rewrite.wk {e e' : Term φ} (h : e.Rewrite e') (ρ) : (e.wk ρ).Rewrite (e'.wk ρ)
  := by simp only [<-Term.subst_fromWk]; exact h.subst _

-- TODO: Cong.Rewrite induces a Setoid on Term... but we should maybe add more stuff?

inductive Reduce : Term φ → Term φ → Prop
  | case_inl (e r s) : Reduce (case (inl e) r s) (let1 e r)
  | case_inr (e r s) : Reduce (case (inr e) r s) (let1 e s)

theorem Reduce.subst {e e' : Term φ} (h : e.Reduce e') (σ) : (e.subst σ).Reduce (e'.subst σ)
  := by induction h with
  | case_inl e r s =>
    simp only [Term.subst, <-wk1_subst_lift]
    exact case_inl (e.subst σ) (r.subst σ.lift) (s.subst σ.lift)
  | case_inr e r s =>
    simp only [Term.subst, <-wk1_subst_lift]
    exact case_inr (e.subst σ) (r.subst σ.lift) (s.subst σ.lift)

theorem Reduce.wk {e e' : Term φ} (h : e.Reduce e') (ρ) : (e.wk ρ).Reduce (e'.wk ρ)
  := by simp only [<-Term.subst_fromWk]; exact h.subst _

-- TODO: Step, FStep, friends...
