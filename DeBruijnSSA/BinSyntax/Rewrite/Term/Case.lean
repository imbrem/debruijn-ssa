import DeBruijnSSA.BinSyntax.Rewrite.Term.Eqv

import Discretion.Utils.Quotient

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

-- Eta rules:

theorem Eqv.case_eta {A B : Ty α}
  {a : Eqv φ Γ ⟨A.coprod B, e⟩}
  : case a (var 0 Ctx.Var.bhead).inl (var 0 Ctx.Var.bhead).inr = a := by
  induction a using Quotient.inductionOn
  apply Eqv.sound; apply InS.case_eta

-- Reduction rules

theorem Eqv.case_inl {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case (inl a) l r = (let1 a l) := by
  induction a using Quotient.inductionOn
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.case_inl

theorem Eqv.case_inr {Γ : Ctx α ε} {a : Eqv φ Γ ⟨B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case (inr a) l r = (let1 a r) := by
  induction a using Quotient.inductionOn
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.case_inr

-- Binding rules

theorem Eqv.case_bind {Γ : Ctx α ε} {a : Eqv φ Γ ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case a l r = (let1 a $ case (var 0 (by simp)) (l.wk1) (r.wk1)) := by
  induction a using Quotient.inductionOn
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.case_bind

-- Derived binding rules

theorem Eqv.case_let1
  {x : Eqv φ Γ ⟨X, e⟩} {d : Eqv φ (⟨X, ⊥⟩::Γ) ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case (let1 x d) l r = let1 x (case d l.wk1 r.wk1) := by
  rw [case_bind, let1_let1]
  apply Eq.symm
  rw [case_bind]
  simp [wk1_wk2]

theorem Eqv.case_let2
  {x : Eqv φ Γ ⟨X.prod Y, e⟩} {d : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case (let2 x d) l r = let2 x (case d l.wk1.wk1 r.wk1.wk1) := by
  rw [case_bind, let1_let2]
  apply Eq.symm
  rw [case_bind]
  simp [wk1_wk2]

theorem Eqv.case_case
  {dd : Eqv φ Γ ⟨X.coprod Y, e⟩}
  {dl : Eqv φ (⟨X, ⊥⟩::Γ) ⟨Ty.coprod A B, e⟩}
  {dr : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case (case dd dl dr) l r = case dd (case dl l.wk1 r.wk1) (case dr l.wk1 r.wk1) := by
  rw [case_bind, let1_case]
  congr <;> {
    apply Eq.symm
    rw [case_bind]
    simp [wk1_wk2]
  }

-- Beta helpers

theorem Eqv.let1_beta_inl_var0 {b : Eqv φ (⟨A.coprod B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : let1 (inl (var 0 Ctx.Var.bhead)) b = b.subst (inl (var 0 Ctx.Var.shead)).subst0
  := by rw [let1_beta']; rfl

theorem Eqv.let1_beta_inr_var0 {A B : Ty α} {b : Eqv φ (⟨A.coprod B, ⊥⟩::⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : let1 (inr (var 0 Ctx.Var.bhead)) b = b.subst (inr (var 0 Ctx.Var.shead)).subst0
  := by rw [let1_beta']; rfl

-- Derived distributivity rules

theorem Eqv.case_wk0_wk0 {A B : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A.coprod B, e⟩}
  {r : Eqv φ Γ ⟨C, e⟩}
  : case a r.wk0 r.wk0 = let1 a r.wk0 := calc
  _ = (case a
        (let1 (A := A.coprod B) (var 0 Ctx.Var.bhead).inl r.wk0.wk1)
        (let1 (A := A.coprod B) (var 0 Ctx.Var.bhead).inr r.wk0.wk1))
        := by simp [let1_beta_inl_var0, let1_beta_inr_var0, wk0_wk1]
  _ = let1 (case a (var 0 Ctx.Var.bhead).inl (var 0 Ctx.Var.bhead).inr) r.wk0
        := by simp [let1_case]
  _ = _ := by simp [case_eta]

-- TODO: probably derivable with hacks: bind a case, then stick a let1 in the bound case

-- theorem Eqv.let1_case_var1 {Γ : Ctx α ε}
--   {b : Eqv φ (⟨Ty.coprod A B, ⊥⟩::Γ) ⟨X, e⟩}
--   {l : Eqv φ (⟨A, ⊥⟩::⟨X, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨C, e⟩}
--   {r : Eqv φ (⟨B, ⊥⟩::⟨X, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨C, e⟩}
--   : (let1 b $ case (var 1 Ctx.Var.bhead.step) l r)
--     = case (var 0 Ctx.Var.bhead) (let1 b.wk0 l.swap01) (let1 b.wk0 r.swap01) := calc
--   _ = sorry := sorry
--   _ = _ := sorry

-- theorem Eqv.let1_let1_case {Γ : Ctx α ε}
--   {a : Eqv φ Γ ⟨Ty.coprod A B, e⟩}
--   {b : Eqv φ (⟨Ty.coprod A B, ⊥⟩::Γ) ⟨X, e⟩}
--   {l : Eqv φ (⟨A, ⊥⟩::⟨X, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨C, e⟩}
--   {r : Eqv φ (⟨B, ⊥⟩::⟨X, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨C, e⟩}
--   : (let1 a $ let1 b $ case (var 1 Ctx.Var.bhead.step) l r)
--   = (let1 a $ case (var 0 Ctx.Var.bhead) (let1 b.wk0 l.swap01) (let1 b.wk0 r.swap01)) := by
--   rw [let1_case_var1]

-- TODO: probably derivable with hacks; see above

-- theorem Eqv.let1_let2_case {Γ : Ctx α ε}
--   {a : Eqv φ Γ ⟨Ty.coprod A B, e⟩}
--   {b : Eqv φ (⟨Ty.coprod A B, ⊥⟩::Γ) ⟨X.prod Y, e⟩}
--   {l : Eqv φ (⟨A, ⊥⟩::⟨Y, ⊥⟩::⟨X, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨C, e⟩}
--   {r : Eqv φ (⟨B, ⊥⟩::⟨Y, ⊥⟩::⟨X, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨C, e⟩}
--   : (let1 a $ let2 b $ case (var 2 Ctx.Var.bhead.step.step) l r)
--   = (let1 a $ case (var 0 Ctx.Var.bhead) (let2 b.wk0 $ l.swap02) (let2 b.wk0 $ r.swap02)) := by
--   induction a using Quotient.inductionOn
--   induction b using Quotient.inductionOn
--   induction l using Quotient.inductionOn
--   induction r using Quotient.inductionOn
--   apply Eqv.sound; apply InS.let1_let2_case

-- theorem Eqv.let1_case_case {Γ : Ctx α ε}
--   {a : Eqv φ Γ ⟨Ty.coprod A B, e⟩}
--   {d : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) ⟨Ty.coprod X Y, e⟩}
--   {ll : Eqv φ (⟨A, ⊥⟩::⟨X, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨X, e⟩}
--   {lr : Eqv φ (⟨B, ⊥⟩::⟨X, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨X, e⟩}
--   {rl : Eqv φ (⟨A, ⊥⟩::⟨Y, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨X, e⟩}
--   {rr : Eqv φ (⟨B, ⊥⟩::⟨Y, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨X, e⟩}
--   : (let1 a $ case d
--       (case (var 1 Ctx.Var.bhead.step) ll lr)
--       (case (var 1 Ctx.Var.bhead.step) rl rr))
--   = (let1 a $ case (var 0 Ctx.Var.bhead)
--     (case d.wk0 ll.swap01 rl.swap01)
--     (case d.wk0 lr.swap01 rr.swap01)) := by
--   induction a using Quotient.inductionOn
--   induction d using Quotient.inductionOn
--   induction ll using Quotient.inductionOn
--   induction lr using Quotient.inductionOn
--   induction rl using Quotient.inductionOn
--   induction rr using Quotient.inductionOn
--   apply Eqv.sound; apply InS.let1_case_case

theorem Eqv.let1_case_wk0_wk_eff {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X, ⊥⟩} {b : Eqv φ Γ ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨C, e⟩}
  : let1 (a.wk_eff bot_le) (case b.wk0 l r)
    = case b (let1 (a.wk0.wk_eff bot_le) l.swap01) (let1 (a.wk0.wk_eff bot_le) r.swap01) := by
  simp [let1_beta]
  induction a using Quotient.inductionOn
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  congr 1 <;> {
    apply Eqv.eq_of_term_eq
    simp only [Set.mem_setOf_eq, InS.coe_subst, Subst.InS.coe_lift, InS.coe_subst0, InS.coe_wk,
      Ctx.InS.coe_wk0, ← Term.subst_fromWk, Ctx.InS.coe_swap01, Term.subst_subst]
    congr
    funext k; cases k using Nat.cases2 with
    | one => simp [Term.Subst.comp, Term.subst_fromWk]
    | _ => rfl
  }

theorem Eqv.Pure.let1_case_wk0 {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X, e⟩} {b : Eqv φ Γ ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨C, e⟩}
  : a.Pure → let1 a (case b.wk0 l r) = case b (let1 a.wk0 l.swap01) (let1 a.wk0 r.swap01)
  | ⟨a, ha⟩ => by cases ha; rw [let1_case_wk0_wk_eff]; simp [wk0_wk_eff]

theorem Eqv.Pure.case_let1_wk0_pure {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨Ty.coprod A B, e⟩} {b : Eqv φ Γ ⟨X, e⟩}
  {l : Eqv φ (⟨X, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨X, ⊥⟩::⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  (hb : b.Pure) : case a (let1 b.wk0 l) (let1 b.wk0 r) = let1 b (case a.wk0 l.swap01 r.swap01)
  := by simp [hb.let1_case_wk0]

theorem Eqv.let1_case_wk0_pure {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X, ⊥⟩} {b : Eqv φ Γ ⟨Ty.coprod A B, ⊥⟩}
  {l : Eqv φ (⟨A, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨C, ⊥⟩} {r : Eqv φ (⟨B, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨C, ⊥⟩}
  : let1 a (case b.wk0 l r) = case b (let1 a.wk0 l.swap01) (let1 a.wk0 r.swap01)
  := Eqv.Pure.let1_case_wk0 (by simp)

theorem Eqv.case_let1_wk0_pure {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨Ty.coprod A B, ⊥⟩} {b : Eqv φ Γ ⟨X, ⊥⟩}
  {l : Eqv φ (⟨X, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, ⊥⟩} {r : Eqv φ (⟨X, ⊥⟩::⟨B, ⊥⟩::Γ) ⟨C, ⊥⟩}
  : case a (let1 b.wk0 l) (let1 b.wk0 r) = let1 b (case a.wk0 l.swap01 r.swap01)
  := by simp [let1_case_wk0_pure]

-- Should *definitely* be derivable from let1 lore; convenient file break opportunity too

-- theorem Eqv.case_op_op {Γ : Ctx α ε}
--   {a : Eqv φ Γ ⟨Ty.coprod A B, e⟩}
--   {f} {hf : Φ.EFn f C D e}
--   {r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩}
--   {s : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
--   : case a (op f hf r) (op f hf s) = op f hf (case a r s) := by
--   induction a using Quotient.inductionOn
--   induction r using Quotient.inductionOn
--   induction s using Quotient.inductionOn
--   apply Eqv.sound; apply InS.case_op_op

-- TODO: derive these...

theorem Eqv.let1_inl {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, e⟩} {r : Eqv φ (⟨Ty.coprod A B, ⊥⟩::Γ) ⟨C, e⟩}
  : let1 (inl a) r = (let1 a $ let1 (inl (var 0 (by simp))) $ r.wk1) := by
  rw [<-case_eta (a := inl a), let1_case, case_inl]

theorem Eqv.let1_inr {Γ : Ctx α ε} {a : Eqv φ Γ ⟨B, e⟩} {r : Eqv φ (⟨Ty.coprod A B, ⊥⟩::Γ) ⟨C, e⟩}
  : let1 (inr a) r = (let1 a $ let1 (inr (var 0 (by simp))) $ r.wk1) := by
  rw [<-case_eta (a := inr a), let1_case, case_inr]

theorem Eqv.inl_bind {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, e⟩}
  : a.inl (B := B) = let1 a (inl (var 0 (by simp))) := calc
  _ = let1 a.inl (var 0 Ctx.Var.bhead) := by rw [let1_eta]
  _ = let1 a (let1 (inl (var 0 Ctx.Var.bhead)) (var 0 Ctx.Var.bhead)) := by rw [let1_inl, wk1_var0]
  _ = let1 a (let1 (wk_eff bot_le (inl (var 0 Ctx.Var.shead))) (var 0 Ctx.Var.bhead)) := by rfl
  _ = _ := by rw [let1_beta]; rfl

theorem Eqv.inr_bind {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, e⟩}
  : a.inr (A := B) = let1 a (inr (var 0 (by simp))) := calc
  _ = let1 a.inr (var 0 Ctx.Var.bhead) := by rw [let1_eta]
  _ = let1 a (let1 (inr (var 0 Ctx.Var.bhead)) (var 0 Ctx.Var.bhead)) := by rw [let1_inr, wk1_var0]
  _ = let1 a (let1 (wk_eff bot_le (inr (var 0 Ctx.Var.shead))) (var 0 Ctx.Var.bhead)) := by rfl
  _ = _ := by rw [let1_beta]; rfl

theorem Eqv.inl_let1 {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ ((A, ⊥)::Γ) ⟨B, e⟩}
  : (let1 a b).inl = let1 a (b.inl (B := C)) := by
  rw [inl_bind, let1_let1, wk1_inl, wk1_var0, <-inl_bind]

theorem Eqv.inr_let1 {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ ((A, ⊥)::Γ) ⟨B, e⟩}
  : (let1 a b).inr = let1 a (b.inr (A := C)) := by
  rw [inr_bind, let1_let1, wk1_inr, wk1_var0, <-inr_bind]

theorem Eqv.inl_let2 {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A.prod B, e⟩} {b : Eqv φ ((B, ⊥)::(A, ⊥)::Γ) ⟨C, e⟩}
  : (let2 a b).inl = let2 a (b.inl (B := D)) := by
  rw [inl_bind, let1_let2, wk1_inl, wk1_inl, wk1_var0, wk1_var0, <-inl_bind]

theorem Eqv.inr_let2 {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A.prod B, e⟩} {b : Eqv φ ((B, ⊥)::(A, ⊥)::Γ) ⟨C, e⟩}
  : (let2 a b).inr = let2 a (b.inr (A := D)) := by
  rw [inr_bind, let1_let2, wk1_inr, wk1_inr, wk1_var0, wk1_var0, <-inr_bind]

theorem Eqv.case_inl_inl {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A.coprod B, e⟩}
  {r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  {s : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case a (inl (B := D) r) (inl s) = inl (case a r s) := by
  conv => rhs; rw [inl_bind]
  rw [let1_case]
  simp [<-inl_let1, let1_eta]

theorem Eqv.case_inr_inr {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A.coprod B, e⟩}
  {r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨D, e⟩}
  {s : Eqv φ (⟨B, ⊥⟩::Γ) ⟨D, e⟩}
  : case a (inr (A := C) r) (inr s) = inr (case a r s) := by
  conv => rhs; rw [inr_bind]
  rw [let1_case]
  simp [<-inr_let1, let1_eta]

-- theorem Eqv.case_abort_abort {Γ : Ctx α ε}
--   {a : Eqv φ Γ ⟨A.coprod B, e⟩}
--   {r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨Ty.empty, e⟩}
--   {s : Eqv φ (⟨B, ⊥⟩::Γ) ⟨Ty.empty, e⟩}
--   : case a (abort r A) (abort s A) = abort (case a r s) A := by
--   induction a using Quotient.inductionOn
--   induction r using Quotient.inductionOn
--   induction s using Quotient.inductionOn
--   apply Eqv.sound; apply InS.case_abort_abort

-- theorem Eqv.case_pair_pair {Γ : Ctx α ε}
--   {d : Eqv φ Γ ⟨A.coprod B, e⟩}
--   {al : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩}
--   {bl : Eqv φ (⟨A, ⊥⟩::Γ) ⟨D, e⟩}
--   {ar : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
--   {br : Eqv φ (⟨B, ⊥⟩::Γ) ⟨D, e⟩}
--   : case d (pair al bl) (pair ar br)
--   = (let1 d $ pair
--       (case (var 0 Ctx.Var.bhead) al.wk1 ar.wk1)
--       (case (var 0 Ctx.Var.bhead) bl.wk1 br.wk1)) := by
--   induction d using Quotient.inductionOn
--   induction al using Quotient.inductionOn
--   induction bl using Quotient.inductionOn
--   induction ar using Quotient.inductionOn
--   induction br using Quotient.inductionOn
--   apply Eqv.sound; apply InS.case_pair_pair
