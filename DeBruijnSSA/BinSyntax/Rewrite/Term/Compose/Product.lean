import DeBruijnSSA.BinSyntax.Rewrite.Term.Eqv

import Discretion.Utils.Quotient

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

def Eqv.reassoc {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ Γ ⟨(A.prod B).prod C, e⟩)
  : Eqv φ Γ ⟨A.prod (B.prod C), e⟩
  := let2 r
  $ let2 (var (V := (A.prod B, e)) 1 (by simp))
  $ pair (var 1 (by simp)) (pair (var 0 (by simp)) (var 2 (by simp)))

def Eqv.reassoc_inv {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ Γ ⟨A.prod (B.prod C), e⟩)
  : Eqv φ Γ ⟨(A.prod B).prod C, e⟩
  := let2 r
  $ let2 (var (V := (B.prod C, e)) 0 (by simp))
  $ pair (pair (var 3 (by simp)) (var 1 (by simp))) (var 0 (by simp))

theorem Eqv.reassoc_beta {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ Γ ⟨B, e⟩} {c : Eqv φ Γ ⟨C, e⟩}
  : reassoc (pair (pair a b) c) = pair a (pair b c) := by
  rw [reassoc, let2_pair, let1_pair, let1_beta_let2_eta]
  simp only [wk1_let1, wk2_let2, wk2_var1, List.length_cons, Fin.mk_one, List.get_eq_getElem,
    Fin.val_one, List.getElem_cons_succ, List.getElem_cons_zero, wk_pair, wk_var, Set.mem_setOf_eq,
    Ctx.InS.coe_liftn₂, Nat.liftnWk, Nat.one_lt_ofNat, ↓reduceIte, Nat.ofNat_pos, lt_self_iff_false,
    le_refl, tsub_eq_zero_of_le, Ctx.InS.coe_wk2, zero_add, subst_let1, subst_let2,
    subst_lift_var_succ, var0_subst0, Fin.zero_eta, Fin.val_zero, wk_res_eff, wk_eff_pair,
    wk_eff_var, wk0_pair, wk0_var, Nat.reduceAdd, ← Subst.Eqv.lift_lift, subst_pair,
    subst_lift_var_zero, let2_pair, let1_beta_var2, var_succ_subst0, Nat.add_zero, Nat.zero_eq,
    ↓dreduceIte, Nat.reduceSub]
  rw [pair_bind (a := a) (b := b.pair c)]
  apply congrArg
  rw [wk0_pair, let1_pair]
  apply congrArg
  rw [let1_beta_let2_eta, wk0_wk1, wk0_wk1, subst0_wk0]
  rfl

theorem Eqv.reassoc_inv_beta {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ Γ ⟨B, e⟩} {c : Eqv φ Γ ⟨C, e⟩}
  : reassoc_inv (pair a (pair b c)) = pair (pair a b) c := by
  rw [reassoc_inv, let2_pair, wk0_pair, let1_pair, let1_beta_let2_eta]
  simp only [wk1_let2, wk1_var0, List.length_cons, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero,
    List.getElem_cons_zero, wk_pair, wk_var, Set.mem_setOf_eq, Ctx.InS.coe_liftn₂, Nat.liftnWk,
    Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Ctx.InS.coe_wk1, Nat.liftWk_succ, Nat.succ_eq_add_one,
    zero_add, Nat.reduceAdd, Nat.one_lt_ofNat, Nat.ofNat_pos, subst_let2, var0_subst0, wk_res_eff,
    wk_eff_pair, wk_eff_var, subst_pair, subst_liftn₂_var_add_2, var_succ_subst0, wk0_var,
    subst_liftn₂_var_one, ge_iff_le, Prod.mk_le_mk, le_refl, bot_le, and_self,
    subst_liftn₂_var_zero, let2_pair, let1_beta_var1, ↓dreduceIte, Nat.liftWk_zero]
  rw [pair_bind (b := c), pair_bind (a := a), let1_let1, let1_let1, let1_beta_let2_eta]
  simp [wk0_wk1]

theorem Eqv.reassoc_let1 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X, e⟩}
  {r : Eqv φ ((X, ⊥)::Γ) ⟨(A.prod B).prod C, e⟩}
  : reassoc (let1 a r) = let1 a (reassoc r) := by rw [reassoc, let2_let1]; rfl

theorem Eqv.let1_reassoc {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X, e⟩}
  {r : Eqv φ ((X, ⊥)::Γ) ⟨(A.prod B).prod C, e⟩}
  : let1 a (reassoc r) = reassoc (let1 a r) := reassoc_let1.symm

theorem Eqv.reassoc_let2 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.prod Y, e⟩}
  {r : Eqv φ ((Y, ⊥)::(X, ⊥)::Γ) ⟨(A.prod B).prod C, e⟩}
  : reassoc (let2 a r) = let2 a (reassoc r) := by rw [reassoc, let2_let2]; rfl

theorem Eqv.let2_reassoc {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.prod Y, e⟩}
  {r : Eqv φ ((Y, ⊥)::(X, ⊥)::Γ) ⟨(A.prod B).prod C, e⟩}
  : let2 a (reassoc r) = reassoc (let2 a r) := reassoc_let2.symm

theorem Eqv.reassoc_case {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨Ty.coprod X Y, e⟩}
  {l : Eqv φ (⟨X, ⊥⟩::Γ) ⟨(A.prod B).prod C, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨(A.prod B).prod C, e⟩}
  : reassoc (case a l r) = case a (reassoc l) (reassoc r) := by rw [reassoc, let2_case]; rfl

theorem Eqv.case_reassoc {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨Ty.coprod X Y, e⟩}
  {l : Eqv φ (⟨X, ⊥⟩::Γ) ⟨(A.prod B).prod C, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨(A.prod B).prod C, e⟩}
  : case a (reassoc l) (reassoc r) = reassoc (case a l r) := reassoc_case.symm

theorem Eqv.reassoc_inv_let1 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X, e⟩}
  {r : Eqv φ ((X, ⊥)::Γ) ⟨A.prod (B.prod C), e⟩}
  : reassoc_inv (let1 a r) = let1 a (reassoc_inv r) := by rw [reassoc_inv, let2_let1]; rfl

theorem Eqv.let1_reassoc_inv {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X, e⟩}
  {r : Eqv φ ((X, ⊥)::Γ) ⟨A.prod (B.prod C), e⟩}
  : let1 a (reassoc_inv r) = reassoc_inv (let1 a r) := reassoc_inv_let1.symm

theorem Eqv.reassoc_inv_let2 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.prod Y, e⟩}
  {r : Eqv φ ((Y, ⊥)::(X, ⊥)::Γ) ⟨A.prod (B.prod C), e⟩}
  : reassoc_inv (let2 a r) = let2 a (reassoc_inv r) := by rw [reassoc_inv, let2_let2]; rfl

theorem Eqv.let2_reassoc_inv {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.prod Y, e⟩}
  {r : Eqv φ ((Y, ⊥)::(X, ⊥)::Γ) ⟨A.prod (B.prod C), e⟩}
  : let2 a (reassoc_inv r) = reassoc_inv (let2 a r) := reassoc_inv_let2.symm

theorem Eqv.reassoc_inv_case {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨Ty.coprod X Y, e⟩}
  {l : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.prod (B.prod C), e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨A.prod (B.prod C), e⟩}
  : reassoc_inv (case a l r) = case a (reassoc_inv l) (reassoc_inv r)
    := by rw [reassoc_inv, let2_case]; rfl

theorem Eqv.case_reassoc_inv {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨Ty.coprod X Y, e⟩}
  {l : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.prod (B.prod C), e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨A.prod (B.prod C), e⟩}
  : case a (reassoc_inv l) (reassoc_inv r) = reassoc_inv (case a l r) := reassoc_inv_case.symm

theorem Eqv.reassoc_reassoc_inv {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A.prod (B.prod C), e⟩} : reassoc (reassoc_inv a) = a := by
  rw [reassoc_inv, reassoc_let2, reassoc_let2, reassoc_beta]
  apply Eq.trans _ a.let2_eta
  apply congrArg
  rw [pair_bind, let1_pair_var_1_left, let1_beta_var3]
  simp [let2_pair_var_3_left, let1_beta_let2_eta, let2_eta]

theorem Eqv.reassoc_inv_reassoc {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨(A.prod B).prod C, e⟩} : reassoc_inv (reassoc a) = a := by
  rw [reassoc, reassoc_inv_let2, reassoc_inv_let2, reassoc_inv_beta]
  apply Eq.trans _ a.let2_eta
  apply congrArg
  conv => lhs; rhs; rhs; rw [var2_eq_wk0_var1, var1_eq_wk0_var0]
  rw [let2_pair_right, let2_eta]
