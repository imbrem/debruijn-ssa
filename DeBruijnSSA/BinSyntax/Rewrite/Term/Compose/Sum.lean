import DeBruijnSSA.BinSyntax.Rewrite.Term.Eqv
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Seq
import DeBruijnSSA.BinSyntax.Typing.Term.Compose

import Discretion.Utils.Quotient


namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

def Eqv.swap_sum {A B : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ Γ ⟨A.coprod B, e⟩)
  : Eqv φ Γ ⟨B.coprod A, e⟩
  := case r (var 0 Ctx.Var.bhead).inr (var 0 Ctx.Var.bhead).inl

theorem Eqv.swap_sum_swap_sum {A B : Ty α} {Γ : Ctx α ε}
  {r : Eqv φ Γ ⟨A.coprod B, e⟩}
  : swap_sum (swap_sum r) = r := by
  simp [swap_sum, case_inl, case_inr, case_eta, case_case, let1_beta_var0]

theorem Eqv.let1_swap_sum {A B : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.coprod B, e⟩}
  : let1 a (swap_sum r) = swap_sum (let1 a r) := sorry

theorem Eqv.swap_sum_let1 {A B : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A, e⟩}
  {r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B.coprod A, e⟩}
  : swap_sum (let1 a r) = let1 a (swap_sum r) := let1_swap_sum.symm

theorem Eqv.let2_swap_sum {A B : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.prod Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨A.coprod B, e⟩}
  : let2 a (swap_sum r) = swap_sum (let2 a r) := sorry

theorem Eqv.swap_sum_let2 {A B : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.prod Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨A.coprod B, e⟩}
  : swap_sum (let2 a r) = let2 a (swap_sum r) := let2_swap_sum.symm

theorem Eqv.case_swap_sum {A B : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.coprod Y, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.coprod B, e⟩}
  {s : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨A.coprod B, e⟩}
  : case a (swap_sum r) (swap_sum s) = swap_sum (case a r s) := sorry

theorem Eqv.swap_sum_case {A B : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.coprod Y, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.coprod B, e⟩}
  {s : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨A.coprod B, e⟩}
  : swap_sum (case a r s) = case a (swap_sum r) (swap_sum s) := case_swap_sum.symm

theorem Eqv.wk_swap_sum {A B : Ty α} {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ}
  {r : Eqv φ Δ ⟨A.coprod B, e⟩}
  : wk ρ (swap_sum r) = swap_sum (wk ρ r) := sorry

theorem Eqv.swap_sum_wk {A B : Ty α} {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ}
  {r : Eqv φ Δ ⟨A.coprod B, e⟩}
  : swap_sum (wk ρ r) = wk ρ (swap_sum r) := wk_swap_sum.symm

theorem Eqv.wk0_swap_sum {A B : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ Γ ⟨A.coprod B, e⟩)
  : (swap_sum r).wk0 (head := head) = swap_sum r.wk0 := wk_swap_sum

theorem Eqv.swap_sum_wk0 {A B : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ Γ ⟨A.coprod B, e⟩)
  : swap_sum r.wk0 = (swap_sum r).wk0 (head := head) := swap_sum_wk

theorem Eqv.wk1_swap_sum {A B : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (head::Γ) ⟨A.coprod B, e⟩)
  : (swap_sum r).wk1 (inserted := inserted) = swap_sum r.wk1 := wk_swap_sum

theorem Eqv.swap_sum_wk1 {A B : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (head::Γ) ⟨A.coprod B, e⟩)
  : swap_sum r.wk1 = (swap_sum r).wk1 (inserted := inserted) := swap_sum_wk

theorem Eqv.wk2_swap_sum {A B : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (left::right::Γ) ⟨A.coprod B, e⟩)
  : (swap_sum r).wk2 (inserted := inserted) = swap_sum r.wk2 := wk_swap_sum

theorem Eqv.swap_sum_wk2 {A B : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (left::right::Γ) ⟨A.coprod B, e⟩)
  : swap_sum r.wk2 = (swap_sum r).wk2 (inserted := inserted) := swap_sum_wk

theorem Eqv.seq_swap_sum {X Y A B : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ (⟨X, ⊥⟩::Γ) ⟨Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨A.coprod B, e⟩}
  : a ;;' (swap_sum r) = swap_sum (a ;;' r) := by rw [seq, wk1_swap_sum, let1_swap_sum]; rfl

theorem Eqv.swap_sum_seq {X Y A B : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ (⟨X, ⊥⟩::Γ) ⟨Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨A.coprod B, e⟩}
  : swap_sum (a ;;' r) = a ;;' (swap_sum r) := seq_swap_sum.symm

def Eqv.reassoc_sum {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ Γ ⟨(A.coprod B).coprod C, e⟩)
  : Eqv φ Γ ⟨A.coprod (B.coprod C), e⟩
  := case r
    (case (var 0 Ctx.Var.bhead) (var 0 Ctx.Var.bhead).inl (var 0 Ctx.Var.bhead).inl.inr)
    (var 0 Ctx.Var.bhead).inr.inr

def Eqv.reassoc_inv_sum {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ Γ ⟨A.coprod (B.coprod C), e⟩)
  : Eqv φ Γ ⟨(A.coprod B).coprod C, e⟩
  := case r
    (var 0 Ctx.Var.bhead).inl.inl
    (case (var 0 Ctx.Var.bhead) (var 0 Ctx.Var.bhead).inr.inl (var 0 Ctx.Var.bhead).inr)

theorem Eqv.let1_beta_inl_var0 {Γ : Ctx α ε} {b : Eqv φ (⟨A.coprod B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : let1 (var 0 (by simp)).inl b = b.subst (var 0 (by simp)).inl.subst0
  := by rw [<-wk_eff_var, <-wk_eff_inl, let1_beta]

theorem Eqv.let1_beta_inr_var0 {A : Ty α} {Γ : Ctx α ε}
  {b : Eqv φ (⟨A.coprod B, ⊥⟩::⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : let1 (var 0 (by simp)).inr b = b.subst (var 0 (by simp)).inr.subst0
  := by rw [<-wk_eff_var, <-wk_eff_inr, let1_beta]

theorem Eqv.reassoc_reassoc_inv_sum {A B C : Ty α} {Γ : Ctx α ε}
  {r : Eqv φ Γ ⟨A.coprod (B.coprod C), e⟩}
  : reassoc_sum (reassoc_inv_sum r) = r := by
  rw [reassoc_inv_sum, reassoc_sum]
  simp [
    case_case, case_inl, case_inr, let1_beta_inl_var0, let1_beta_inr_var0, let1_beta_var0,
    case_inr_inr, case_eta
  ]

theorem Eqv.reassoc_inv_reassoc_sum {A B C : Ty α} {Γ : Ctx α ε}
  {r : Eqv φ Γ ⟨(A.coprod B).coprod C, e⟩}
  : reassoc_inv_sum (reassoc_sum r) = r := by
  rw [reassoc_sum, reassoc_inv_sum]
  simp [
    case_case, case_inl, case_inr, let1_beta_inl_var0, let1_beta_inr_var0, let1_beta_var0,
    case_inl_inl, case_eta
  ]

theorem Eqv.let1_reassoc_sum {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  : let1 a (reassoc_sum r) = reassoc_sum (let1 a r) := sorry

theorem Eqv.reassoc_sum_let1 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  : reassoc_sum (let1 a r) = let1 a (reassoc_sum r) := let1_reassoc_sum.symm

theorem Eqv.let2_reassoc_sum {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.prod Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  : let2 a (reassoc_sum r) = reassoc_sum (let2 a r) := sorry

theorem Eqv.reassoc_sum_let2 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.prod Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  : reassoc_sum (let2 a r) = let2 a (reassoc_sum r) := let2_reassoc_sum.symm

theorem Eqv.case_reassoc_sum {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.coprod Y, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  {s : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  : case a (reassoc_sum r) (reassoc_sum s) = reassoc_sum (case a r s) := sorry

theorem Eqv.reassoc_sum_case {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.coprod Y, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  {s : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  : reassoc_sum (case a r s) = case a (reassoc_sum r) (reassoc_sum s) := case_reassoc_sum.symm

theorem Eqv.wk_reassoc_sum {A B C : Ty α} {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ}
  {r : Eqv φ Δ ⟨(A.coprod B).coprod C, e⟩}
  : wk ρ (reassoc_sum r) = reassoc_sum (wk ρ r) := sorry

theorem Eqv.reassoc_sum_wk {A B C : Ty α} {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ}
  {r : Eqv φ Δ ⟨(A.coprod B).coprod C, e⟩}
  : reassoc_sum (wk ρ r) = wk ρ (reassoc_sum r) := wk_reassoc_sum.symm

theorem Eqv.wk1_reassoc_sum {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (head::Γ) ⟨(A.coprod B).coprod C, e⟩)
  : (reassoc_sum r).wk1 (inserted := inserted) = reassoc_sum r.wk1 := wk_reassoc_sum

theorem Eqv.reassoc_sum_wk0 {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ Γ ⟨(A.coprod B).coprod C, e⟩)
  : reassoc_sum r.wk0 = (reassoc_sum r).wk0 (head := head) := reassoc_sum_wk

theorem Eqv.reassoc_sum_wk1 {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (head::Γ) ⟨(A.coprod B).coprod C, e⟩)
  : reassoc_sum r.wk1 = (reassoc_sum r).wk1 (inserted := inserted) := reassoc_sum_wk

theorem Eqv.wk2_reassoc_sum {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (left::right::Γ) ⟨(A.coprod B).coprod C, e⟩)
  : (reassoc_sum r).wk2 (inserted := inserted) = reassoc_sum r.wk2 := wk_reassoc_sum

theorem Eqv.reassoc_sum_wk2 {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (left::right::Γ) ⟨(A.coprod B).coprod C, e⟩)
  : reassoc_sum r.wk2 = (reassoc_sum r).wk2 (inserted := inserted) := reassoc_sum_wk

theorem Eqv.seq_reassoc_sum {X Y A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ (⟨X, ⊥⟩::Γ) ⟨Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  : a ;;' (reassoc_sum r) = reassoc_sum (a ;;' r)
  := by rw [seq, wk1_reassoc_sum, let1_reassoc_sum]; rfl

theorem Eqv.reassoc_sum_seq {X Y A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ (⟨X, ⊥⟩::Γ) ⟨Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  : reassoc_sum (a ;;' r) = a ;;' (reassoc_sum r) := seq_reassoc_sum.symm

theorem Eqv.let1_reassoc_inv_sum {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  : let1 a (reassoc_inv_sum r) = reassoc_inv_sum (let1 a r) := sorry

theorem Eqv.reassoc_inv_sum_let1 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  : reassoc_inv_sum (let1 a r) = let1 a (reassoc_inv_sum r) := let1_reassoc_inv_sum.symm

theorem Eqv.let2_reassoc_inv_sum {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.prod Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  : let2 a (reassoc_inv_sum r) = reassoc_inv_sum (let2 a r) := sorry

theorem Eqv.reassoc_inv_sum_let2 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.prod Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  : reassoc_inv_sum (let2 a r) = let2 a (reassoc_inv_sum r) := let2_reassoc_inv_sum.symm

theorem Eqv.case_reassoc_inv_sum {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.coprod Y, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  {s : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  : case a (reassoc_inv_sum r) (reassoc_inv_sum s) = reassoc_inv_sum (case a r s) := sorry

theorem Eqv.reassoc_inv_sum_case {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.coprod Y, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  {s : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  : reassoc_inv_sum (case a r s) = case a (reassoc_inv_sum r) (reassoc_inv_sum s)
  := case_reassoc_inv_sum.symm

theorem Eqv.wk_reassoc_inv_sum {A B C : Ty α} {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ}
  {r : Eqv φ Δ ⟨A.coprod (B.coprod C), e⟩}
  : wk ρ (reassoc_inv_sum r) = reassoc_inv_sum (wk ρ r) := sorry

theorem Eqv.reassoc_inv_sum_wk {A B C : Ty α} {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ}
  {r : Eqv φ Δ ⟨A.coprod (B.coprod C), e⟩}
  : reassoc_inv_sum (wk ρ r) = wk ρ (reassoc_inv_sum r) := wk_reassoc_inv_sum.symm

theorem Eqv.wk0_reassoc_inv_sum {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ Γ ⟨A.coprod (B.coprod C), e⟩)
  : (reassoc_inv_sum r).wk0 (head := head) = reassoc_inv_sum r.wk0 := wk_reassoc_inv_sum

theorem Eqv.reassoc_inv_sum_wk0 {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ Γ ⟨A.coprod (B.coprod C), e⟩)
  : reassoc_inv_sum r.wk0 = (reassoc_inv_sum r).wk0 (head := head) := reassoc_inv_sum_wk

theorem Eqv.wk1_reassoc_inv_sum {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (head::Γ) ⟨A.coprod (B.coprod C), e⟩)
  : (reassoc_inv_sum r).wk1 (inserted := inserted) = reassoc_inv_sum r.wk1 := wk_reassoc_inv_sum

theorem Eqv.reassoc_inv_sum_wk1 {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (head::Γ) ⟨A.coprod (B.coprod C), e⟩)
  : reassoc_inv_sum r.wk1 = (reassoc_inv_sum r).wk1 (inserted := inserted) := reassoc_inv_sum_wk

theorem Eqv.wk2_reassoc_inv_sum {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (left::right::Γ) ⟨A.coprod (B.coprod C), e⟩)
  : (reassoc_inv_sum r).wk2 (inserted := inserted) = reassoc_inv_sum r.wk2 := wk_reassoc_inv_sum

theorem Eqv.reassoc_inv_sum_wk2 {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (left::right::Γ) ⟨A.coprod (B.coprod C), e⟩)
  : reassoc_inv_sum r.wk2 = (reassoc_inv_sum r).wk2 (inserted := inserted) := reassoc_inv_sum_wk

theorem Eqv.seq_reassoc_inv_sum {X Y A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ (⟨X, ⊥⟩::Γ) ⟨Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  : a ;;' (reassoc_inv_sum r) = reassoc_inv_sum (a ;;' r)
  := by rw [seq, wk1_reassoc_inv_sum, let1_reassoc_inv_sum]; rfl

theorem Eqv.reassoc_inv_sum_seq {X Y A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ (⟨X, ⊥⟩::Γ) ⟨Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  : reassoc_inv_sum (a ;;' r) = a ;;' (reassoc_inv_sum r) := seq_reassoc_inv_sum.symm

def Eqv.coprod {A B C : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩) (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩)
  : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) ⟨C, e⟩ := case nil l.wk1 r.wk1

def Eqv.inj_l {A B : Ty α} {Γ : Ctx α ε} : Eqv (φ := φ) (⟨A, ⊥⟩::Γ) ⟨A.coprod B, e⟩
  := inl nil

def Eqv.inj_r {A B : Ty α} {Γ : Ctx α ε} : Eqv (φ := φ) (⟨B, ⊥⟩::Γ) ⟨A.coprod B, e⟩
  := inr nil

-- TODO: lzero, rzero; appropriate isomorphisms

def Eqv.sum {A A' B B' : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩) (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) ⟨A'.coprod B', e⟩ := coprod (l.seq inj_l) (r.seq inj_r)

-- TODO: sum is a bifunctor; so that's nil nil and seq!

def Eqv.braid_sum {A B : Ty α} {Γ : Ctx α ε} : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) ⟨B.coprod A, e⟩
  := nil.swap_sum

theorem Eqv.braid_braid_sum
  : braid_sum (φ := φ) (A := A) (B := A) (Γ := Γ) (e := e) ;;' braid_sum = nil := by
  rw [braid_sum, seq_swap_sum, seq_nil, swap_sum_swap_sum]

def Eqv.assoc_sum {A B C : Ty α} {Γ : Ctx α ε}
  : Eqv φ (⟨(A.coprod B).coprod C, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩
  := nil.reassoc_sum

def Eqv.assoc_inv_sum {A B C : Ty α} {Γ : Ctx α ε}
  : Eqv φ (⟨A.coprod (B.coprod C), ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩
  := nil.reassoc_inv_sum

theorem Eqv.assoc_assoc_inv_sum
  : assoc_sum (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (e := e) ;;' assoc_inv_sum = nil := by
  rw [assoc_sum, assoc_inv_sum, seq_reassoc_inv_sum, seq_nil, reassoc_inv_reassoc_sum]

theorem Eqv.assoc_inv_assoc_sum
  : assoc_inv_sum (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (e := e) ;;' assoc_sum = nil := by
  rw [assoc_sum, assoc_inv_sum, seq_reassoc_sum, seq_nil, reassoc_reassoc_inv_sum]

-- TODO: assoc is natural

-- TODO: lzero, rzero are natural

-- TODO: triangle

-- TODO: pentagon

-- TODO: hexagon

-- TODO: zero, join

-- TODO: comonoid structure on _everything_

end Term

end BinSyntax
