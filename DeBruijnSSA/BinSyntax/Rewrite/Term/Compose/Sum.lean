import DeBruijnSSA.BinSyntax.Rewrite.Term.Eqv
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Seq
import DeBruijnSSA.BinSyntax.Rewrite.Term.Case
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
  {a : Eqv φ Γ ⟨X, e⟩} {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.coprod B, e⟩}
  : let1 a (swap_sum r) = swap_sum (let1 a r) := by simp only [swap_sum, case_let1]; rfl

theorem Eqv.swap_sum_let1 {A B : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A, e⟩} {r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B.coprod A, e⟩}
  : swap_sum (let1 a r) = let1 a (swap_sum r) := let1_swap_sum.symm

theorem Eqv.let2_swap_sum {A B : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.prod Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨A.coprod B, e⟩}
  : let2 a (swap_sum r) = swap_sum (let2 a r) := by simp only [swap_sum, case_let2]; rfl

theorem Eqv.swap_sum_let2 {A B : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.prod Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨A.coprod B, e⟩}
  : swap_sum (let2 a r) = let2 a (swap_sum r) := let2_swap_sum.symm

theorem Eqv.case_swap_sum {A B : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.coprod Y, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.coprod B, e⟩}
  {s : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨A.coprod B, e⟩}
  : case a (swap_sum r) (swap_sum s) = swap_sum (case a r s)
  := by simp only [swap_sum, case_case]; rfl

theorem Eqv.swap_sum_case {A B : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.coprod Y, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.coprod B, e⟩}
  {s : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨A.coprod B, e⟩}
  : swap_sum (case a r s) = case a (swap_sum r) (swap_sum s) := case_swap_sum.symm

theorem Eqv.wk_swap_sum {A B : Ty α} {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ}
  {r : Eqv φ Δ ⟨A.coprod B, e⟩}
  : wk ρ (swap_sum r) = swap_sum (wk ρ r) := by simp [swap_sum]

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
  : let1 a (reassoc_sum r) = reassoc_sum (let1 a r) := by simp only [reassoc_sum, case_let1]; rfl

theorem Eqv.reassoc_sum_let1 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  : reassoc_sum (let1 a r) = let1 a (reassoc_sum r) := let1_reassoc_sum.symm

theorem Eqv.let2_reassoc_sum {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.prod Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  : let2 a (reassoc_sum r) = reassoc_sum (let2 a r) := by simp only [reassoc_sum, case_let2]; rfl

theorem Eqv.reassoc_sum_let2 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.prod Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  : reassoc_sum (let2 a r) = let2 a (reassoc_sum r) := let2_reassoc_sum.symm

theorem Eqv.case_reassoc_sum {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.coprod Y, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  {s : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  : case a (reassoc_sum r) (reassoc_sum s) = reassoc_sum (case a r s)
  := by simp only [reassoc_sum, case_case]; rfl

theorem Eqv.reassoc_sum_case {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.coprod Y, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  {s : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩}
  : reassoc_sum (case a r s) = case a (reassoc_sum r) (reassoc_sum s) := case_reassoc_sum.symm

theorem Eqv.wk_reassoc_sum {A B C : Ty α} {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ}
  {r : Eqv φ Δ ⟨(A.coprod B).coprod C, e⟩}
  : wk ρ (reassoc_sum r) = reassoc_sum (wk ρ r) := by simp [reassoc_sum]

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
  : let1 a (reassoc_inv_sum r) = reassoc_inv_sum (let1 a r)
  := by simp only [reassoc_inv_sum, case_let1]; rfl

theorem Eqv.reassoc_inv_sum_let1 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  : reassoc_inv_sum (let1 a r) = let1 a (reassoc_inv_sum r) := let1_reassoc_inv_sum.symm

theorem Eqv.let2_reassoc_inv_sum {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.prod Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  : let2 a (reassoc_inv_sum r) = reassoc_inv_sum (let2 a r)
  := by simp only [reassoc_inv_sum, case_let2]; rfl

theorem Eqv.reassoc_inv_sum_let2 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.prod Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  : reassoc_inv_sum (let2 a r) = let2 a (reassoc_inv_sum r) := let2_reassoc_inv_sum.symm

theorem Eqv.case_reassoc_inv_sum {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.coprod Y, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  {s : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  : case a (reassoc_inv_sum r) (reassoc_inv_sum s) = reassoc_inv_sum (case a r s)
  := by simp only [reassoc_inv_sum, case_case]; rfl

theorem Eqv.reassoc_inv_sum_case {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X.coprod Y, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  {s : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩}
  : reassoc_inv_sum (case a r s) = case a (reassoc_inv_sum r) (reassoc_inv_sum s)
  := case_reassoc_inv_sum.symm

theorem Eqv.wk_reassoc_inv_sum {A B C : Ty α} {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ}
  {r : Eqv φ Δ ⟨A.coprod (B.coprod C), e⟩}
  : wk ρ (reassoc_inv_sum r) = reassoc_inv_sum (wk ρ r)
  := by simp [reassoc_inv_sum]

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

theorem Eqv.coprod_seq {A B C : Ty α} {Γ : Ctx α ε}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  {f : Eqv φ (⟨C, ⊥⟩::Γ) ⟨D, e⟩}
  : coprod l r ;;' f = coprod (l ;;' f) (r ;;' f)
  := by rw [coprod, seq, let1_case, coprod, wk1_seq, wk1_seq]; rfl

def Eqv.inj_l {A B : Ty α} {Γ : Ctx α ε} : Eqv (φ := φ) (⟨A, ⊥⟩::Γ) ⟨A.coprod B, e⟩
  := inl nil

@[simp]
theorem Eqv.wk1_inj_l {A B : Ty α} {Γ : Ctx α ε}
  : (inj_l (φ := φ) (e := e) (A := A) (B := B) (Γ := Γ)).wk1 (inserted := inserted) = inj_l
  := by simp [inj_l]

@[simp]
theorem Eqv.wk2_inj_l {A B : Ty α} {Γ : Ctx α ε}
  : (inj_l (φ := φ) (e := e) (A := A) (B := B) (Γ := head::Γ)).wk2 (inserted := inserted) = inj_l
  := by simp [inj_l]

theorem Eqv.seq_inj_l {A B C : Ty α} {Γ : Ctx α ε} {f : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  : f ;;' inj_l (B := C) = f.inl := by
  rw [seq, wk1_inj_l, inj_l]
  exact inl_bind.symm

def Eqv.inj_r {A B : Ty α} {Γ : Ctx α ε} : Eqv (φ := φ) (⟨B, ⊥⟩::Γ) ⟨A.coprod B, e⟩
  := inr nil

@[simp]
theorem Eqv.wk1_inj_r {A B : Ty α} {Γ : Ctx α ε}
  : (inj_r (φ := φ) (e := e) (A := A) (B := B) (Γ := Γ)).wk1 (inserted := inserted) = inj_r
  := by simp [inj_r]

@[simp]
theorem Eqv.wk2_inj_r {A B : Ty α} {Γ : Ctx α ε}
  : (inj_r (φ := φ) (e := e) (A := A) (B := B) (Γ := head::Γ)).wk2 (inserted := inserted) = inj_r
  := by simp [inj_r]

theorem Eqv.seq_inj_r {Γ : Ctx α ε} {f : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : f ;;' inj_r (A := A) = f.inr := by
  rw [seq, wk1_inj_r, inj_r]
  exact inr_bind.symm

theorem Eqv.coprod_inl_inr {A B : Ty α} {Γ : Ctx α ε}
  : coprod (Γ := Γ) (e := e) (inj_l (B := B) (φ := φ)) (inj_r (A := A) (φ := φ)) = nil
  := by simp [coprod, inj_l, inj_r, nil, case_eta]

theorem Eqv.inj_l_coprod {B B' C : Ty α} {Γ : Ctx α ε}
  {g : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  {h : Eqv φ (⟨B', ⊥⟩::Γ) ⟨C, e⟩}
  : inj_l ;;' coprod g h = g := by
  rw [inj_l, seq, <-wk_eff_nil (h := bot_le), <-wk_eff_inl, let1_beta, coprod]
  simp only [wk1_case, wk1_nil, subst_case, nil_subst0, wk_eff_inl, wk_eff_nil]
  rw [case_inl]
  convert nil_seq _
  rw [seq]
  congr
  induction g using Quotient.inductionOn
  apply Eqv.eq_of_term_eq
  simp only [Set.mem_setOf_eq, InS.coe_subst, Subst.InS.coe_lift, InS.coe_subst0, InS.coe_inl,
    InS.coe_var, InS.coe_wk, Ctx.InS.coe_wk2, Ctx.InS.coe_wk1, Term.wk_wk]
  simp only [← Term.subst_fromWk, Term.subst_subst]
  congr
  funext k; cases k <;> rfl

theorem Eqv.inl_coprod {A B B' C : Ty α} {Γ : Ctx α ε}
  {f : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  {g : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  {h : Eqv φ (⟨B', ⊥⟩::Γ) ⟨C, e⟩}
  : f.inl ;;' coprod g h = f ;;' g := by rw [<-seq_inj_l, <-seq_assoc, inj_l_coprod]

theorem Eqv.inj_r_coprod {B B' C : Ty α} {Γ : Ctx α ε}
  {g : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  {h : Eqv φ (⟨B', ⊥⟩::Γ) ⟨C, e⟩}
  : inj_r ;;' coprod g h = h := by
  rw [inj_r, seq, <-wk_eff_nil (h := bot_le), <-wk_eff_inr, let1_beta, coprod]
  simp only [wk1_case, wk1_nil, subst_case, nil_subst0, wk_eff_inr, wk_eff_nil]
  rw [case_inr]
  convert nil_seq _
  rw [seq]
  congr
  induction h using Quotient.inductionOn
  apply Eqv.eq_of_term_eq
  simp only [Set.mem_setOf_eq, InS.coe_subst, Subst.InS.coe_lift, InS.coe_subst0, InS.coe_inl,
    InS.coe_var, InS.coe_wk, Ctx.InS.coe_wk2, Ctx.InS.coe_wk1, Term.wk_wk]
  simp only [← Term.subst_fromWk, Term.subst_subst]
  congr
  funext k; cases k <;> rfl

theorem Eqv.inr_coprod {A B B' C : Ty α} {Γ : Ctx α ε}
  {f : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B', e⟩}
  {g : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  {h : Eqv φ (⟨B', ⊥⟩::Γ) ⟨C, e⟩}
  : f.inr ;;' coprod g h = f ;;' h := by rw [<-seq_inj_r, <-seq_assoc, inj_r_coprod]

theorem Eqv.wk1_coprod {B B' C : Ty α} {Γ : Ctx α ε}
  {g : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  {h : Eqv φ (⟨B', ⊥⟩::Γ) ⟨C, e⟩}
  : (coprod g h).wk1 (inserted := inserted) = coprod g.wk1 h.wk1 := by
  simp [coprod, wk1_wk2]

def Eqv.zero {Γ : Ctx α ε} {A : Ty α}
  : Eqv φ (⟨Ty.empty, ⊥⟩::Γ) (A, e)
  := (abort (var 0 (by simp)) A)

theorem Eqv.zero_eq {A : Ty α} {Γ : Ctx α ε}
  (r s : Eqv φ (⟨Ty.empty, ⊥⟩::Γ) (A, e)) : r = s
  := by apply Eqv.initial; exact ⟨(Ty.empty, ⊥), by simp, Ty.IsInitial.empty, rfl⟩

theorem Eqv.zero_seq {A B : Ty α} {Γ : Ctx α ε} {f : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  : zero ;;' f = zero := zero_eq _ _

def Eqv.lzero {Γ : Ctx α ε} {A : Ty α}
  : Eqv φ (⟨Ty.empty.coprod A, ⊥⟩::Γ) (A, e)
  := coprod zero nil

def Eqv.rzero {Γ : Ctx α ε} {A : Ty α}
  : Eqv φ (⟨A.coprod Ty.empty, ⊥⟩::Γ) (A, e)
  := coprod nil zero

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

theorem Eqv.braid_sum_def' {A B : Ty α} {Γ : Ctx α ε}
  : braid_sum (φ := φ) (A := A) (B := B) (Γ := Γ) (e := e) = coprod inj_r inj_l := rfl

def Eqv.assoc_sum {A B C : Ty α} {Γ : Ctx α ε}
  : Eqv φ (⟨(A.coprod B).coprod C, ⊥⟩::Γ) ⟨A.coprod (B.coprod C), e⟩
  := nil.reassoc_sum

theorem Eqv.assoc_sum_def' {A B C : Ty α} {Γ : Ctx α ε}
  : assoc_sum (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (e := e)
  = coprod (coprod inj_l (inj_l ;;' inj_r)) (inj_r ;;' inj_r) := by
  simp only [assoc_sum, reassoc_sum, coprod, wk1_inj_l, wk1_seq, wk1_inj_r, wk1_case, wk1_nil,
    wk2_inj_l, wk2_seq, wk2_inj_r, seq_inj_r, seq_inj_l]
  rfl

def Eqv.assoc_inv_sum {A B C : Ty α} {Γ : Ctx α ε}
  : Eqv φ (⟨A.coprod (B.coprod C), ⊥⟩::Γ) ⟨(A.coprod B).coprod C, e⟩
  := nil.reassoc_inv_sum

theorem Eqv.assoc_inv_sum_def' {A B C : Ty α} {Γ : Ctx α ε}
  : assoc_inv_sum (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (e := e)
  = coprod (inj_l ;;' inj_l) (coprod (inj_r ;;' inj_l) inj_r) := by
  simp only [assoc_inv_sum, reassoc_inv_sum, coprod, wk1_inj_l, wk1_seq, wk1_inj_r, wk1_case,
    wk1_nil, wk2_inj_l, wk2_seq, wk2_inj_r, seq_inj_r, seq_inj_l]
  rfl

theorem Eqv.assoc_assoc_inv_sum
  : assoc_sum (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (e := e) ;;' assoc_inv_sum = nil := by
  rw [assoc_sum, assoc_inv_sum, seq_reassoc_inv_sum, seq_nil, reassoc_inv_reassoc_sum]

theorem Eqv.assoc_inv_assoc_sum
  : assoc_inv_sum (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (e := e) ;;' assoc_sum = nil := by
  rw [assoc_sum, assoc_inv_sum, seq_reassoc_sum, seq_nil, reassoc_reassoc_inv_sum]

theorem Eqv.assoc_sum_nat {A B C A' B' C' : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (A', e)) (m : Eqv φ (⟨B, ⊥⟩::Γ) (B', e)) (r : Eqv φ (⟨C, ⊥⟩::Γ) (C', e))
  : sum (sum l m) r ;;' assoc_sum = assoc_sum ;;' sum l (sum m r)
  := by simp only [
    sum, coprod_seq, <-seq_assoc, inj_l_coprod, inj_r_coprod, assoc_sum_def'
  ]

theorem Eqv.triangle_sum {X Y : Ty α} {Γ : Ctx α ε}
  : assoc_sum (φ := φ) (Γ := Γ) (e := e) (A := X) (B := Ty.empty) (C := Y) ;;' nil.sum lzero
  = rzero.sum nil := by simp only [
    assoc_sum_def', coprod_seq, <-seq_assoc, lzero, rzero, inj_l_coprod, inj_r_coprod, zero_seq, sum
  ]

theorem Eqv.pentagon_sum {W X Y Z : Ty α} {Γ : Ctx α ε}
  : assoc_sum (φ := φ) (Γ := Γ) (e := e) (A := W.coprod X) (B := Y) (C := Z) ;;' assoc_sum
  = assoc_sum.sum nil ;;' assoc_sum ;;' nil.sum assoc_sum := by simp only [
    assoc_sum_def', coprod_seq, inj_l_coprod, <-seq_assoc, inj_r_coprod, nil_seq, sum
  ]

theorem Eqv.hexagon_sum {X Y Z : Ty α} {Γ : Ctx α ε}
  : assoc_sum (φ := φ) (Γ := Γ) (e := e) (A := X) (B := Y) (C := Z) ;;' braid_sum ;;' assoc_sum
  = braid_sum.sum nil ;;' assoc_sum ;;' nil.sum braid_sum := by simp only [
    braid_sum_def', assoc_sum_def', nil_seq, coprod_seq, <-seq_assoc, inj_r_coprod, inj_l_coprod,
    sum
  ]

-- TODO: join

-- TODO: comonoid structure on _everything_

end Term

end BinSyntax
