import DeBruijnSSA.BinSyntax.Typing.Term.Subst
import DeBruijnSSA.BinSyntax.Syntax.Compose.Term

namespace BinSyntax

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [OrderBot ε]
  {Γ Δ : Ctx α ε} {σ : Term.Subst φ}

namespace Term

@[simp]
theorem Wf.nil {A : Ty α} {Γ : Ctx α ε} : nil.Wf (φ := φ) (⟨A, ⊥⟩::Γ) ⟨A, e⟩
  := var (by simp)

def InS.nil {A : Ty α} {Γ : Ctx α ε} : InS (φ := φ) (⟨A, ⊥⟩::Γ) ⟨A, e⟩
  := var 0 (by simp)

theorem Wf.seq {A B : Ty α} {Γ : Ctx α ε} {l r : Term φ}
  (hl : l.Wf (⟨A, ⊥⟩::Γ) ⟨B, e⟩) (hr : r.Wf (⟨B, ⊥⟩::Γ) ⟨C, e⟩)
  : (l.seq r).Wf (⟨A, ⊥⟩::Γ) ⟨C, e⟩
  := let1 hl hr.wk1

def InS.seq {A B C : Ty α} {Γ : Ctx α ε}
  (l : InS φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩) (r : InS φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩)
  : InS φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩ := let1 l r.wk1

theorem InS.seq_wk_eff {A B : Ty α} {Γ : Ctx α ε} (h : lo ≤ hi)
  (l : InS φ (⟨A, ⊥⟩::Γ) ⟨B, lo⟩) (r : InS φ (⟨B, ⊥⟩::Γ) ⟨C, lo⟩)
  : (l.wk_eff h).seq (r.wk_eff h) = (l.seq r).wk_eff h := rfl

theorem Wf.pseq {A B : Ty α} {Γ : Ctx α ε} {l r : Term φ}
  (hl : l.Wf (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩) (hr : r.Wf (⟨B, ⊥⟩::Γ) ⟨C, ⊥⟩)
  : (l.pseq r).Wf (⟨A, ⊥⟩::Γ) ⟨C, ⊥⟩
  := hr.wk1.subst hl.subst0

def InS.pseq {A B C : Ty α} {Γ : Ctx α ε}
  (l : InS φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩) (r : InS φ (⟨B, ⊥⟩::Γ) ⟨C, ⊥⟩)
  : InS φ (⟨A, ⊥⟩::Γ) ⟨C, ⊥⟩ := r.wk1.subst l.subst0

theorem Wf.pi_l {A B : Ty α} {Γ : Ctx α ε}
  : pi_l.Wf (φ := φ) (⟨A.prod B, ⊥⟩::Γ) ⟨A, e⟩
  := let2 nil (var (by simp))

def InS.pi_l {A B : Ty α} {Γ : Ctx α ε} : InS φ (⟨A.prod B, ⊥⟩::Γ) ⟨A, e⟩
  := let2 nil (var 1 (by simp))

theorem Wf.pi_r {A B : Ty α} {Γ : Ctx α ε}
  : pi_r.Wf (φ := φ) (⟨A.prod B, ⊥⟩::Γ) ⟨B, e⟩
  := let2 nil (var (by simp))

def InS.pi_r {A B : Ty α} {Γ : Ctx α ε} : InS φ (⟨A.prod B, ⊥⟩::Γ) ⟨B, e⟩
  := let2 nil (var 0 (by simp))

theorem Wf.prod {A B C : Ty α} {Γ : Ctx α ε} {l r : Term φ}
  (hl : l.Wf (⟨A, ⊥⟩::Γ) ⟨B, e⟩) (hr : r.Wf (⟨A, ⊥⟩::Γ) ⟨C, e⟩)
  : (l.prod r).Wf (⟨A, ⊥⟩::Γ) ⟨B.prod C, e⟩
  := let1 nil (pair hl.wk1 hr.wk1)

def InS.prod {A B C : Ty α} {Γ : Ctx α ε}
  (l : InS φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩) (r : InS φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩)
  : InS φ (⟨A, ⊥⟩::Γ) ⟨B.prod C, e⟩ := let1 nil (pair l.wk1 r.wk1)

theorem Wf.tensor {A A' B B' : Ty α} {Γ : Ctx α ε} {l r : Term φ}
  (hl : l.Wf (⟨A, ⊥⟩::Γ) ⟨A', e⟩) (hr : r.Wf (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : (l.tensor r).Wf (⟨A.prod B, ⊥⟩::Γ) ⟨A'.prod B', e⟩
  := let2 nil (pair hl.wk1.wk0 hr.wk1.wk1)

def InS.tensor {A A' B B' : Ty α} {Γ : Ctx α ε}
  (l : InS φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩) (r : InS φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : InS φ (⟨A.prod B, ⊥⟩::Γ) ⟨A'.prod B', e⟩ := let2 nil (pair l.wk1.wk0 r.wk1.wk1)

theorem Wf.split {A : Ty α} {Γ : Ctx α ε} : split.Wf (φ := φ) (⟨A, ⊥⟩::Γ) ⟨A.prod A, e⟩
  := let1 nil (pair nil nil)

def InS.split {A : Ty α} {Γ : Ctx α ε} : InS (φ := φ) (⟨A, ⊥⟩::Γ) ⟨A.prod A, e⟩
  := let1 nil (pair nil nil)

theorem Wf.assoc {A B C : Ty α} {Γ : Ctx α ε}
  : assoc.Wf (φ := φ) (⟨(A.prod B).prod C, ⊥⟩::Γ) ⟨A.prod (B.prod C), e⟩ := by
  apply let2 nil
  apply let2 (var (V := (A.prod B, e)) (by simp))
  simp

def InS.assoc {A B C : Ty α} {Γ : Ctx α ε}
  : InS (φ := φ) (⟨(A.prod B).prod C, ⊥⟩::Γ) ⟨A.prod (B.prod C), e⟩ :=
  let2 nil $
  let2 (var (V := (A.prod B, e)) 1 (by simp)) $
  pair (var 1 (by simp)) (pair (var 0 (by simp)) (var 2 (by simp)))

theorem Wf.assoc_inv {A B C : Ty α} {Γ : Ctx α ε}
  : assoc_inv.Wf (φ := φ) (⟨A.prod (B.prod C), ⊥⟩::Γ) ⟨(A.prod B).prod C, e⟩ := by
  apply let2 nil
  apply let2 nil
  simp

def InS.assoc_inv {A B C : Ty α} {Γ : Ctx α ε}
  : InS (φ := φ) (⟨A.prod (B.prod C), ⊥⟩::Γ) ⟨(A.prod B).prod C, e⟩ :=
  let2 nil $
  let2 (var (V := (B.prod C, e)) 0 (by simp)) $
  pair (pair (var 3 (by simp)) (var 1 (by simp))) (var 0 (by simp))

theorem Wf.coprod {A B C : Ty α} {Γ : Ctx α ε} {l r : Term φ}
  (hl : l.Wf (⟨A, ⊥⟩::Γ) ⟨C, e⟩) (hr : r.Wf (⟨B, ⊥⟩::Γ) ⟨C, e⟩)
  : (l.coprod r).Wf (⟨A.coprod B, ⊥⟩::Γ) ⟨C, e⟩
  := case nil hl.wk1 hr.wk1

def InS.coprod {A B C : Ty α} {Γ : Ctx α ε}
  (l : InS φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩) (r : InS φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩)
  : InS φ (⟨A.coprod B, ⊥⟩::Γ) ⟨C, e⟩ := case nil l.wk1 r.wk1

theorem Wf.inj_l {A B : Ty α} {Γ : Ctx α ε} : inj_l.Wf (φ := φ) (⟨A, ⊥⟩::Γ) ⟨A.coprod B, e⟩
  := inl nil

def InS.inj_l {A B : Ty α} {Γ : Ctx α ε} : InS (φ := φ) (⟨A, ⊥⟩::Γ) ⟨A.coprod B, e⟩
  := inl nil

theorem Wf.inj_r {A B : Ty α} {Γ : Ctx α ε} : inj_r.Wf (φ := φ) (⟨B, ⊥⟩::Γ) ⟨A.coprod B, e⟩
  := inr nil

def InS.inj_r {A B : Ty α} {Γ : Ctx α ε} : InS (φ := φ) (⟨B, ⊥⟩::Γ) ⟨A.coprod B, e⟩
  := inr nil

theorem Wf.sum {A A' B B' : Ty α} {Γ : Ctx α ε} {l r : Term φ}
  (hl : l.Wf (⟨A, ⊥⟩::Γ) ⟨A', e⟩) (hr : r.Wf (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : (l.sum r).Wf (⟨A.coprod B, ⊥⟩::Γ) ⟨A'.coprod B', e⟩
  := coprod (hl.seq inj_l) (hr.seq inj_r)

def InS.sum {A A' B B' : Ty α} {Γ : Ctx α ε}
  (l : InS φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩) (r : InS φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : InS φ (⟨A.coprod B, ⊥⟩::Γ) ⟨A'.coprod B', e⟩ := coprod (l.seq inj_l) (r.seq inj_r)
