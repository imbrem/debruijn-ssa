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

@[simp]
theorem InS.coe_tensor {A A' B B' : Ty α} {Γ : Ctx α ε}
  (l : InS φ (⟨A, ⊥⟩::Γ) ⟨A', lo⟩) (r : InS φ (⟨B, ⊥⟩::Γ) ⟨B', lo⟩)
  : (l.tensor r).val = Term.let2 Term.nil (Term.pair l.val.wk1.wk0 r.val.wk1.wk1) := by
  rfl

theorem InS.wk_slift_tensor {A A' B B' : Ty α} {Γ : Ctx α ε} {ρ : Γ.InS Δ}
  (l : InS φ (⟨A, ⊥⟩::Δ) ⟨A', e⟩) (r : InS φ (⟨B, ⊥⟩::Δ) ⟨B', e⟩)
  : (l.tensor r).wk ρ.slift = (l.wk ρ.slift).tensor (r.wk ρ.slift) := by
  ext
  simp only [Set.mem_setOf_eq, coe_wk, Term.wk, Ctx.InS.coe_lift, Nat.liftWk_zero, coe_wk0, coe_wk1,
    coe_tensor]
  congr 2
  simp only [Term.wk1, Term.wk0, Term.wk_wk]
  congr
  funext k
  cases k <;> rfl
  simp only [Term.wk1, Term.wk0, Term.wk_wk]
  congr
  funext k
  cases k <;> rfl

theorem InS.wk1_tensor {A A' B B' : Ty α} {Γ : Ctx α ε}
  (l : InS φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩) (r : InS φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : (l.tensor r).wk1 (inserted := inserted) = l.wk1.tensor r.wk1 := by
  simp only [wk1, <-Ctx.InS.lift_wk0, wk_slift_tensor]

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

def pl (t : Term φ) := let2 t (var 1)

@[simp]
theorem wk_pl {t : Term φ} : t.pl.wk ρ = (t.wk ρ).pl := rfl

@[simp]
theorem subst_pl {t : Term φ} : t.pl.subst σ = (t.subst σ).pl := rfl

theorem wk0_pl {t : Term φ} : t.pl.wk0 = (t.wk0).pl := rfl

theorem wk1_pl {t : Term φ} : t.pl.wk1 = (t.wk1).pl := rfl

theorem Wf.pl {A B : Ty α} {Γ : Ctx α ε} {t : Term φ} (ht : t.Wf Γ ⟨A.prod B, e⟩)
  : (pl t).Wf Γ ⟨A, e⟩ := by
  apply let2 ht
  apply var (by simp)

def pr (t : Term φ) := let2 t (var 0)

@[simp]
theorem wk_pr {t : Term φ} : t.pr.wk ρ = (t.wk ρ).pr := rfl

@[simp]
theorem subst_pr {t : Term φ} : t.pr.subst σ = (t.subst σ).pr := rfl

theorem wk0_pr {t : Term φ} : t.pr.wk0 = (t.wk0).pr := rfl

theorem wk1_pr {t : Term φ} : t.pr.wk1 = (t.wk1).pr := rfl

theorem Wf.pr {A B : Ty α} {Γ : Ctx α ε} {t : Term φ} (ht : t.Wf Γ ⟨A.prod B, e⟩)
  : (pr t).Wf Γ ⟨B, e⟩ := by
  apply let2 ht
  apply var (by simp)

def InS.pl {A B : Ty α} {Γ : Ctx α ε} (t : InS φ Γ ⟨A.prod B, e⟩) : InS φ Γ ⟨A, e⟩
  := let2 t (var 1 (by simp))

@[simp]
theorem InS.coe_pl {A B : Ty α} {Γ : Ctx α ε} (t : InS φ Γ ⟨A.prod B, e⟩)
  : (InS.pl t).val = Term.let2 t.val (Term.var 1) := by
  rfl

@[simp]
theorem InS.wk_pl {A B : Ty α} {Γ : Ctx α ε} {ρ : Γ.InS Δ} (t : InS φ Δ ⟨A.prod B, e⟩)
  : (t.pl).wk ρ = (t.wk ρ).pl := rfl

@[simp]
theorem InS.subst_pl {A B : Ty α} {Γ : Ctx α ε} {σ : Subst.InS φ Γ Δ} (t : InS φ Δ ⟨A.prod B, e⟩)
  : (t.pl).subst σ = (t.subst σ).pl := rfl

theorem InS.wk0_pl {A B : Ty α} {Γ : Ctx α ε} (t : InS φ Γ ⟨A.prod B, e⟩)
  : (t.pl).wk0 (head := head) = (t.wk0).pl := rfl

theorem InS.wk1_pl {A B : Ty α} {Γ : Ctx α ε} (t : InS φ (head::Γ) ⟨A.prod B, e⟩)
  : (t.pl).wk1 (inserted := inserted) = (t.wk1).pl := rfl

def InS.pr {A B : Ty α} {Γ : Ctx α ε} (t : InS φ Γ ⟨A.prod B, e⟩) : InS φ Γ ⟨B, e⟩
  := let2 t (var 0 (by simp))

@[simp]
theorem InS.coe_pr {A B : Ty α} {Γ : Ctx α ε} (t : InS φ Γ ⟨A.prod B, e⟩)
  : (InS.pr t).val = Term.let2 t.val (Term.var 0) := by
  rfl

@[simp]
theorem InS.wk_pr {A B : Ty α} {Γ : Ctx α ε} {ρ : Γ.InS Δ} (t : InS φ Δ ⟨A.prod B, e⟩)
  : (t.pr).wk ρ = (t.wk ρ).pr := rfl

@[simp]
theorem InS.subst_pr {A B : Ty α} {Γ : Ctx α ε} {σ : Subst.InS φ Γ Δ} (t : InS φ Δ ⟨A.prod B, e⟩)
  : (t.pr).subst σ = (t.subst σ).pr := rfl

theorem InS.wk0_pr {A B : Ty α} {Γ : Ctx α ε} (t : InS φ Γ ⟨A.prod B, e⟩)
  : (t.pr).wk0 (head := head) = (t.wk0).pr := rfl

theorem InS.wk1_pr {A B : Ty α} {Γ : Ctx α ε} (t : InS φ (head::Γ) ⟨A.prod B, e⟩)
  : (t.pr).wk1 (inserted := inserted) = (t.wk1).pr := rfl
