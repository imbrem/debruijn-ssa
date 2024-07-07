import DeBruijnSSA.BinSyntax.Rewrite.Term.Eqv

import Discretion.Utils.Quotient

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

def Eqv.nil {A : Ty α} {Γ : Ctx α ε} : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A, e⟩
  := var 0 (by simp)

@[simp]
theorem Eqv.wk1_nil {A : Ty α} {Γ : Ctx α ε}
  : (nil (φ := φ) (A := A) (Γ := Γ) (e := e)).wk1 (inserted := inserted) = nil
  := rfl

def Eqv.seq {A B C : Ty α} {Γ : Ctx α ε}
(a : Eqv φ ((A, ⊥)::Γ) (B, e)) (b : Eqv φ ((B, ⊥)::Γ) (C, e))
  : Eqv φ ((A, ⊥)::Γ) (C, e)
  := let1 a b.wk1

infixl:65 " ;;' "  => Eqv.seq

theorem Eqv.seq_pure {A B C : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ ((A, ⊥)::Γ) (B, ⊥)) (b : Eqv φ ((B, ⊥)::Γ) (C, ⊥)) : a ;;' b = b.wk1.subst a.subst0
  := let1_beta_pure

theorem Eqv.pure_seq {A B C : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ ((A, ⊥)::Γ) (B, ⊥)) (b : Eqv φ ((B, ⊥)::Γ) (C, e))
  : (a.wk_eff (by simp)) ;;' b = b.wk1.subst a.subst0
  := let1_beta

theorem Eqv.seq_nil {A B : Ty α} {Γ : Ctx α ε} (a : Eqv φ ((A, ⊥)::Γ) (B, e))
  : a ;;' nil = a := let1_eta

theorem Eqv.nil_seq {A B : Ty α} {Γ : Ctx α ε} (a : Eqv φ ((A, ⊥)::Γ) (B, e))
  : nil ;;' a = a := by
  rw [ seq, nil, <-wk_eff_var (lo := ⊥) (he := bot_le) (hn := Ctx.Var.shead), let1_beta]
  induction a using Quotient.inductionOn
  simp only [var, subst0_quot, wk1_quot, subst_quot]
  -- TODO: lift to InS...
  congr
  ext
  simp

theorem Eqv.seq_assoc {A B C D : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ ((A, ⊥)::Γ) (B, e)) (b : Eqv φ ((B, ⊥)::Γ) (C, e)) (c : Eqv φ ((C, ⊥)::Γ) (D, e))
  : a ;;' (b ;;' c) = (a ;;' b) ;;' c := by simp only [seq, let1_let1, wk1_let1, wk1_wk2]

def Eqv.pi_l {A B : Ty α} {Γ : Ctx α ε} : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨A, e⟩
  := let2 nil (var 1 (by simp))

def Eqv.pi_r {A B : Ty α} {Γ : Ctx α ε} : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨B, e⟩
  := let2 nil (var 0 (by simp))

-- TODO: lunit, runit, pi_l_lunit, pi_r_runit, lunit_pi_l, runit_pi_r

def Eqv.prod {A B C : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩) (r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩)
  : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B.prod C, e⟩ := let1 nil (pair l.wk1 r.wk1)

def Eqv.tensor {A A' B B' : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩) (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨A'.prod B', e⟩ := let2 nil (pair l.wk1.wk0 r.wk1.wk1)

theorem Eqv.tensor_nil_nil {A B : Ty α} {Γ : Ctx α ε}
  : tensor (φ := φ) (Γ := Γ) (A := A) (A' := A) (B := B) (B' := B) (e := e) nil nil = nil := by
  simp [tensor, nil, let2_eta]

def Eqv.ltimes {A A' B : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩)
  : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨A'.prod B, e⟩ := tensor l nil

theorem Eqv.ltimes_nil {A B : Ty α} {Γ : Ctx α ε}
  : ltimes (φ := φ) (Γ := Γ) (A := A) (A' := A) (B := B) (e := e) nil = nil := tensor_nil_nil

-- TODO: ltimes_seq

def Eqv.rtimes {A B B' : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨A.prod B', e⟩ := tensor nil r

theorem Eqv.rtimes_nil {A B : Ty α} {Γ : Ctx α ε}
  : rtimes (φ := φ) (Γ := Γ) (A := A) (B := B) (B' := B) (e := e) nil = nil := tensor_nil_nil

-- TODO: rtimes_seq

-- TODO: ltimes comm pure

-- TODO: rtimes comm pure

-- TODO: tensor_seq (pure only)

-- TODO: swap

def Eqv.split {A : Ty α} {Γ : Ctx α ε} : Eqv (φ := φ) (⟨A, ⊥⟩::Γ) ⟨A.prod A, e⟩
  := let1 nil (pair nil nil)

-- TODO: split_seq (pure only)

def Eqv.assoc {A B C : Ty α} {Γ : Ctx α ε}
  : Eqv (φ := φ) (⟨(A.prod B).prod C, ⊥⟩::Γ) ⟨A.prod (B.prod C), e⟩ :=
  let2 nil $
  let2 (var (V := (A.prod B, e)) 1 (by simp)) $
  pair (var 1 (by simp)) (pair (var 0 (by simp)) (var 2 (by simp)))

def Eqv.assoc_inv {A B C : Ty α} {Γ : Ctx α ε}
  : Eqv (φ := φ) (⟨A.prod (B.prod C), ⊥⟩::Γ) ⟨(A.prod B).prod C, e⟩ :=
  let2 nil $
  let2 (var (V := (B.prod C, e)) 0 (by simp)) $
  pair (pair (var 3 (by simp)) (var 1 (by simp))) (var 0 (by simp))

-- TODO: assoc_assoc_inv, assoc_inv_assoc

def Eqv.coprod {A B C : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩) (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩)
  : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) ⟨C, e⟩ := case nil l.wk1 r.wk1

def Eqv.inj_l {A B : Ty α} {Γ : Ctx α ε} : Eqv (φ := φ) (⟨A, ⊥⟩::Γ) ⟨A.coprod B, e⟩
  := inl nil

def Eqv.inj_r {A B : Ty α} {Γ : Ctx α ε} : Eqv (φ := φ) (⟨B, ⊥⟩::Γ) ⟨A.coprod B, e⟩
  := inr nil

def Eqv.sum {A A' B B' : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩) (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) ⟨A'.coprod B', e⟩ := coprod (l.seq inj_l) (r.seq inj_r)
