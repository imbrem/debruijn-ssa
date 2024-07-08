import DeBruijnSSA.BinSyntax.Rewrite.Term.Eqv
import DeBruijnSSA.BinSyntax.Typing.Term.Compose

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

@[simp]
theorem Eqv.wk_eff_nil {A : Ty α} {Γ : Ctx α ε} (h : lo ≤ hi)
  : (nil (φ := φ) (A := A) (Γ := Γ)).wk_eff h = nil
  := rfl

@[simp]
theorem Eqv.subst0_nil_wk1 {Γ : Ctx α ε}
  (a : Eqv φ (⟨A, ⊥⟩::Γ) V) : a.wk1.subst nil.subst0 = a
  := by simp [nil]

@[simp]
theorem Eqv.nil_subst0 {Γ : Ctx α ε} (a : Eqv φ Γ ⟨A, ⊥⟩)
  : (nil (e := e)).subst a.subst0 = a.wk_eff bot_le
  := by induction a using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.nil_pure {A : Ty α} {Γ : Ctx α ε} : (nil (φ := φ) (A := A) (Γ := Γ) (e := e)).Pure
  := ⟨nil, rfl⟩

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

@[simp]
theorem Eqv.seq_quot {A B C : Ty α} {Γ : Ctx α ε}
  (a : InS φ ((A, ⊥)::Γ) (B, e)) (b : InS φ ((B, ⊥)::Γ) (C, e))
  : ⟦a⟧ ;;' ⟦b⟧ = ⟦a.seq b⟧
  := rfl

theorem Eqv.seq_wk_eff {A B C : Ty α} {Γ : Ctx α ε} {h : lo ≤ hi}
  {a : Eqv φ ((A, ⊥)::Γ) (B, lo)} {b : Eqv φ ((B, ⊥)::Γ) (C, lo)}
  : (a.wk_eff h) ;;' (b.wk_eff h) = (a ;;' b).wk_eff h := by
  induction a using Quotient.inductionOn;
  induction b using Quotient.inductionOn;
  rfl

theorem Eqv.wk_eff_seq {A B C : Ty α} {Γ : Ctx α ε} {h : lo ≤ hi}
  {a : Eqv φ ((A, ⊥)::Γ) (B, lo)} {b : Eqv φ ((B, ⊥)::Γ) (C, lo)}
  : (a ;;' b).wk_eff h = (a.wk_eff h) ;;' (b.wk_eff h) := seq_wk_eff.symm

theorem Eqv.seq_nil {A B : Ty α} {Γ : Ctx α ε} (a : Eqv φ ((A, ⊥)::Γ) (B, e))
  : a ;;' nil = a := let1_eta

theorem Eqv.nil_seq {A B : Ty α} {Γ : Ctx α ε} (a : Eqv φ ((A, ⊥)::Γ) (B, e))
  : nil ;;' a = a := by
  rw [seq, <-wk_eff_nil (lo := ⊥), let1_beta, subst0_nil_wk1]

theorem Eqv.let1_seq {A B C : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ ((A, ⊥)::Γ) (B, e))
  (b : Eqv φ ((B, ⊥)::(A, ⊥)::Γ) (C, e)) (c : Eqv φ ((C, ⊥)::Γ) (D, e))
  : a.let1 b ;;' c = a.let1 (b ;;' c.wk1) := by rw [seq, seq, let1_let1]

theorem Eqv.let2_seq {A B C D : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ ((A, ⊥)::Γ) (B.prod B', e))
  (b : Eqv φ ((B', ⊥)::(B, ⊥)::(A, ⊥)::Γ) (C, e)) (c : Eqv φ ((C, ⊥)::Γ) (D, e))
  : a.let2 b ;;' c = a.let2 (b ;;' c.wk1.wk1) := by rw [seq, seq, let1_let2]

theorem Eqv.seq_assoc {A B C D : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ ((A, ⊥)::Γ) (B, e)) (b : Eqv φ ((B, ⊥)::Γ) (C, e)) (c : Eqv φ ((C, ⊥)::Γ) (D, e))
  : a ;;' (b ;;' c) = (a ;;' b) ;;' c := by simp only [seq, let1_let1, wk1_let1, wk1_wk2]

def Eqv.pi_l {A B : Ty α} {Γ : Ctx α ε} : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨A, e⟩
  := let2 nil (var 1 (by simp))

def Eqv.pi_r {A B : Ty α} {Γ : Ctx α ε} : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨B, e⟩
  := let2 nil (var 0 (by simp))

@[simp]
theorem Eqv.pi_l_is_pure {A B : Ty α} {Γ : Ctx α ε}
  : (pi_l (φ := φ) (A := A) (B := B) (Γ := Γ) (e := e)).Pure := ⟨pi_l, rfl⟩

@[simp]
theorem Eqv.pi_r_is_pure {A B : Ty α} {Γ : Ctx α ε}
  : (pi_r (φ := φ) (A := A) (B := B) (Γ := Γ) (e := e)).Pure := ⟨pi_r, rfl⟩

@[simp]
theorem Eqv.wk1_pi_l {A B : Ty α} {Γ : Ctx α ε}
  : (pi_l : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨A, e⟩).wk1 (inserted := inserted) = pi_l := rfl

@[simp]
theorem Eqv.wk1_pi_r {A B : Ty α} {Γ : Ctx α ε}
  : (pi_r : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨B, e⟩).wk1 (inserted := inserted) = pi_r := rfl

@[simp]
theorem Eqv.wk_eff_pi_l {A B : Ty α} {Γ : Ctx α ε} {h : lo ≤ hi}
  : (pi_l : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨A, lo⟩).wk_eff h = pi_l := rfl

@[simp]
theorem Eqv.wk_eff_pi_r {A B : Ty α} {Γ : Ctx α ε} {h : lo ≤ hi}
  : (pi_r : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨B, lo⟩).wk_eff h = pi_r := rfl

@[simp]
theorem Eqv.wk_lift_pi_l {A B B' : Ty α} {Δ : Ctx α ε} {ρ : Ctx.InS Γ Δ} {h}
  : (pi_l : Eqv φ (⟨A.prod B, ⊥⟩::Δ) ⟨A, lo⟩).wk (ρ.lift h)
  = (pi_l : Eqv φ (⟨A.prod B', ⊥⟩::Γ) ⟨A, lo⟩) := rfl

@[simp]
theorem Eqv.wk_lift_pi_r {A B A' : Ty α} {Δ : Ctx α ε} {ρ : Ctx.InS Γ Δ} {h}
  : (pi_r : Eqv φ (⟨A.prod B, ⊥⟩::Δ) ⟨B, lo⟩).wk (ρ.lift h)
  = (pi_r : Eqv φ (⟨A'.prod B, ⊥⟩::Γ) ⟨B, lo⟩) := rfl

@[simp]
theorem Eqv.subst_lift_pi_l {A B B' : Ty α} {Δ : Ctx α ε} {σ : Subst.Eqv φ Γ Δ} {h}
  : (pi_l : Eqv φ (⟨A.prod B, ⊥⟩::Δ) ⟨A, e⟩).subst (σ.lift h)
  = (pi_l : Eqv φ (⟨A.prod B', ⊥⟩::Γ) ⟨A, e⟩) := by
  induction σ using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.subst_lift_pi_r {A B A' : Ty α} {Δ : Ctx α ε} {σ : Subst.Eqv φ Γ Δ} {h}
  : (pi_r : Eqv φ (⟨A.prod B, ⊥⟩::Δ) ⟨B, e⟩).subst (σ.lift h)
  = (pi_r : Eqv φ (⟨A'.prod B, ⊥⟩::Γ) ⟨B, e⟩) := by
  induction σ using Quotient.inductionOn; rfl

theorem Eqv.subst0_pi_l {A B : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ Γ ⟨A.prod B, ⊥⟩) : pi_l.subst a.subst0 = let2 a (var 1 (by simp)) := by
  simp [pi_l]

def Eqv.runit {A : Ty α} {Γ : Ctx α ε} : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A.prod Ty.unit, e⟩
  := pair (var 0 (by simp)) (unit e)

def Eqv.lunit {A : Ty α} {Γ : Ctx α ε} : Eqv φ (⟨A, ⊥⟩::Γ) ⟨Ty.unit.prod A, e⟩
  := pair (unit e) (var 0 (by simp))

@[simp]
theorem Eqv.runit_subst0 {A : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ Γ ⟨A, ⊥⟩) : runit.subst a.subst0 = pair (a.wk_eff bot_le) (unit e) := by
  induction a using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.lunit_subst0 {A : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ Γ ⟨A, ⊥⟩) : lunit.subst a.subst0 = pair (unit e) (a.wk_eff bot_le) := by
  induction a using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.runit_wk1 {A : Ty α} {Γ : Ctx α ε}
  : (runit : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A.prod Ty.unit, e⟩).wk1 (inserted := inserted) = runit := rfl

@[simp]
theorem Eqv.lunit_wk1 {A : Ty α} {Γ : Ctx α ε}
  : (lunit : Eqv φ (⟨A, ⊥⟩::Γ) ⟨Ty.unit.prod A, e⟩).wk1 (inserted := inserted) = lunit := rfl

@[simp]
theorem Eqv.runit_is_pure {A : Ty α} {Γ : Ctx α ε}
  : (runit : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A.prod Ty.unit, e⟩).Pure
  := ⟨runit, rfl⟩

@[simp]
theorem Eqv.lunit_is_pure {A : Ty α} {Γ : Ctx α ε}
  : (lunit : Eqv φ (⟨A, ⊥⟩::Γ) ⟨Ty.unit.prod A, e⟩).Pure
  := ⟨lunit, rfl⟩

theorem Eqv.pair_pi_r_wk_eff {A B C : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩) (r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩)
  : pair (l.wk_eff (by simp)) r ;;' pi_r = r := by
  rw [seq, let1_pair, let1_beta_let2_eta]
  simp only [wk1_pi_r]
  rw [pi_r, subst_let2, nil_subst0, let1_beta, subst_let1, subst0_wk0]
  simp [let2_pair, let1_beta, wk0_wk_eff, let1_eta]

theorem Eqv.pair_pi_l_wk_eff {A B C : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩) (r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, ⊥⟩)
  : pair l (r.wk_eff (by simp)) ;;' pi_l = l := by
  rw [seq, let1_pair, let1_beta_let2_eta]
  simp only [wk1_pi_l]
  rw [pi_l, subst_let2, nil_subst0]
  simp [let2_pair, let1_beta, wk0_wk_eff, let1_eta]

@[simp]
theorem Eqv.pair_pi_r {A B C : Ty α} {Γ : Ctx α ε}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩} (hl : l.Pure) (r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩)
  : pair l r ;;' pi_r = r := by have ⟨p, hp⟩ := hl; rw [hp, pair_pi_r_wk_eff]

@[simp]
theorem Eqv.pair_pi_l {A B C : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩) {r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} (hr : r.Pure)
  : pair l r ;;' pi_l = l := by have ⟨p, hp⟩ := hr; rw [hp, pair_pi_l_wk_eff]

theorem Eqv.pair_pi_r_pure {A B C : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩) (r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, ⊥⟩)
  : pair l r ;;' pi_r = r := by simp

theorem Eqv.pair_pi_l_pure {A B C : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩) (r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, ⊥⟩)
  : pair l r ;;' pi_l = l := by simp

@[simp]
theorem Eqv.lunit_pi_r {A : Ty α} {Γ : Ctx α ε}
  : lunit ;;' pi_r = nil (φ := φ) (A := A) (Γ := Γ) (e := e) := by
  simp only [lunit, unit_is_pure, pair_pi_r, nil]

@[simp]
theorem Eqv.runit_pi_l {A : Ty α} {Γ : Ctx α ε}
  : runit ;;' pi_l = nil (φ := φ) (A := A) (Γ := Γ) (e := e) := by
  simp only [runit, unit_is_pure, pair_pi_l, nil]

theorem Eqv.pi_r_lunit {A : Ty α} {Γ : Ctx α ε}
  : pi_r ;;' lunit = nil (φ := φ) (A := Ty.unit.prod A) (Γ := Γ) (e := e) := by
  rw [pi_r, let2_seq, <-nil, nil_seq, lunit_wk1, lunit_wk1, lunit, <-eq_unit, let2_eta]
  exact ⟨var 1 (by simp), rfl⟩

theorem Eqv.pi_l_runit {A : Ty α} {Γ : Ctx α ε}
  : pi_l ;;' runit = nil (φ := φ) (A := A.prod Ty.unit) (Γ := Γ) (e := e) := by
  rw [
    pi_l, let2_seq, runit_wk1, runit_wk1, runit, seq,
    <-wk_eff_var (lo := ⊥) (he := bot_le) (hn := by simp),
    let1_beta, wk1_pair, wk1_var0, wk1_unit, subst_pair, var0_subst0,
    wk_res_eff, wk_eff_var, subst_unit, <-eq_unit, let2_eta
  ]
  exact ⟨var 0 (by simp), rfl⟩

def Eqv.tensor {A A' B B' : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩) (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨A'.prod B', e⟩ := let2 nil (pair l.wk1.wk0 r.wk1.wk1)

theorem Eqv.tensor_nil_nil {A B : Ty α} {Γ : Ctx α ε}
  : tensor (φ := φ) (Γ := Γ) (A := A) (A' := A) (B := B) (B' := B) (e := e) nil nil = nil := by
  simp [tensor, nil, let2_eta]

def Eqv.ltimes {A A' : Ty α} {Γ : Ctx α ε} (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩) (B)
  : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨A'.prod B, e⟩ := tensor l nil

theorem Eqv.ltimes_nil {A B : Ty α} {Γ : Ctx α ε}
  : ltimes (φ := φ) (Γ := Γ) (A := A) (A' := A) (B := B) (e := e) nil = nil := tensor_nil_nil

theorem Eqv.ltimes_seq {A A' B : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩) (r : Eqv φ (⟨A', ⊥⟩::Γ) ⟨B, e⟩)
  : ltimes l B ;;' ltimes r B = ltimes (l ;;' r) B := by
  sorry

def Eqv.rtimes {Γ : Ctx α ε} (A : Ty α) {B B' : Ty α} (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨A.prod B', e⟩ := tensor nil r

theorem Eqv.rtimes_nil {A B : Ty α} {Γ : Ctx α ε}
  : rtimes (φ := φ) (Γ := Γ) (A := A) (B := B) (B' := B) (e := e) nil = nil := tensor_nil_nil

theorem Eqv.rtimes_seq {A B : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩) (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B, e⟩)
  : rtimes A r ;;' rtimes A r = rtimes A (r ;;' r) := by
  sorry

theorem Eqv.ltimes_rtimes {A A' B B' : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩) (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : ltimes l B ;;' rtimes A' r = tensor l r := by
  sorry

theorem Eqv.Pure.left_central {A A' B B' : Ty α} {Γ : Ctx α ε}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩} (hl : l.Pure) (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : ltimes l B ;;' rtimes A' r = rtimes A r ;;' ltimes l B'
  := by sorry

theorem Eqv.Pure.right_central {A A' B B' : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩) {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩} (hr : r.Pure)
  : ltimes l B ;;' rtimes A' r = rtimes A r ;;' ltimes l B'
  := by sorry

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
