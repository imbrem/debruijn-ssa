import DeBruijnSSA.BinSyntax.Rewrite.Term.Eqv
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Seq

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

theorem Eqv.wk_reassoc {A B C : Ty α} {Γ Δ : Ctx α ε} {ρ : Ctx.InS Γ Δ}
  {a : Eqv φ Δ ⟨((A.prod B).prod C), e⟩}
  : (reassoc a).wk ρ = reassoc (a.wk ρ) := by
  induction a using Quotient.inductionOn; rfl

theorem Eqv.reassoc_wk {A B C : Ty α} {Γ Δ : Ctx α ε} {ρ : Ctx.InS Γ Δ}
  {a : Eqv φ Δ ⟨(A.prod B).prod C, e⟩}
  : reassoc (a.wk ρ) = (reassoc a).wk ρ := wk_reassoc.symm

theorem Eqv.wk0_reassoc {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨(A.prod B).prod C, e⟩}
  : (reassoc a).wk0 (head := head) = reassoc (a.wk0) := wk_reassoc

theorem Eqv.reassoc_wk0 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨(A.prod B).prod C, e⟩}
  : reassoc (a.wk0) = (reassoc a).wk0 (head := head) := reassoc_wk

theorem Eqv.wk1_reassoc {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ (head::Γ) ⟨(A.prod B).prod C, e⟩}
  : (reassoc a).wk1 (inserted := inserted) = reassoc a.wk1 := wk_reassoc

theorem Eqv.reassoc_wk1 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ (head::Γ) ⟨(A.prod B).prod C, e⟩}
  : reassoc a.wk1 = (reassoc a).wk1 (inserted := inserted) := reassoc_wk

theorem Eqv.wk2_reassoc {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ (left::right::Γ) ⟨(A.prod B).prod C, e⟩}
  : (reassoc a).wk2 (inserted := inserted) = reassoc a.wk2 := wk_reassoc

theorem Eqv.reassoc_wk2 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ (left::right::Γ) ⟨(A.prod B).prod C, e⟩}
  : reassoc a.wk2 = (reassoc a).wk2 (inserted := inserted) := reassoc_wk

theorem Eqv.wk_reassoc_inv {A B C : Ty α} {Γ Δ : Ctx α ε} {ρ : Ctx.InS Γ Δ}
  {a : Eqv φ Δ ⟨A.prod (B.prod C), e⟩}
  : (reassoc_inv a).wk ρ = reassoc_inv (a.wk ρ) := by
  induction a using Quotient.inductionOn; rfl

theorem Eqv.reassoc_inv_wk {A B C : Ty α} {Γ Δ : Ctx α ε} {ρ : Ctx.InS Γ Δ}
  {a : Eqv φ Δ ⟨A.prod (B.prod C), e⟩}
  : reassoc_inv (a.wk ρ) = (reassoc_inv a).wk ρ := wk_reassoc_inv.symm

theorem Eqv.wk0_reassoc_inv {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A.prod (B.prod C), e⟩}
  : (reassoc_inv a).wk0 (head := head) = reassoc_inv (a.wk0) := wk_reassoc_inv

theorem Eqv.reassoc_inv_wk0 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A.prod (B.prod C), e⟩}
  : reassoc_inv (a.wk0) = (reassoc_inv a).wk0 (head := head) := reassoc_inv_wk

theorem Eqv.wk1_reassoc_inv {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ (head::Γ) ⟨A.prod (B.prod C), e⟩}
  : (reassoc_inv a).wk1 (inserted := inserted) = reassoc_inv a.wk1 := wk_reassoc_inv

theorem Eqv.reassoc_inv_wk1 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ (head::Γ) ⟨A.prod (B.prod C), e⟩}
  : reassoc_inv a.wk1 = (reassoc_inv a).wk1 (inserted := inserted) := reassoc_inv_wk

theorem Eqv.wk2_reassoc_inv {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ (left::right::Γ) ⟨A.prod (B.prod C), e⟩}
  : (reassoc_inv a).wk2 (inserted := inserted) = reassoc_inv a.wk2 := wk_reassoc_inv

theorem Eqv.reassoc_inv_wk2 {A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ (left::right::Γ) ⟨A.prod (B.prod C), e⟩}
  : reassoc_inv a.wk2 = (reassoc_inv a).wk2 (inserted := inserted) := reassoc_inv_wk

theorem Eqv.seq_reassoc {X Y A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ (⟨X, ⊥⟩::Γ) ⟨Y, e⟩} {b : Eqv φ ((Y, ⊥)::Γ) ⟨(A.prod B).prod C, e⟩}
  : a ;;' reassoc b = reassoc (a ;;' b) := by rw [seq, wk1_reassoc, let1_reassoc]; rfl

theorem Eqv.seq_reassoc_inv {X Y A B C : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ (⟨X, ⊥⟩::Γ) ⟨Y, e⟩} {b : Eqv φ ((Y, ⊥)::Γ) ⟨A.prod (B.prod C), e⟩}
  : a ;;' reassoc_inv b = reassoc_inv (a ;;' b)
  := by rw [seq, wk1_reassoc_inv, let1_reassoc_inv]; rfl

def Eqv.pi_l {A B : Ty α} {Γ : Ctx α ε} : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨A, e⟩
  := let2 nil (var 1 (by simp))

def Eqv.pi_r {A B : Ty α} {Γ : Ctx α ε} : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨B, e⟩
  := let2 nil (var 0 (by simp))

theorem Eqv.seq_pi_l {C A B : Ty α} {Γ : Ctx α ε} (a : Eqv φ (⟨C, ⊥⟩::Γ) ⟨A.prod B, e⟩) :
  a ;;' pi_l = a.let2 (var 1 (by simp)) := by rw [seq, let2_bind]; rfl

theorem Eqv.seq_pi_r {C A B : Ty α} {Γ : Ctx α ε} (a : Eqv φ (⟨C, ⊥⟩::Γ) ⟨A.prod B, e⟩) :
  a ;;' pi_r = a.let2 (var 0 (by simp)) := by rw [seq, let2_bind]; rfl

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
  rw [pi_r, seq_let2, <-nil, nil_seq, lunit_wk1, lunit_wk1, lunit, <-eq_unit, let2_eta]
  exact ⟨var 1 (by simp), rfl⟩

theorem Eqv.pi_l_runit {A : Ty α} {Γ : Ctx α ε}
  : pi_l ;;' runit = nil (φ := φ) (A := A.prod Ty.unit) (Γ := Γ) (e := e) := by
  rw [
    pi_l, seq_let2, runit_wk1, runit_wk1, runit, seq,
    let1_beta_var1, wk1_pair, wk1_var0, wk1_unit, subst_pair, var0_subst0,
    wk_res_eff, wk_eff_var, subst_unit, <-eq_unit, let2_eta
  ]
  exact ⟨var 0 (by simp), rfl⟩

def Eqv.swap {A B : Ty α} {Γ : Ctx α ε} : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨B.prod A, e⟩
  := let2 nil $ pair (var 0 (by simp)) (var 1 (by simp))

-- TODO: wk_lift_swap

theorem Eqv.wk1_swap {A B : Ty α} {Γ : Ctx α ε}
  : (swap : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨B.prod A, e⟩).wk1 (inserted := inserted) = swap := rfl

-- theorem Eqv.wk2_swap {A B : Ty α} {Γ : Ctx α ε}
--   : (swap : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨B.prod A, e⟩).wk2 (inserted := inserted) = swap := rfl

theorem Eqv.seq_swap {C A B : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ (⟨C, ⊥⟩::Γ) ⟨A.prod B, e⟩)
  : a ;;' swap = (let2 a $ pair (var 0 (by simp)) (var 1 (by simp))) := by rw [seq, let2_bind]; rfl

theorem Eqv.swap_swap {A B : Ty α} {Γ : Ctx α ε}
  : swap ;;' swap = nil (φ := φ) (A := A.prod B) (Γ := Γ) (e := e) := by
  rw [
    seq_swap, swap, let2_let2, swap_eta_wk2, swap_eta_wk2, let2_pair, let1_beta_var0,
    subst_let1, wk0_var, var_succ_subst0, let1_beta_var1
  ]
  apply Eq.trans _ let2_eta
  rfl

theorem Eqv.seq_swap_inj {A B C : Ty α} {Γ : Ctx α ε}
  {a b : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B.prod C, e⟩}
  : a ;;' swap = b ;;' swap ↔ a = b := ⟨
    λh => by rw [<-seq_nil (a := a), <-seq_nil (a := b), <-swap_swap]; simp only [seq_assoc, h],
    λh => h ▸ rfl
  ⟩

theorem Eqv.swap_seq_inj {A B C : Ty α} {Γ : Ctx α ε}
  {a b : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨C, e⟩}
  : swap ;;' a = swap ;;' b ↔ a = b := ⟨
    λh => by rw [<-nil_seq (a := a), <-nil_seq (a := b), <-swap_swap]; simp only [<-seq_assoc, h],
    λh => h ▸ rfl
  ⟩

def Eqv.tensor {A A' B B' : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩) (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨A'.prod B', e⟩ := let2 nil (pair l.wk1.wk0 r.wk1.wk1)

theorem Eqv.tensor_nil_nil {A B : Ty α} {Γ : Ctx α ε}
  : tensor (φ := φ) (Γ := Γ) (A := A) (A' := A) (B := B) (B' := B) (e := e) nil nil = nil := by
  simp [tensor, nil, let2_eta]

theorem Eqv.seq_tensor {X A A' B B' : Ty α} {Γ : Ctx α ε}
  {s : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.prod B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩}
  : s ;;' tensor l r = let2 s (pair l.wk1.wk0 r.wk1.wk1) := by rw [
    tensor, seq, wk1_let2, wk1_nil, wk_pair,
    wk0_wk_liftn₂, wk_lift_wk1, wk1_wk_liftn₂, wk_lift_wk1, wk1_wk2, wk1_wk2,
    l.wk1.wk1_wk0, <-r.wk1.wk1_wk2, <-wk2_pair, nil, <-let2_bind
  ]

theorem Eqv.let2_tensor {A A' B B' C : Ty α} {Γ : Ctx α ε}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩}
  {c : Eqv φ (⟨B', ⊥⟩::⟨A', ⊥⟩::⟨A.prod B, ⊥⟩::Γ) ⟨C, e⟩}
  : let2 (tensor l r) c = (let2 nil $ let1 l.wk1.wk0 $ let1 r.wk1.wk1.wk0 $ c.wk2.wk2)
  := by rw [tensor, let2_let2, let2_pair]

def Eqv.ltimes {A A' : Ty α} {Γ : Ctx α ε} (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩) (B)
  : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨A'.prod B, e⟩ := tensor l nil

theorem Eqv.ltimes_nil {A B : Ty α} {Γ : Ctx α ε}
  : ltimes (φ := φ) (Γ := Γ) (A := A) (A' := A) (B := B) (e := e) nil = nil := tensor_nil_nil

theorem Eqv.seq_ltimes {A A' B : Ty α} {Γ : Ctx α ε}
  {s : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.prod B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩}
  : s ;;' ltimes l B = let2 s (pair l.wk1.wk0 nil) := by simp only [ltimes, seq_tensor, wk1_nil]

theorem Eqv.seq_ltimes' {A A' B : Ty α} {Γ : Ctx α ε}
  {s : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.prod B, e⟩} {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩}
  : s ;;' ltimes l B = let2 s (pair l.wk0 nil).wk2 := by rw [seq_ltimes, wk1_wk0, wk2_pair, wk2_nil]

theorem Eqv.let2_ltimes {A A' B C : Ty α} {Γ : Ctx α ε}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩}
  {c : Eqv φ (⟨B, ⊥⟩::⟨A', ⊥⟩::⟨A.prod B, ⊥⟩::Γ) ⟨C, e⟩}
  : let2 (ltimes l B) c = (let2 nil $ let1 l.wk1.wk0 $ let1 (var 1 (by simp)) $ c.wk2.wk2)
  := by rw [ltimes, let2_tensor]; rfl

theorem Eqv.ltimes_ltimes {A₀ A₁ A₂ B : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A₀, ⊥⟩::Γ) ⟨A₁, e⟩) (r : Eqv φ (⟨A₁, ⊥⟩::Γ) ⟨A₂, e⟩)
  : ltimes l B ;;' ltimes r B = ltimes (l ;;' r) B := by
  rw [
    seq_ltimes, let2_ltimes, let1_beta_var1, wk2_pair, wk2_pair, wk2_nil, wk2_nil, subst_pair,
    nil_subst0, wk0_wk2, wk0_wk2, subst0_wk0, ltimes, tensor, wk1_nil, wk1_nil, wk1_seq, wk0_seq,
    wk_eff_var, pair_bind_left (a := _ ;;' _), let1_seq, seq, wk1_pair, wk0_wk1, wk0_nil, wk1_var0,
    <-pair_bind_left
  ]

def Eqv.rtimes {Γ : Ctx α ε} (A : Ty α) {B B' : Ty α} (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨A.prod B', e⟩ := tensor nil r

theorem Eqv.seq_rtimes {A B B' : Ty α} {Γ : Ctx α ε}
  {l : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.prod B, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩}
  : l ;;' rtimes A r = let2 l (pair (var 1 (by simp)) r.wk1.wk1)
  := by rw [rtimes, seq_tensor, wk1_nil, wk0_nil]

theorem Eqv.swap_rtimes {A B B' : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : swap ;;' rtimes A r = ltimes r A ;;' swap := by
  rw [seq_rtimes, swap, let2_let2, seq, let2_pair, let1_beta_var0]
  simp only [wk0_var, Nat.reduceAdd, subst_let1, var_succ_subst0]
  rw [let1_beta_var1]
  simp only [wk2_pair, wk2_var1, List.length_cons, Nat.reduceAdd, Fin.mk_one, List.get_eq_getElem,
    Fin.val_one, List.getElem_cons_succ, List.getElem_cons_zero, subst_pair, subst_lift_var_succ,
    var0_subst0, Fin.zero_eta, Fin.val_zero, wk_res_eff, wk_eff_var, wk0_var, zero_add,
    var_succ_subst0]
  rw [wk1_swap, ltimes, tensor, let1_let2, wk1_swap, wk1_swap]
  apply congrArg
  rw [swap]
  apply Eq.symm
  rw [
    var0_eq_wk2_var0, var1_eq_wk2_var1, <-wk2_pair, <-let2_let1, wk1_nil, wk1_nil, nil, nil,
    let1_eta, let2_pair, wk0_var, let1_beta_var1, subst_pair, var0_subst0, wk_res_var,
    var_succ_subst0, let1_pair_var_1_left, let1_eta
  ]
  apply congrArg
  rw [wk1_wk2, wk1_wk2]
  -- TODO: factor this part out...
  induction r using Quotient.inductionOn
  simp only [wk1_quot, wk0_quot, var, subst0_quot, Subst.Eqv.lift_quot, wk2_quot, subst_quot]
  apply congrArg
  ext
  simp only [Set.mem_setOf_eq, InS.coe_wk0, Term.wk0, InS.coe_wk1, Term.wk1, ← subst_fromWk, ←
    Subst.fromWk_lift, Term.subst_subst, InS.coe_subst, InS.coe_subst0, InS.coe_var, Subst.coe_lift,
    ← Subst.lift_comp]
  congr
  funext k
  cases k <;> rfl

theorem Eqv.swap_rtimes_swap {A B B' : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩) : swap ;;' rtimes A r ;;' swap = ltimes r A
  := by rw [swap_rtimes, <-seq_assoc, swap_swap, seq_nil]

theorem Eqv.swap_ltimes_swap {A B B' : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩) : swap ;;' ltimes l A ;;' swap = rtimes A l
  := by rw [<-seq_assoc, <-swap_rtimes, seq_assoc, swap_swap, nil_seq]

theorem Eqv.swap_ltimes {A B B' : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩) : swap ;;' ltimes l A = rtimes A l ;;' swap := by
  rw [<-seq_swap_inj, swap_ltimes_swap, <-seq_assoc, swap_swap, seq_nil]

theorem Eqv.rtimes_swap {A B B' : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩) : rtimes A r ;;' swap = swap ;;' ltimes r A := by rw [swap_ltimes]

theorem Eqv.ltimes_swap {A B B' : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩) : ltimes l A ;;' swap = swap ;;' rtimes A l := by rw [swap_rtimes]

theorem Eqv.rtimes_nil {A B : Ty α} {Γ : Ctx α ε}
  : rtimes (φ := φ) (Γ := Γ) (A := A) (B := B) (B' := B) (e := e) nil = nil := tensor_nil_nil

theorem Eqv.rtimes_rtimes {A B₀ B₁ B₂ : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨B₀, ⊥⟩::Γ) ⟨B₁, e⟩) (r : Eqv φ (⟨B₁, ⊥⟩::Γ) ⟨B₂, e⟩)
  : rtimes A l ;;' rtimes A r = rtimes A (l ;;' r) := by rw [
    <-swap_ltimes_swap, <-seq_assoc, swap_rtimes, seq_assoc, <-seq_assoc (a := swap), ltimes_ltimes,
    swap_ltimes_swap]

theorem Eqv.ltimes_rtimes {A A' B B' : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩) (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : ltimes l B ;;' rtimes A' r = tensor l r := by
  rw [
    seq_rtimes, ltimes, tensor, let2_let2, let2_pair, wk1_nil, wk1_nil, wk0_nil, let1_beta_var1,
    wk2_pair, wk2_pair, wk2_var1, wk2_var1, subst_pair, var_succ_subst0, tensor,
    pair_bind_left (a := l.wk1.wk0)
  ]
  congr
  -- TODO: _really_ need to factor this...
  induction r using Quotient.inductionOn
  simp only [var, subst0_quot, wk2, wk1, wk_quot, subst_quot, wk0]
  congr
  ext
  simp only [Set.mem_setOf_eq, InS.coe_subst, InS.coe_subst0, InS.coe_var, InS.coe_wk,
    Ctx.InS.coe_wk2, Ctx.InS.coe_wk1, ← subst_fromWk, Term.subst_subst, Ctx.InS.coe_wk0]
  congr
  funext k
  cases k <;> rfl

theorem Eqv.Pure.left_central {A A' B B' : Ty α} {Γ : Ctx α ε}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩} (hl : l.Pure) (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : ltimes l B ;;' rtimes A' r = rtimes A r ;;' ltimes l B':= by
  rw [ltimes_rtimes, seq_ltimes, tensor, rtimes, tensor, let2_let2]
  apply congrArg
  rw [let2_pair]
  simp only [wk1_nil, wk0_nil, wk2_pair, wk2_nil, let1_beta_var1, subst_let1, subst0_wk0,
    subst_pair, subst_lift_nil]
  apply Eq.symm
  rw [pair_bind_left]
  apply Eq.symm
  rw [pair_bind_swap_left]
  -- TODO: this REALLY needs to be factored out...
  congr
  induction l using Quotient.inductionOn
  apply eq_of_term_eq
  simp only [Set.mem_setOf_eq, InS.coe_wk, Ctx.InS.coe_wk0, Ctx.InS.coe_wk1, ← subst_fromWk,
    Term.subst_subst, InS.coe_subst, Subst.coe_lift, InS.coe_subst0, InS.coe_var, Ctx.InS.coe_wk2]
  congr
  funext k
  cases k <;> rfl
  sorry -- TODO: obviously, if something is pure so are its weakenings

theorem Eqv.Pure.right_central {A A' B B' : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩) {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩} (hr : r.Pure)
  : ltimes l B ;;' rtimes A' r = rtimes A r ;;' ltimes l B'
  := by
  apply Eq.symm
  rw [
    <-swap_ltimes_swap, <-seq_assoc, swap_ltimes (l := l), seq_assoc, <-seq_assoc (a := swap),
    hr.left_central, seq_assoc, swap_rtimes, <-seq_assoc, ltimes_swap (l := r), seq_assoc,
    <-seq_assoc (c := swap), swap_swap, seq_nil
  ]

theorem Eqv.tensor_seq_of_comm {A₀ A₁ A₂ B₀ B₁ B₂ : Ty α} {Γ : Ctx α ε}
  {l : Eqv φ (⟨A₀, ⊥⟩::Γ) ⟨A₁, e⟩} {r : Eqv φ (⟨B₀, ⊥⟩::Γ) ⟨B₁, e⟩}
  {l' : Eqv φ (⟨A₁, ⊥⟩::Γ) ⟨A₂, e⟩} {r' : Eqv φ (⟨B₁, ⊥⟩::Γ) ⟨B₂, e⟩}
  (h : rtimes _ r ;;' ltimes l' _ = ltimes l' _ ;;' rtimes _ r)
  : tensor l r ;;' tensor l' r' = tensor (l ;;' l') (r ;;' r') := by
  simp only [<-ltimes_rtimes]
  rw [<-seq_assoc, seq_assoc (a := rtimes A₁ r), h, <-ltimes_ltimes, <-rtimes_rtimes]
  simp only [seq_assoc]

-- TODO: tensor_seq (pure only)

def Eqv.split {A : Ty α} {Γ : Ctx α ε} : Eqv (φ := φ) (⟨A, ⊥⟩::Γ) ⟨A.prod A, e⟩
  := let1 nil (pair nil nil)

-- TODO: split_seq (pure only)

def Eqv.assoc {A B C : Ty α} {Γ : Ctx α ε}
  : Eqv (φ := φ) (⟨(A.prod B).prod C, ⊥⟩::Γ) ⟨A.prod (B.prod C), e⟩ := nil.reassoc

def Eqv.assoc_inv {A B C : Ty α} {Γ : Ctx α ε}
  : Eqv (φ := φ) (⟨A.prod (B.prod C), ⊥⟩::Γ) ⟨(A.prod B).prod C, e⟩ := nil.reassoc_inv

theorem Eqv.seq_prod_assoc {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨(A.prod B).prod C, e⟩)
  : r ;;' assoc = r.reassoc := by rw [assoc, seq_reassoc, seq_nil]

theorem Eqv.seq_assoc_inv {A B C : Ty α} {Γ : Ctx α ε}
  (r : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A.prod (B.prod C), e⟩)
  : r ;;' assoc_inv = r.reassoc_inv := by rw [assoc_inv, seq_reassoc_inv, seq_nil]

@[simp]
theorem Eqv.wk_eff_assoc {A B C : Ty α} {Γ : Ctx α ε} {h : lo ≤ hi}
  : (assoc (φ := φ) (Γ := Γ) (A := A) (B := B) (C := C) (e := lo)).wk_eff h = assoc := rfl

@[simp]
theorem Eqv.wk_eff_assoc_inv {A B C : Ty α} {Γ : Ctx α ε} {h : lo ≤ hi}
  : (assoc_inv (φ := φ) (Γ := Γ) (A := A) (B := B) (C := C) (e := lo)).wk_eff h = assoc_inv := rfl

theorem Eqv.assoc_pure  {A B C : Ty α} {Γ : Ctx α ε}
  : assoc (φ := φ) (Γ := Γ) (A := A) (B := B) (C := C) (e := e) = assoc.wk_eff bot_le
  := rfl

theorem Eqv.assoc_inv_pure {A B C : Ty α} {Γ : Ctx α ε}
  : assoc_inv (φ := φ) (Γ := Γ) (A := A) (B := B) (C := C) (e := e) = assoc_inv.wk_eff bot_le
  := rfl

@[simp]
theorem Eqv.Pure.assoc {A B C : Ty α} {Γ : Ctx α ε}
  : (assoc (φ := φ) (Γ := Γ) (A := A) (B := B) (C := C) (e := e)).Pure := ⟨Eqv.assoc, rfl⟩

@[simp]
theorem Eqv.Pure.assoc_inv {A B C : Ty α} {Γ : Ctx α ε}
  : (assoc_inv (φ := φ) (Γ := Γ) (A := A) (B := B) (C := C) (e := e)).Pure := ⟨Eqv.assoc_inv, rfl⟩

theorem Eqv.assoc_assoc_inv {A B C : Ty α} {Γ : Ctx α ε}
  : assoc (φ := φ) (Γ := Γ) (A := A) (B := B) (C := C) (e := e) ;;' assoc_inv = nil :=  by
  rw [seq_assoc_inv, assoc, reassoc_inv_reassoc]

theorem Eqv.assoc_inv_assoc {A B C : Ty α} {Γ : Ctx α ε}
  : assoc_inv (φ := φ) (Γ := Γ) (A := A) (B := B) (C := C) (e := e) ;;' assoc = nil := by
  rw [seq_prod_assoc, assoc_inv, reassoc_reassoc_inv]
