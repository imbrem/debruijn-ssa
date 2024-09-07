import DeBruijnSSA.BinSyntax.Rewrite.Region.LSubst
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Seq
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Product
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Sum
import DeBruijnSSA.BinSyntax.Typing.Region.Compose

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

open Term.Eqv

def Eqv.distl {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨(A.prod B).coprod (A.prod C), ⊥⟩::Γ) (A.prod (B.coprod C)::L) :=
  coprod (A ⋊ inj_l) (A ⋊ inj_r)

def Eqv.distl_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨A.prod (B.coprod C), ⊥⟩::Γ) ((A.prod B).coprod (A.prod C)::L) :=
  let2 (var 0 Ctx.Var.shead) $
  case (var 0 Ctx.Var.shead)
    (ret $ inl (pair (var 2 (by simp)) (var 0 Ctx.Var.shead)))
    (ret $ inr (pair (var 2 (by simp)) (var 0 Ctx.Var.shead)))

theorem Eqv.distl_inv_coprod {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : distl_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)
  = (let2 (var 0 Ctx.Var.shead) $
    coprod
      (ret $ inl (pair (var 1 (by simp)) (var 0 Ctx.Var.shead)))
      (ret $ inr (pair (var 1 (by simp)) (var 0 Ctx.Var.shead)))) := rfl

theorem Eqv.vwk_slift_distl_inv {A B C : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {ρ : Ctx.InS Γ Δ}
  : distl_inv.vwk ρ.slift = distl_inv (φ := φ) (A := A) (B := B) (C := C) (L := L) := rfl

theorem Eqv.vwk1_distl_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (distl_inv (Γ := Γ)).vwk1 (inserted := inserted)
  = distl_inv (φ := φ) (A := A) (B := B) (C := C) (L := L) := rfl

theorem Eqv.vsubst_lift_distl_inv {A B C : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {ρ : Term.Subst.Eqv φ Γ Δ}
  : distl_inv.vsubst (ρ.lift (le_refl _))
  = distl_inv (φ := φ) (A := A) (B := B) (C := C) (L := L)
  := by induction ρ using Quotient.inductionOn; rfl

theorem Eqv.let2_eta_seq_distl_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : ret (φ := φ) ((var 1 Ctx.Var.shead.step).pair (var 0 Ctx.Var.shead))
    ;; distl_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := _::Γ) (L := L)
  = coprod
      (ret $ inl (pair (var 1 (by simp)) (var 0 Ctx.Var.shead)))
      (ret $ inr (pair (var 1 (by simp)) (var 0 Ctx.Var.shead))) := by
  rw [
    ret_seq, vwk1_distl_inv, distl_inv, vsubst_let2, var0_subst0, wk_res_self, let2_pair,
    let1_beta, let1_beta
  ]
  rfl

theorem Eqv.Pure.distl {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (distl (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).Pure := sorry

theorem Eqv.Pure.distl_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (distl_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).Pure := sorry

-- TODO: dist isomorphism

-- TODO: "naturality"

def Eqv.left_exit {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) (B::A::L) :=
  case (var 0 Ctx.Var.shead)
    (br 1 (var 0 (by simp)) ⟨by simp, le_refl _⟩)
    (ret (var 0 (by simp)))

theorem Eqv.left_exit_def {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : left_exit (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L) = ⟦InS.left_exit⟧ := rfl

@[simp]
theorem Eqv.vwk1_left_exit {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (left_exit (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L)).vwk1 (inserted := inserted) = left_exit
  := rfl

@[simp]
theorem Eqv.vwk2_left_exit {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (left_exit (φ := φ) (A := A) (B := B) (Γ := (X::Γ)) (L := L)).vwk2 (inserted := inserted)
  = left_exit
  := rfl

theorem Eqv.left_exit_eq_coprod {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : left_exit (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L) =
    coprod (br 1 (var 0 (by simp)) ⟨by simp, le_refl _⟩) (ret (var 0 (by simp)))
  := rfl

theorem Eqv.lwk1_sum_seq_left_exit {A B A' B' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Eqv φ (⟨A, ⊥⟩::Γ) (A'::L)} {g : Eqv φ (⟨B, ⊥⟩::Γ) (B'::L)}
  : (sum f g).lwk1 ;; left_exit
  = coprod (f.lwk1 ;; (br 1 (var 0 (by simp)) ⟨by simp, le_refl _⟩)) g.lwk1
  := by rw [left_exit_eq_coprod, lwk1_sum, sum_seq_coprod, ret_var_zero, seq_nil]

theorem Eqv.lwk1_sum_seq_left_exit' {A B A' B' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Eqv φ (⟨A, ⊥⟩::Γ) (A'::L)} {g : Eqv φ (⟨B, ⊥⟩::Γ) (B'::L)}
  : (sum f g).lwk1 ;; left_exit
  = case (Term.Eqv.var 0 Ctx.Var.shead)
    (f.vwk1.lwk1 ;; (br 1 (var 0 (by simp)) ⟨by simp, le_refl _⟩))
    g.vwk1.lwk1 := by
  rw [lwk1_sum_seq_left_exit, coprod, vwk1_seq, vwk1_lwk1, vwk1_br, Term.Eqv.wk1_var0, vwk1_lwk1]

def Eqv.fixpoint {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  : Eqv φ (⟨A, ⊥⟩::Γ) (B::L) := cfg [A] nil (Fin.elim1 (f.vwk1.lwk1 ;; left_exit))

@[simp]
theorem Eqv.fixpoint_quot {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : InS φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  : fixpoint ⟦f⟧ = ⟦f.fixpoint⟧ := by
  simp only [fixpoint, nil, List.append_eq, List.nil_append, List.length_singleton,
    List.get_eq_getElem, List.singleton_append, Fin.zero_eta, Fin.isValue, Fin.val_zero,
    List.getElem_cons_zero, vwk1_quot, lwk1_quot, left_exit_def, seq_quot]
  apply Eqv.cfg_eq_quot rfl
  intro i
  cases i using Fin.elim1; rfl

theorem Eqv.fixpoint_eq_vwk1 {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L)}
  : f.fixpoint = cfg [A] nil (Fin.elim1 ((f.lwk1 ;; left_exit).vwk1))
  := by rw [vwk1_seq, vwk1_left_exit, vwk1_lwk1]; rfl

theorem Eqv.vwk_lift_fixpoint {A B : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨A, ⊥⟩::Δ) ((B.coprod A)::L)}
  {ρ : Ctx.InS Γ Δ}
  : r.fixpoint.vwk ρ.slift = (r.vwk ρ.slift).fixpoint := by
  induction r using Quotient.inductionOn
  simp [InS.vwk_lift_fixpoint]

theorem Eqv.vwk1_fixpoint {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L)}
  : r.fixpoint.vwk1 (inserted := inserted) = (r.vwk1).fixpoint := by
  simp only [vwk1, <-Ctx.InS.lift_wk0, vwk_lift_fixpoint]

theorem Eqv.lwk_lift_fixpoint {A B : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
  {r : Eqv φ (⟨A, ⊥⟩::Δ) ((B.coprod A)::L)}
  {ρ : L.InS K}
  : r.fixpoint.lwk ρ.slift = (r.lwk ρ.slift).fixpoint := by
  induction r using Quotient.inductionOn
  --simp [InS.lwk_lift_fixpoint]
  sorry

theorem Eqv.lwk1_fixpoint {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L)}
  : r.fixpoint.lwk1 (inserted := inserted) = (r.lwk1).fixpoint := sorry

theorem Eqv.vsubst_lift_fixpoint {A B : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨A, ⊥⟩::Δ) ((B.coprod A)::L)}
  {σ : Term.Subst.Eqv φ Γ Δ}
  : r.fixpoint.vsubst (σ.lift (le_refl _)) = (r.vsubst (σ.lift (le_refl _))).fixpoint := by
  induction r using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  simp [InS.vsubst_lift_fixpoint]

theorem Eqv.lsubst_fixpoint_seq_helper {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L)} {σ : Subst.Eqv φ (⟨A, ⊥⟩::Γ) (B::L) K}
  : f.fixpoint.lsubst σ
  = cfg [A] nil (Fin.elim1 ((f.vwk1.lwk1 ;; left_exit).lsubst σ.slift.vlift)) := by
  rw [fixpoint, lsubst_cfg]
  congr
  · simp
  · funext i
    cases i using Fin.elim1
    simp

theorem Eqv.lsubst_fixpoint {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L)} {σ : Subst.Eqv φ (⟨A, ⊥⟩::Γ) (B::L) K}
  : f.fixpoint.lsubst σ
  = cfg [A] nil (Fin.elim1 ((f.vwk1.lwk1.lsubst σ.slift.vlift ;; left_exit.lsubst σ.slift.vlift)))
  := by rw [lsubst_fixpoint_seq_helper, lsubst_vlift_slift_seq]

theorem Eqv.fixpoint_iter_cfg {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  : fixpoint f = cfg [A] (f.lwk1 ;; left_exit) (Fin.elim1 (f.vwk1.lwk1 ;; left_exit)) := by
  rw [fixpoint, <-ret_nil, ret, cfg_br_lt (hℓ' := by simp)]
  congr
  simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.zero_eq, Fin.zero_eta, Fin.isValue, List.get_eq_getElem, Fin.val_zero,
    List.getElem_cons_zero, List.append_eq, Fin.elim1_zero, vwk_id_eq, let1_beta]
  rw [lwk1_vwk1, seq, vsubst_lsubst, seq]
  congr
  · rw [vsubst_alpha0]
    rfl
  · induction f using Quotient.inductionOn
    simp only [Term.Eqv.nil, var, subst0_quot, lwk1_quot, vwk1_quot, vsubst_quot]
    apply congrArg
    ext
    simp only [Set.mem_setOf_eq, InS.coe_vsubst, Term.InS.coe_subst0, Term.InS.coe_var,
      InS.coe_vwk1]
    rw [Region.vwk1, <-Region.vsubst_fromWk, Region.vsubst_vsubst]
    apply Eq.trans _ (Region.vsubst_id _)
    congr
    funext k
    cases k <;> rfl

theorem Eqv.ret_var_zero_eq_nil_vwk1 {A : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : ret (var 0 (by simp)) = (nil (φ := φ) (ty := A) (rest := Γ) (targets := L)).vwk1 (inserted := X)
  := rfl

theorem Eqv.fixpoint_iter {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  : fixpoint f = f ;; coprod nil (fixpoint f) := by
  apply Eq.trans f.fixpoint_iter_cfg
  rw [lwk1_vwk1, <-vwk1_left_exit]
  simp only [<-vwk1_seq (left := f.lwk1) (right := left_exit)]
  rw [<-seq_cont]
  congr
  conv =>
    lhs
    lhs
    rw [left_exit]
  rw [cfg_case, cfg_br_ge (ℓ := 1) (hℓ' := by simp)]
  simp only [List.length_singleton, Nat.sub_self, coprod]
  congr
  rw [fixpoint, vwk1_cfg]
  congr
  funext i
  cases i using Fin.elim1 with
  | zero => simp only [
      Fin.elim1_zero, vwk1_seq, vwk1_left_exit, vwk2_seq, vwk2_left_exit, lwk1_vwk1, vwk1_vwk2]

theorem Eqv.fixpoint_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  (g : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : (fixpoint f) ;; g = fixpoint (f ;; sum g nil) := by
  rw [seq, lsubst_fixpoint, fixpoint]
  apply congrArg
  apply congrArg
  rw [vwk1_seq, lwk1_seq, seq_assoc]
  congr 1
  · simp only [lwk1, <-lsubst_toSubst, lsubst_lsubst]
    induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    apply Eqv.eq_of_reg_eq
    simp only [
      InS.coe_lsubst, Subst.InS.coe_comp, Subst.InS.coe_vlift, Subst.InS.coe_slift, InS.coe_alpha0,
      InS.coe_vwk, Ctx.InS.coe_wk1, LCtx.InS.coe_toSubst, LCtx.InS.coe_wk1
    ]
    congr
    funext k
    cases k <;> rfl
  · rw [
      vwk1_sum, lwk1_sum_seq_left_exit, coprod, vwk1_seq, nil_vwk1, nil_lwk1, nil_vwk1, vwk1_br,
      wk1_var0, left_exit, lsubst_case
    ]
    induction g using Quotient.inductionOn
    congr 1
    apply Eqv.eq_of_reg_eq
    simp only [InS.lsubst_br, InS.coe_vsubst, Term.InS.coe_subst0, Term.InS.coe_var, InS.coe_vwk_id,
      Subst.InS.coe_get, Subst.InS.coe_vlift, Subst.InS.coe_slift, InS.coe_alpha0, InS.coe_vwk,
      Ctx.InS.coe_wk1, InS.vwk_br, Term.InS.wk_var, Nat.liftWk_zero, InS.coe_lsubst, InS.coe_br,
      InS.coe_lwk, LCtx.InS.coe_wk1, Region.vwk_lwk, Region.vwk_vwk, Region.Subst.vlift,
      Region.Subst.lift, Function.comp_apply, Region.vwk1_lwk, Region.vsubst_lwk, Region.alpha,
      Function.update_same]
    simp only [<-Region.lsubst_fromLwk, Region.vwk1, Region.vwk_vwk, Region.lsubst_lsubst]
    simp only [<-Region.vsubst_fromWk, Region.vsubst_vsubst]
    congr
    funext k
    cases k <;> rfl
    funext k
    cases k <;> rfl

theorem Eqv.fixpoint_naturality {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  (g : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : fixpoint (f ;; sum g nil) = (fixpoint f) ;; g := by rw [fixpoint_seq]

theorem Eqv.fixpoint_codiagonal {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) (((B.coprod A).coprod A)::L))
  : fixpoint (fixpoint f) = fixpoint (f ;; coprod nil inj_r) := by
  rw [
    fixpoint, vwk1_fixpoint, lwk1_fixpoint, fixpoint_seq, fixpoint_eq_vwk1,
  ]
  apply Eq.trans codiagonal
  rw [fixpoint]
  congr
  apply congrArg
  rw [
    lwk1_seq, seq_assoc, lwk1_sum_seq_left_exit, left_exit_eq_coprod, lwk1_coprod, coprod_seq,
    nil_lwk1, lwk1_br_succ, br_succ_seq, lwk1_ret, ret_seq, vwk1_br, vsubst_br,
    subst0_var0_wk1, vwk1_seq, vwk1_coprod, nil_vwk1, vwk1_inj_r, lwk1_seq, lwk1_coprod,
    nil_lwk1, lwk1_inj_r, seq_assoc, coprod_seq, inj_r_coprod
  ]
  simp only [Fin.isValue, List.get_eq_getElem, List.length_singleton, Fin.val_zero,
    List.getElem_cons_zero, List.singleton_append, List.append_eq, List.nil_append, Nat.zero_eq,
    List.getElem_cons_succ, List.length_cons, Nat.reduceAdd, nil_seq]
  induction f using Quotient.inductionOn
  apply Eqv.eq_of_reg_eq
  simp only [Set.mem_setOf_eq, InS.vwk_br, Term.InS.wk_var, Ctx.InS.coe_wk1, Nat.liftWk_zero,
    InS.vwk_case, Ctx.InS.lift_wk1, Ctx.InS.coe_wk2, Ctx.InS.coe_lift, InS.coe_lsubst,
    InS.coe_lsubst0, InS.coe_nil, InS.coe_alpha0, InS.coe_case, Term.InS.coe_var, InS.coe_br,
    InS.coe_vwk, Region.vwk, Term.wk, InS.coe_lwk, LCtx.InS.coe_wk1, Region.lwk_lwk]
  simp only [<-Region.lsubst_fromLwk, Region.lsubst_lsubst]
  congr
  funext k
  cases k <;> rfl

theorem Eqv.seq_fixpoint_eq_cfg {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (h : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  (f : Eqv φ (⟨B, ⊥⟩::Γ) ((C.coprod B)::L))
  : h ;; fixpoint f = cfg [B] h.lwk1 (Fin.elim1 (f.lwk1.vwk1 ;; left_exit)) := by rw [
    fixpoint, <-vwk1_left_exit, lwk1_vwk1, <-vwk1_seq, seq_cont, seq_nil, vwk1_seq, vwk1_left_exit]

theorem Eqv.seq_fixpoint_eq_wrseq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (h : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  (f : Eqv φ (⟨B, ⊥⟩::Γ) ((C.coprod B)::L))
  : h ;; fixpoint f = cfg [B] (nil.wrseq h.lwk1.vwk1) (Fin.elim1 (f.lwk1.vwk1 ;; left_exit)) := by
  rw [seq_fixpoint_eq_cfg, <-wseq_eq_wrseq, wseq_eq_seq, nil_seq]

theorem Eqv.fixpoint_uniformity {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L)) (g : Eqv φ (⟨C, ⊥⟩::Γ) ((B.coprod C)::L))
  (h : Eqv φ (⟨C, ⊥⟩::Γ) (A::L)) (hh : h.Pure)
  (hfg : h ;; f = g ;; sum nil h)
  : h ;; (fixpoint f) = fixpoint g := by
  rw [seq_fixpoint_eq_wrseq, fixpoint]
  have ⟨e, he⟩ := hh
  cases he
  rw [lwk1_ret, vwk1_ret]
  apply uniform
  rw [
    <-seq_assoc, <-lwk1_ret, vwk1_lwk1, <-lwk1_seq, <-vwk1_ret, <-vwk1_seq, hfg, vwk1_seq, lwk1_seq,
    seq_assoc, seq_assoc
  ]
  congr 1
  simp only [vwk1_ret, lwk1_ret, vwk1_sum, lwk1_sum, nil_vwk1, nil_lwk1]
  simp only [
    left_exit_eq_coprod, sum_seq_coprod, nil_seq, ret_var_zero, seq_nil, coprod_seq,
    br_succ_seq
  ]

theorem Eqv.pi_r_fixpoint_uniform_inner {X A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L)} : pi_r ;; f = X ⋊ f ;; distl_inv ;; sum pi_r pi_r := by
  simp only [rtimes, let2_seq, vwk1_distl_inv, vwk1_sum, vwk1_pi_r]
  rw [distl_inv_coprod, seq_assoc, let2_seq]
  simp only [vwk1_sum, vwk1_seq, vwk1_pi_r, nil_vwk1, nil_seq, seq_nil]
  rw [
    coprod_seq, <-ret_seq_inj_l, seq_assoc, seq_assoc, inj_l_seq_sum, <-ret_seq_inj_r, seq_assoc,
    inj_r_seq_sum, <-seq_assoc, <-seq_assoc, <-seq_assoc, ret_pair_pi_r, ret_pair_pi_r,
    <-sum, ret_var_zero, ret_var_zero, sum_nil, <-ret_var_zero, <-pi_r, seq_assoc,
    ret_pair_pi_r, ret_var_zero, seq_nil
  ]
  induction f using Quotient.inductionOn
  apply Eqv.eq_of_reg_eq
  simp only [Set.mem_setOf_eq, InS.lsubst_let2, InS.lsubst_br, List.length_cons, Fin.zero_eta,
    List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, InS.coe_let2, Term.InS.coe_var,
    InS.coe_vsubst, Term.InS.coe_subst0, InS.coe_vwk_id, Subst.InS.coe_get, Subst.InS.coe_vliftn₂,
    Subst.vliftn, InS.coe_alpha0, alpha, InS.coe_vwk, Ctx.InS.coe_wk1, Function.comp_apply,
    Function.update_same, let2.injEq, true_and]
  simp only [<-Region.vsubst_fromWk, Region.vsubst_vsubst]
  congr
  funext k
  cases k <;> rfl

theorem Eqv.pi_r_fixpoint {X A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L)}
  : pi_r ;; fixpoint f = fixpoint (X ⋊ f ;; distl_inv) ;; pi_r := by
  rw [<-fixpoint_naturality]
  apply fixpoint_uniformity
  · simp
  · rw [seq_assoc, seq_assoc, sum_seq_sum]
    simp [pi_r_fixpoint_uniform_inner, seq_assoc]

theorem Eqv.ret_eta_fixpoint_uniform_inner {X A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Eqv φ (⟨A, ⊥⟩::⟨X, ⊥⟩::Γ) ((B.coprod A)::L)}
  : ret ((Term.Eqv.var 1 Ctx.Var.shead.step).pair (Term.Eqv.var 0 Ctx.Var.shead))
    ;; (X ⋊ f ;; distl_inv)
  = f ;; sum
    (ret ((Term.Eqv.var 1 Ctx.Var.shead.step).pair (Term.Eqv.var 0 Ctx.Var.shead)))
    (ret ((Term.Eqv.var 1 Ctx.Var.shead.step).pair (Term.Eqv.var 0 Ctx.Var.shead))) := by
  rw [
    ret_seq, vwk1_seq, vwk1_distl_inv, vwk1_rtimes, rtimes, let2_seq, vsubst_let2,
    var0_subst0, wk_res_self, <-Term.Subst.Eqv.lift_lift, vsubst_lift_seq, vsubst_lift_seq
  ]
  simp only [
    vsubst_br, subst_pair, subst_lift_var_succ, subst_lift_var_zero, wk0_var, zero_add,
    vwk1_distl_inv, vsubst_lift_distl_inv
  ]
  rw [
    <-ret, seq_assoc, let2_eta_seq_distl_inv, <-ret_seq_inj_l, <-ret_seq_inj_r, <-sum,
    let2_pair, let1_beta, let1_beta, wk_var
  ]
  simp only [Nat.succ_eq_add_one, zero_add, vsubst_vsubst, seq, vsubst_lsubst]
  congr
  · simp only [var, subst0_quot, sum, coprod, pair_quot, br_quot, inj_l, inl_quot, seq_quot,
    vwk1_quot, inj_r, inr_quot, case_quot, alpha0_quot, Subst.Eqv.vsubst_quot]
    apply congrArg
    ext k; cases k <;> rfl
  · induction f using Quotient.inductionOn
    apply Eqv.eq_of_reg_eq
    simp only [InS.coe_vsubst, Term.Subst.InS.coe_comp, Term.InS.coe_subst0,
      Term.InS.coe_var, Term.Subst.InS.coe_lift, Term.InS.coe_pair, InS.coe_vwk, Ctx.InS.coe_wk1,
      <-Region.vsubst_fromWk, Region.vsubst_vsubst]
    rw [Region.vsubst_id']
    funext k; cases k <;> rfl

theorem Eqv.ret_eta_fixpoint {X A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Eqv φ (⟨A, ⊥⟩::⟨X, ⊥⟩::Γ) ((B.coprod A)::L)}
  : ret ((Term.Eqv.var 1 Ctx.Var.shead.step).pair (Term.Eqv.var 0 Ctx.Var.shead))
    ;; fixpoint (X ⋊ f ;; distl_inv)
  = fixpoint f ;;  ret ((Term.Eqv.var 1 Ctx.Var.shead.step).pair (Term.Eqv.var 0 Ctx.Var.shead))
  := by
  rw [<-fixpoint_naturality]
  apply fixpoint_uniformity
  · exact ⟨_, rfl⟩
  · rw [seq_assoc, sum_seq_sum, nil_seq, seq_nil, ret_eta_fixpoint_uniform_inner]

theorem Eqv.fixpoint_strong_left {X A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  : X ⋊ fixpoint f = fixpoint (X ⋊ f ;; distl_inv) := by
  apply Eq.trans _ let2_eta_seq
  simp only [vwk1_fixpoint, vwk1_seq, vwk1_distl_inv, vwk1_rtimes]
  rw [ret_eta_fixpoint]
  simp only [<-vwk1_fixpoint]
  rfl

-- TODO: this is derivable, probably: see Proposition 16 in Unifying Guarded and Unguarded Iteration
-- by Goncharov et al
theorem Eqv.fixpoint_dinaturality_seq_cfg {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod C)::L))
  (g : Eqv φ (⟨C, ⊥⟩::Γ) ((B.coprod A)::L))
  : fixpoint (f ;; coprod inj_l g)
  = cfg [A] (f.lwk1 ;; (inj_l.coprod g.lwk1 ;; left_exit))
            (Fin.elim1 (f.lwk1 ;; (inj_l.coprod g.lwk1 ;; left_exit)).vwk1) := by
  rw [fixpoint_iter_cfg]
  simp only [
    lwk1_seq, vwk1_seq, lwk1_coprod, vwk1_coprod, vwk1_inj_l, lwk1_inj_l, lwk1_vwk1,
    seq_assoc
  ]
  rfl

-- theorem Eqv.fixpoint_dinaturality_left_loop {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
--   (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod C)::L))
--   (g : Eqv φ (⟨C, ⊥⟩::Γ) ((B.coprod A)::L))
--   : fixpoint (f ;; coprod inj_l g)
--   = cfg [A] f.lwk1
--             (Fin.elim1 (f.lwk1 ;; (inj_l.coprod g.lwk1 ;; left_exit)).vwk1) := by
--   sorry

-- theorem Eqv.fixpoint_dinaturality {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
--   (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod C)::L))
--   (g : Eqv φ (⟨C, ⊥⟩::Γ) ((B.coprod A)::L))
--   : fixpoint (f ;; coprod inj_l g) = f ;; coprod nil (fixpoint (g ;; coprod inj_l f))
--   := by sorry

end Region

end BinSyntax
