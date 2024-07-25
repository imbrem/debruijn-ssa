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

theorem Eqv.vwk_lift_fixpoint {A B : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨A, ⊥⟩::Δ) ((B.coprod A)::L)}
  {ρ : Ctx.InS Γ Δ}
  : r.fixpoint.vwk ρ.slift = (r.vwk ρ.slift).fixpoint := by
  induction r using Quotient.inductionOn
  simp [InS.vwk_lift_fixpoint]

theorem Eqv.vsubst_lift_fixpoint {A B : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨A, ⊥⟩::Δ) ((B.coprod A)::L)}
  {σ : Term.Subst.Eqv φ Γ Δ}
  : r.fixpoint.vsubst (σ.lift (le_refl _)) = (r.vsubst (σ.lift (le_refl _))).fixpoint := by
  induction r using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  simp [InS.vsubst_lift_fixpoint]

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

theorem Eqv.seq_cfg {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (g : Eqv φ (⟨B, ⊥⟩::Γ) (R ++ C::L))
  (G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ C::L))
  : f ;; cfg R g (λi => (G i).vwk1)
  = cfg R
    ((f.lwk sorry ;; g.cast rfl output_reshuffle_helper).cast rfl output_reshuffle_helper.symm)
    (λi => (G i).vwk1)
  := sorry

theorem Eqv.seq_cont {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (g : Eqv φ (⟨B, ⊥⟩::Γ) (C::D::L))
  (h : Eqv φ (⟨C, ⊥⟩::Γ) (C::D::L))
  : f ;; cfg [C] g (Fin.elim1 h.vwk1) = cfg [C] (f.lwk1 ;; g) (Fin.elim1 h.vwk1)
  := by
  induction f using Eqv.arrow_induction with
  | br ℓ a hℓ =>
    cases ℓ with
    | zero =>
      simp only [List.append_eq, List.nil_append, br_zero_eq_ret, wk_res_self, lwk1_ret, ret_seq,
        List.length_singleton, List.get_eq_getElem, List.singleton_append, vwk1_cfg, vsubst_cfg]
      congr
      funext i
      cases i using Fin.elim1
      induction h using Quotient.inductionOn
      induction a using Quotient.inductionOn
      apply Eqv.eq_of_reg_eq
      simp only [Set.mem_setOf_eq, InS.coe_vwk, Ctx.InS.coe_wk1, Fin.isValue, Fin.val_zero,
        List.getElem_cons_zero, InS.coe_vsubst, Term.Subst.InS.coe_lift, Term.InS.coe_subst0,
        Ctx.InS.coe_wk2, Region.vwk_vwk]
      simp only [<-Region.vsubst_fromWk, Region.vsubst_vsubst]
      congr
      funext i
      cases i <;> rfl
    | succ ℓ => simp [cfg_br_ge]
  | let1 a r Ir =>
    apply Eq.symm
    rw [lwk1_let1, let1_seq, cfg_let1, let1_seq]
    congr
    apply Eq.trans (Ir g.vwk1 h.vwk1).symm
    simp only [vwk1_cfg]
    congr
    funext i
    cases i using Fin.elim1
    simp [vwk1_vwk2]
  | let2 a r Ir =>
    sorry
  | case a l r Il Ir => sorry
  | cfg R β G Iβ IG => sorry

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

theorem Eqv.fixpoint_naturality {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  (g : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : fixpoint (f ;; sum g nil) = (fixpoint f) ;; g := sorry

theorem Eqv.fixpoint_dinaturality {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod C)::L))
  (g : Eqv φ (⟨C, ⊥⟩::Γ) ((B.coprod A)::L))
  : fixpoint (f ;; coprod inj_l g) = f ;; coprod nil (fixpoint (g ;; coprod inj_l f)) := sorry

theorem Eqv.fixpoint_codiagonal {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) (((B.coprod A).coprod A)::L))
  : fixpoint (f ;; coprod nil inj_r) = fixpoint (fixpoint f) := sorry

theorem Eqv.fixpoint_uniformity {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L)) (g : Eqv φ (⟨C, ⊥⟩::Γ) ((B.coprod C)::L))
  (h : Eqv φ (⟨C, ⊥⟩::Γ) (A::L)) (hh : h.Pure)
  (hfg : h ;; f = g ;; sum nil h)
  : h ;; (fixpoint f) = fixpoint g := sorry

theorem Eqv.fixpoint_strong_left {X A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  : X ⋊ fixpoint f = fixpoint (X ⋊ f ;; distl_inv) := sorry

end Region

end BinSyntax
