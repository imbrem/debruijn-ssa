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

def Eqv.control {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) (B::A::L) :=
  case (var 0 Ctx.Var.shead)
    (br 1 (var 0 (by simp)) ⟨by simp, le_refl _⟩)
    (ret (var 0 (by simp)))

@[simp]
theorem Eqv.vwk1_control {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (control (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L)).vwk1 (inserted := inserted) = control
  := rfl

@[simp]
theorem Eqv.vwk2_control {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (control (φ := φ) (A := A) (B := B) (Γ := (X::Γ)) (L := L)).vwk2 (inserted := inserted)
  = control
  := rfl

def Eqv.fixpoint {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  : Eqv φ (⟨A, ⊥⟩::Γ) (B::L) := cfg [A] nil (λ| ⟨0, _⟩ => f.vwk1.lwk1 ;; control)

theorem Eqv.fixpoint_iter_cfg {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  : fixpoint f = cfg [A] (f.lwk1 ;; control) (λ| ⟨0, _⟩ => f.vwk1.lwk1 ;; control) := by
  rw [fixpoint, <-ret_nil, ret, cfg_br_lt (hℓ' := by simp)]
  congr
  simp only [List.singleton_append, List.length_singleton, Nat.zero_eq, Fin.zero_eta, Fin.isValue,
    List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, List.append_eq, List.nil_append,
    vwk_id_eq, let1_beta]
  rw [lwk1_vwk1, seq, vsubst_lsubst, seq]
  congr
  . rw [vsubst_alpha0]
    rfl
  . induction f using Quotient.inductionOn
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

theorem Eqv.seq_cont {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (g : Eqv φ (⟨B, ⊥⟩::Γ) (C::D::L))
  (h : Eqv φ (⟨C, ⊥⟩::Γ) (C::D::L))
  : cfg [C] (f.lwk1 ;; g) (λ⟨0, _⟩ => h.vwk1) = f ;; cfg [C] g (λ⟨0, _⟩ => h.vwk1)
  := sorry

theorem Eqv.ret_var_zero_eq_nil_vwk1 {A : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : ret (var 0 (by simp)) = (nil (φ := φ) (ty := A) (rest := Γ) (targets := L)).vwk1 (inserted := X)
  := rfl

theorem Eqv.fixpoint_iter {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  : fixpoint f = f ;; coprod nil (fixpoint f) := by
  apply Eq.trans f.fixpoint_iter_cfg
  rw [lwk1_vwk1, <-vwk1_control]
  simp only [<-vwk1_seq (left := f.lwk1) (right := control)]
  rw [seq_cont]
  congr
  conv =>
    lhs
    lhs
    rw [control]
  rw [cfg_case, cfg_br_ge (ℓ := 1) (hℓ' := by simp)]
  simp only [List.length_singleton, Nat.sub_self, coprod]
  congr
  rw [fixpoint, vwk1_cfg]
  congr
  funext i
  cases i using Fin.cases with
  | zero =>
    simp only [vwk1_seq, vwk1_control, vwk2_seq, vwk2_control, lwk1_vwk1, vwk1_vwk2]
  | succ i => exact i.elim0

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
