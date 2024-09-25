import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Seq
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Product
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Distrib

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

theorem Eqv.let2_eta_vsubst0_distl_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : vsubst ((var 1 Ctx.Var.shead.step).pair (var 0 Ctx.Var.shead)).subst0
      (distl_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := _::_::Γ) (L := L))
  = coprod
      (ret $ inl (pair (var 1 (by simp)) (var 0 Ctx.Var.shead)))
      (ret $ inr (pair (var 1 (by simp)) (var 0 Ctx.Var.shead))) := by
  rw [distl_inv, vsubst_let2, var0_subst0, wk_res_self, let2_pair, let1_beta, let1_beta]
  rfl

theorem Eqv.let2_eta_seq_distl_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : ret (φ := φ) ((var 1 Ctx.Var.shead.step).pair (var 0 Ctx.Var.shead))
    ;; distl_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := _::Γ) (L := L)
  = coprod
      (ret $ inl (pair (var 1 (by simp)) (var 0 Ctx.Var.shead)))
      (ret $ inr (pair (var 1 (by simp)) (var 0 Ctx.Var.shead))) := by
  rw [ret_seq, vwk1_distl_inv, let2_eta_vsubst0_distl_inv]

theorem Eqv.distl_eq_ret {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : distl (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)
  = ret Term.Eqv.distl := by
  simp only [Term.Eqv.distl, ret_of_coprod, <-rtimes_eq_ret]
  rfl

theorem Eqv.distl_inv_eq_ret {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : distl_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)
  = ret Term.Eqv.distl_inv := by
  simp only [Term.Eqv.distl_inv, <-let2_ret, ret_of_coprod]; rfl

theorem Eqv.Pure.distl {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (distl (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).Pure
  := ⟨Term.Eqv.distl, distl_eq_ret⟩

theorem Eqv.Pure.distl_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (distl_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).Pure
  := ⟨Term.Eqv.distl_inv, distl_inv_eq_ret⟩

theorem Eqv.distl_distl_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : distl (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)
  ;; distl_inv = nil := by
  rw [distl_eq_ret, distl_inv_eq_ret, <-ret_of_seq, Term.Eqv.distl_distl_inv_pure]; rfl

theorem Eqv.distl_inv_distl {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : distl_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)
  ;; distl = nil := by
  rw [distl_eq_ret, distl_inv_eq_ret, <-ret_of_seq, Term.Eqv.distl_inv_distl_pure]; rfl
