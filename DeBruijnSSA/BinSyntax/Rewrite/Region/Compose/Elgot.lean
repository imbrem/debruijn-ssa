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

def Eqv.fixpoint {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  : Eqv φ (⟨A, ⊥⟩::Γ) (B::L) := cfg [A] nil (λ| ⟨0, _⟩ => f.vwk1.lwk1 ;; control)

theorem Eqv.fixpoint_iter {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  : fixpoint f = f ;; coprod nil (fixpoint f) := sorry

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
