import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Letc
import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Elgot

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

def Eqv.fixpoint_def' {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L)}
  : fixpoint f = letc A nil (f.vwk1.lwk1 ;; left_exit)
  := rfl


def Eqv.fixpoint_def_vwk1 {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L)}
  : fixpoint f = letc A nil (f.lwk1 ;; left_exit).vwk1
  := by rw [vwk1_seq, vwk1_lwk1]; rfl

-- theorem Eqv.letc_to_vwk1 {Γ : Ctx α ε} {L : LCtx α} {A : Ty α} {β : Eqv φ ((B, ⊥)::Γ) (A::L)} {G}
--   : letc A β G = letc (B.prod A)
--     (ret Term.Eqv.split ;; _ ⋊ β)
--     ((ret Term.Eqv.split ⋉ _ ;; assoc ;; _ ⋊ (let2 (Term.Eqv.var 0 Ctx.Var.shead) G.vwk2)).vwk1)
--   := by
--   sorry

theorem Eqv.letc_vwk1_den {Γ : Ctx α ε}
  {A B : Ty α} {β : Eqv φ ((X, ⊥)::Γ) [A, B]} {G : Eqv φ ((A, ⊥)::Γ) [A, B]}
  : letc A β G.vwk1 = (β.packed_out ;; sum (coprod zero nil) nil) ;;
                    coprod nil (fixpoint (G.packed_out ;; coprod (coprod zero inj_l) inj_r))
  := sorry
