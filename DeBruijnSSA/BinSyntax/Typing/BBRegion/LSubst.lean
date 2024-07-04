import DeBruijnSSA.BinSyntax.Typing.BBRegion.Basic
import DeBruijnSSA.BinSyntax.Typing.Block.LSubst

namespace BinSyntax

section TerminatorSubst

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [OrderBot ε]
  {Γ Δ : Ctx α ε} {σ : Terminator.Subst φ}

def BBRegion.WfD.lsubst {Γ : Ctx α ε} {L} {σ} {r : BBRegion φ} (hσ : σ.WfD Γ L K)
  : r.WfD Γ L → (r.lsubst σ).WfD Γ K
  | cfg n R hR hb hG => cfg n R hR
    (hb.lsubst (hσ.liftn_append' hR.symm))
    (λi => (hG i).lsubst
      ((hσ.liftn_append' hR.symm).vliftn_append_cons' _ (by rw [hb.body.num_defs_eq_length])))
