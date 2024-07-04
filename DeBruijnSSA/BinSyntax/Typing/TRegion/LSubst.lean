import DeBruijnSSA.BinSyntax.Typing.TRegion.Basic
import DeBruijnSSA.BinSyntax.Typing.Terminator.LSubst
import DeBruijnSSA.BinSyntax.Syntax.Subst

namespace BinSyntax

section TerminatorSubst

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [OrderBot ε]
  {Γ Δ : Ctx α ε} {σ : Terminator.Subst φ}

def TRegion.WfD.lsubst {Γ : Ctx α ε} {L} {σ} {r : TRegion φ} (hσ : σ.WfD Γ L K)
  : r.WfD Γ L → (r.lsubst σ).WfD Γ K
  | let1 da dt => let1 da (dt.lsubst hσ.vlift)
  | let2 da dt => let2 da (dt.lsubst hσ.vliftn₂)
  | cfg n R hR hr hG => cfg n R hR
    (hr.lsubst (hσ.liftn_append' hR.symm))
    (λi => (hG i).lsubst (hσ.liftn_append' hR.symm).vlift)
