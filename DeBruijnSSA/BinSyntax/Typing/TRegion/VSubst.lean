import DeBruijnSSA.BinSyntax.Typing.TRegion.Basic
import DeBruijnSSA.BinSyntax.Typing.Terminator.VSubst

namespace BinSyntax

section Subst

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]
  {Γ Δ : Ctx α ε} {σ : Term.Subst φ}

def TRegion.WfD.vsubst {Γ Δ : Ctx α ε} {σ}  {r : TRegion φ} (hσ : σ.WfD Γ Δ)
  : r.WfD Δ L → (r.vsubst σ).WfD Γ L
  | let1 da dt => let1 (da.subst hσ) (dt.vsubst hσ.slift)
  | let2 da dt => let2 (da.subst hσ) (dt.vsubst hσ.sliftn₂)
  | cfg n R hR hr hG => cfg n R hR (hr.vsubst hσ) (λi => (hG i).vsubst hσ.slift)
