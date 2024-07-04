import DeBruijnSSA.BinSyntax.Typing.Term.Subst
import DeBruijnSSA.BinSyntax.Typing.Body.Basic

namespace BinSyntax

section Subst

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]
  {Γ Δ : Ctx α ε} {σ : Term.Subst φ}

def Body.WfD.subst {Γ Δ : Ctx α ε} {σ} {b : Body φ} (hσ : σ.WfD Γ Δ)
  : b.WfD Δ V → (b.subst σ).WfD Γ V
  | nil => nil
  | let1 da dt => let1 (da.subst hσ) (dt.subst hσ.slift)
  | let2 da dt => let2 (da.subst hσ) (dt.subst hσ.sliftn₂)
