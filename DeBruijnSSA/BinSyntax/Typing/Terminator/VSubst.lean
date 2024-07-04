import DeBruijnSSA.BinSyntax.Typing.Terminator.Basic
import DeBruijnSSA.BinSyntax.Typing.Term.Subst
import DeBruijnSSA.BinSyntax.Syntax.Subst

namespace BinSyntax

section Subst

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]
  {Γ Δ : Ctx α ε} {σ : Term.Subst φ}

def Terminator.WfD.vsubst {Γ Δ : Ctx α ε} {σ} {t : Terminator φ} (hσ : σ.WfD Γ Δ)
  : t.WfD Δ V → (t.vsubst σ).WfD Γ V
  | br hL ha => br hL (ha.subst hσ)
  | case he hs ht => case (he.subst hσ) (hs.vsubst hσ.slift) (ht.vsubst hσ.slift)
