import DeBruijnSSA.BinSyntax.Typing.Block.Basic
import DeBruijnSSA.BinSyntax.Typing.Term.Subst
import DeBruijnSSA.BinSyntax.Typing.Body.Subst
import DeBruijnSSA.BinSyntax.Typing.Terminator.VSubst

namespace BinSyntax

section Subst

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]
  {Γ Δ : Ctx α ε} {σ : Term.Subst φ}

def Block.WfD.vsubst {b : Block φ} (hσ : σ.WfD Γ Δ) (hb : b.WfD Δ Ξ L) : (b.vsubst σ).WfD Γ Ξ L
  where
  body := hb.body.subst hσ
  terminator := hb.terminator.vsubst (hσ.liftn_append'
    (by rw [hb.body.num_defs_eq_length, Ctx.reverse, List.length_reverse]))
