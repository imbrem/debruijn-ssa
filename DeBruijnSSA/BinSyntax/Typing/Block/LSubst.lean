import DeBruijnSSA.BinSyntax.Typing.Terminator.LSubst
import DeBruijnSSA.BinSyntax.Typing.Block.Basic

namespace BinSyntax

section TerminatorSubst

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [OrderBot ε]
  {Γ Δ : Ctx α ε} {σ : Terminator.Subst φ}

def Block.WfD.lsubst {b : Block φ} (hσ : σ.WfD Γ L K) (hb : b.WfD Γ Ξ L) : (b.lsubst σ).WfD Γ Ξ K
  where
  body := hb.body
  terminator := hb.terminator.lsubst (hσ.vliftn_append'
    (by rw [hb.body.num_defs_eq_length, Ctx.reverse, List.length_reverse]))
