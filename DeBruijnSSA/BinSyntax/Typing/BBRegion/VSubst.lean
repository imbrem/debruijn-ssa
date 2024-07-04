import DeBruijnSSA.BinSyntax.Typing.BBRegion.Basic
import DeBruijnSSA.BinSyntax.Typing.Block.VSubst

namespace BinSyntax

section Subst

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]
  {Γ Δ : Ctx α ε} {σ : Term.Subst φ}

def BBRegion.WfD.vsubst {Γ Δ : Ctx α ε} {σ} {r : BBRegion φ} (hσ : σ.WfD Γ Δ)
  : r.WfD Δ L → (r.vsubst σ).WfD Γ L
  | cfg n R hR hb hG => cfg n R hR (hb.vsubst hσ)
    (λi => (hG i).vsubst (hσ.liftn_append_cons' _ (by rw [hb.body.num_defs_eq_length])))
