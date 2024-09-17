import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Structural.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Structural.Product

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

def Eqv.packed {Γ : Ctx α ε} {R : LCtx α} (r : Eqv φ Γ R) : Eqv φ [(Γ.pack, ⊥)] [R.pack]
  := r.packed_out.packed_in

def Eqv.unpacked {Γ : Ctx α ε} {R : LCtx α} (r : Eqv φ [(Γ.pack, ⊥)] [R.pack]) (h : Γ.Pure)
  : Eqv φ Γ R := r.unpacked_out.unpacked_in h

-- TODO: (un)packed_in commutes with (un)packed_out

-- TODO: packed_unpacked, unpacked_packed

-- TODO: {br, let1, let2, case, cfg}

end Region

end BinSyntax
