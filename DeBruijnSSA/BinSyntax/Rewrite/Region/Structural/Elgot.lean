import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Gloop
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Elgot

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region
