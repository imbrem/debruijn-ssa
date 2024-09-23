import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Product

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region
