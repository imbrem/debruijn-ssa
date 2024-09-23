import DeBruijnSSA.BinSyntax.Rewrite.Term.Structural.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Term.Structural.Product
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Distrib

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

def Eqv.distl_pack {Γ : Ctx α ε} {R : LCtx α} {X : Ty α}
  : Eqv φ ((X.prod R.pack, ⊥)::Γ) ((R.dist X).pack, e) := match R with
  | [] => pi_r
  | _::_ => distl_inv ;;' coprod (distl_pack ;;' inj_l) inj_r
