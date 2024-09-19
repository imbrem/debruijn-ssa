import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Structural.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Structural.Product

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

theorem Eqv.packed_of_inj
  {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {a : Eqv φ Γ (R.get i, e)}
  : a.inj.packed (Δ := Δ) = a.packed.inj := by simp [packed]
