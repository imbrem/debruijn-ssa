import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Structural.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Structural.Product

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

def Eqv.packed {Γ : Ctx α ε} {R : LCtx α} (r : Eqv φ Γ R) : Eqv φ [(Γ.pack, ⊥)] [R.pack]
  := r.packed_out.packed_in

def Eqv.unpacked {Γ : Ctx α ε} {R : LCtx α} (r : Eqv φ [(Γ.pack, ⊥)] [R.pack]) (h : Γ.Pure)
  : Eqv φ Γ R := r.unpacked_out.unpacked_in h

theorem Eqv.unpacked_out_unpacked_in {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ [(Γ.pack, ⊥)] [R.pack]} {h : Γ.Pure}
  : (r.unpacked_in h).unpacked_out = r.unpacked_out.unpacked_in h := by
  simp [unpacked_in, unpacked_out_let1]
  induction r using Quotient.inductionOn
  simp only [Term.Eqv.packE_def', vwk_id_quot, unpacked_out_quot, let1_quot]
  rfl

-- theorem Eqv.unpacked_out_packed_in {Γ : Ctx α ε} {R : LCtx α}
--   {r : Eqv φ Γ [R.pack]} : r.packed_in.unpacked_out = r.unpacked_out.packed_in := sorry

-- theorem Eqv.packed_out_unpacked_in {Γ : Ctx α ε} {R : LCtx α}
--   {r : Eqv φ [(Γ.pack, ⊥)] R} {h : Γ.Pure}
--   : (r.unpacked_in h).packed_out = r.packed_out.unpacked_in h := sorry

-- theorem Eqv.packed_out_packed_in {Γ : Ctx α ε} {R : LCtx α}
--   {r : Eqv φ Γ R} : r.packed_in.packed_out = r.packed_out.packed_in := sorry

-- TODO: packed_unpacked, unpacked_packed via commutativity + cancellation

-- TODO: {br, let1, let2, case, cfg}

end Region

end BinSyntax
