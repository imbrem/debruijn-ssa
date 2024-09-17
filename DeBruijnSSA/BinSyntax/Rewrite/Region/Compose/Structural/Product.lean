import DeBruijnSSA.BinSyntax.Rewrite.Region.LSubst
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Seq
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Structural.Product
import DeBruijnSSA.BinSyntax.Typing.Region.Structural

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

def Eqv.unpacked_in {Γ : Ctx α ε} {R : LCtx α} (r : Eqv φ [(Γ.pack, ⊥)] R) (h : Γ.Pure) : Eqv φ Γ R
  := let1 h.packE (r.vwk_id (by simp [Ctx.Wkn.drop]))

theorem Eqv.unpacked_in_def' {Γ : Ctx α ε} {R : LCtx α} {r : Eqv φ [(Γ.pack, ⊥)] R} {h : Γ.Pure}
  : r.unpacked_in (φ := φ) (Γ := Γ) h = r.vsubst h.packSE := by
  rw [unpacked_in, let1_beta, vwk_id_eq_vwk, <-vsubst_fromWk, vsubst_vsubst]
  congr
  ext k; cases k using Fin.elim1
  simp [Term.Subst.Eqv.get_comp]

def Eqv.packed_in {Γ : Ctx α ε} {R : LCtx α} (r : Eqv φ Γ R) : Eqv φ [(Γ.pack, ⊥)] R
  := r.vsubst Term.Subst.Eqv.unpack

theorem Eqv.unpacked_in_packed_in {Γ : Ctx α ε} {R : LCtx α} {r : Eqv φ Γ R} {h : Γ.Pure}
  : r.packed_in.unpacked_in h = r := by
  rw [unpacked_in_def', packed_in, vsubst_vsubst, Term.Subst.Eqv.packSE_comp_unpack, vsubst_id]

theorem Eqv.packed_in_unpacked_in
  {Γ : Ctx α ε} {R : LCtx α} {r : Eqv φ [(Γ.pack, ⊥)] R} {h : Γ.Pure}
  : (r.unpacked_in h).packed_in = r := by
  rw [unpacked_in_def', packed_in, vsubst_vsubst, Term.Subst.Eqv.unpack_comp_packSE, vsubst_id]

-- TODO: {br, let1, let2, case, cfg}

end Region

end BinSyntax
