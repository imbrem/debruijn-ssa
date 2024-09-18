import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Structural.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Structural.Product

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

def Eqv.packed {Γ Δ : Ctx α ε} {R : LCtx α} (r : Eqv φ Γ R) : Eqv φ ((Γ.pack, ⊥)::Δ) [R.pack]
  := r.packed_out.packed_in

def Eqv.unpacked {Γ : Ctx α ε} {R : LCtx α} (r : Eqv φ [(Γ.pack, ⊥)] [R.pack]) (h : Γ.Pure)
  : Eqv φ Γ R := r.unpacked_out.unpacked_in h

theorem Eqv.unpacked_out_unpacked_in {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ [(Γ.pack, ⊥)] [R.pack]} {h : Γ.Pure}
  : (r.unpacked_in h).unpacked_out = r.unpacked_out.unpacked_in h := by
  simp only [unpacked_in, unpacked_out_let1]
  induction r using Quotient.inductionOn
  simp only [Term.Eqv.packE_def', vwk_id_quot, unpacked_out_quot, let1_quot]
  rfl

theorem Eqv.unpacked_out_packed_in {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ Γ [R.pack]} : r.packed_in.unpacked_out = r.unpacked_out.packed_in (Δ := Δ) := by
  simp only [unpacked_out, packed_in, vsubst_lsubst]
  congr
  simp only [Subst.Eqv.unpack, unpack_def, InS.unpack, Set.mem_setOf_eq, csubst_quot,
    Term.Subst.Eqv.unpack, Subst.Eqv.vsubst_quot]
  congr; ext; simp

theorem Eqv.packed_out_unpacked_in {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ [(Γ.pack, ⊥)] R} {h : Γ.Pure}
  : (r.unpacked_in h).packed_out = r.packed_out.unpacked_in h := by
  apply unpacked_out_injective; simp [unpacked_out_unpacked_in]

theorem Eqv.packed_out_packed_in {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ Γ R} : r.packed_in.packed_out = r.packed_out.packed_in (Δ := Δ) := by
  apply unpacked_out_injective; simp [unpacked_out_packed_in]

theorem Eqv.packed_def' {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ Γ R} : r.packed (Δ := Δ) = r.packed_in.packed_out
  := by simp [packed, packed_out_packed_in]

theorem Eqv.unpacked_def' {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ [(Γ.pack, ⊥)] [R.pack]} {h : Γ.Pure}
  : r.unpacked h = r.unpacked_out.unpacked_in h := by simp [unpacked, unpacked_out_unpacked_in]

theorem Eqv.packed_unpacked {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ [(Γ.pack, ⊥)] [R.pack]} {h : Γ.Pure} : (r.unpacked h).packed = r
  := by rw [unpacked, packed_def', packed_in_unpacked_in, packed_out_unpacked_out]

theorem Eqv.unpacked_packed {Γ : Ctx α ε} {R : LCtx α}
  {r : Eqv φ Γ R} {h : Γ.Pure} : r.packed.unpacked h = r
  := by rw [unpacked, packed_def', unpacked_out_packed_out, unpacked_in_packed_in]

open Term.Eqv

-- TODO: br

theorem Eqv.packed_let1 {Γ : Ctx α ε} {R : LCtx α}
  {a : Term.Eqv φ Γ (A, e)} {r : Eqv φ ((A, ⊥)::Γ) R}
  : (let1 a r).packed (Δ := Δ)
  = let1 a.packed (let1 (pair (var 0 Ctx.Var.shead) (var 1 (by simp))) r.packed) := by
  rw [packed, packed_out_let1, packed_in_let1, <-packed]

theorem Eqv.packed_let2 {Γ : Ctx α ε} {R : LCtx α}
  {a : Term.Eqv φ Γ (A.prod B, e)} {r : Eqv φ ((B, ⊥)::(A, ⊥)::Γ) R}
  : (let2 a r).packed (Δ := Δ)
  = let2 a.packed (let1
    (pair (var 0 Ctx.Var.shead) (pair (var 1 (by simp)) (var 2 (by simp))))
    r.packed) := by
  rw [packed, packed_out_let2, packed_in_let2, <-packed]

theorem Eqv.packed_case {Γ : Ctx α ε} {R : LCtx α}
  {a : Term.Eqv φ Γ (A.coprod B, e)} {r : Eqv φ ((A, ⊥)::Γ) R} {s : Eqv φ ((B, ⊥)::Γ) R}
  : (case a r s).packed (Δ := Δ)
  = case a.packed
    (let1 (pair (var 0 Ctx.Var.shead) (var 1 (by simp))) r.packed)
    (let1 (pair (var 0 Ctx.Var.shead) (var 1 (by simp))) s.packed) := by
  simp only [packed, packed_out_case, packed_in_case]

-- TODO: cfg

end Region

end BinSyntax
