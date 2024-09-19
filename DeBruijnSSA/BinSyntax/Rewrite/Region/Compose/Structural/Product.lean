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

def Eqv.packed_in {Γ : Ctx α ε} {R : LCtx α} (r : Eqv φ Γ R) : Eqv φ ((Γ.pack, ⊥)::Δ) R
  := r.vsubst Term.Subst.Eqv.unpack

theorem Eqv.unpacked_in_packed_in {Γ : Ctx α ε} {R : LCtx α} {r : Eqv φ Γ R} {h : Γ.Pure}
  : r.packed_in.unpacked_in h = r := by
  rw [unpacked_in_def', packed_in, vsubst_vsubst, Term.Subst.Eqv.packSE_comp_unpack, vsubst_id]

theorem Eqv.packed_in_unpacked_in
  {Γ : Ctx α ε} {R : LCtx α} {r : Eqv φ [(Γ.pack, ⊥)] R} {h : Γ.Pure}
  : (r.unpacked_in h).packed_in = r := by
  rw [unpacked_in_def', packed_in, vsubst_vsubst, Term.Subst.Eqv.unpack_comp_packSE, vsubst_id]

open Term.Eqv

theorem Eqv.packed_in_br {Γ : Ctx α ε} {L : LCtx α}
  {ℓ} {a : Term.Eqv φ Γ (A, ⊥)} {hℓ}
  : (br (L := L) ℓ a hℓ).packed_in (Δ := Δ) = br ℓ a.packed hℓ := by
  simp [packed_in, Term.Eqv.packed]

theorem Eqv.packed_in_let1 {Γ : Ctx α ε} {R : LCtx α}
  {a : Term.Eqv φ Γ (A, e)} {r : Eqv φ ((A, ⊥)::Γ) R}
  : (let1 a r).packed_in (Δ := Δ)
  = let1 a.packed (let1 (pair (var 1 (by simp)) (var 0 Ctx.Var.shead)) r.packed_in) := by
  rw [packed_in, vsubst_let1]; apply congrArg
  rw [packed_in, let1_beta, vsubst_vsubst, Term.Subst.Eqv.lift_unpack]

theorem Eqv.packed_in_let2 {Γ : Ctx α ε} {R : LCtx α}
  {a : Term.Eqv φ Γ (A.prod B, e)} {r : Eqv φ ((B, ⊥)::(A, ⊥)::Γ) R}
  : (let2 a r).packed_in (Δ := Δ)
  = let2 a.packed (let1
    (pair (pair (var 2 (by simp)) (var 1 (by simp))) (var 0 Ctx.Var.shead))
    r.packed_in) := by
  rw [packed_in, vsubst_let2]; apply congrArg
  rw [packed_in, let1_beta, vsubst_vsubst, Term.Subst.Eqv.liftn₂_unpack]

theorem Eqv.packed_in_case {Γ : Ctx α ε} {R : LCtx α}
  {a : Term.Eqv φ Γ (A.coprod B, e)} {r : Eqv φ ((A, ⊥)::Γ) R} {s : Eqv φ ((B, ⊥)::Γ) R}
  : (case a r s).packed_in (Δ := Δ)
  = case a.packed
    (let1 (pair (var 1 (by simp)) (var 0 Ctx.Var.shead)) r.packed_in)
    (let1 (pair (var 1 (by simp)) (var 0 Ctx.Var.shead)) s.packed_in) := by
  rw [packed_in, vsubst_case]
  congr <;> rw [packed_in, let1_beta, vsubst_vsubst, Term.Subst.Eqv.lift_unpack]

theorem Eqv.packed_in_cfg {Γ : Ctx α ε} {R L : LCtx α}
  {β : Eqv φ Γ (R ++ L)} {G}
  : (cfg R β G).packed_in (Δ := Δ)
  = cfg R β.packed_in (λi => (let1 (pair (var 1 (by simp)) (var 0 Ctx.Var.shead)) (G i).packed_in))
  := by
  rw [packed_in, vsubst_cfg]; apply congrArg; funext i
  rw [packed_in, let1_beta, vsubst_vsubst, Term.Subst.Eqv.lift_unpack]

end Region

end BinSyntax
