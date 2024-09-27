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

theorem Eqv.split_rtimes_pi_r_distl_packed {A B : Ty α} {Γ : Ctx α ε}
  : split (φ := φ) (e := e) (Γ := Δ)
  ;;' Ctx.pack ((A.coprod B, ⊥)::Γ) ⋊' pi_r ;;' distl_inv
  = distl_inv
  ;;' sum
    (_ ⋊' (split ;;' inj_l ⋉' _) ;;' assoc_inv)
    (_ ⋊' (split ;;' inj_r ⋉' _) ;;' assoc_inv)
  := split_rtimes_pi_r_distl

-- theorem Eqv.split_rtimes_nil_packed_distl {A B C : Ty α} {Γ : Ctx α ε}
--   : split (φ := φ) (A := Ctx.pack ((A.coprod B, ⊥)::Γ)) (e := e) (Γ := Δ)
--   ;;' _ ⋊' Term.Eqv.nil.packed ;;' distl_inv
--   = distl_inv
--   ;;' sum
--     (_ ⋊' (split ;;' inj_l ⋉' _) ;;' assoc_inv)
--     (_ ⋊' (split ;;' inj_r ⋉' _) ;;' assoc_inv) := by
--   rw [seq_distl_inv]
--   simp [
--     seq_rtimes, split, distl_inv, seq_let2, coprod_seq, sum, wk1_seq, wk1_coprod,
--     inl_coprod, inr_coprod, seq_assoc, seq_ltimes, wk1_rtimes, seq_rtimes,
--     let2_pair
--   ]
--   simp [nil, let1_beta_var0]
