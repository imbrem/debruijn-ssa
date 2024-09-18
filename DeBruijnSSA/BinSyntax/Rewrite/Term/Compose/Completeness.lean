import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Structural.Product
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Structural.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Distrib

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

-- theorem Eqv.packed_let1_den {Γ : Ctx α ε} {A B : Ty α}
--   {a : Eqv φ Γ (A, e)} {b : Eqv φ ((A, ⊥)::Γ) (B, e)}
--   : (let1 a b).packed (Δ := Δ)
--   = Eqv.split ;;' (a.packed ⋉' _) ;;' b.packed
--   := by
--   sorry

-- theorem Eqv.packed_let2_den {Γ : Ctx α ε} {A B C : Ty α}
--   {a : Eqv φ Γ (A.prod B, e)} {b : Eqv φ ((B, ⊥)::(A, ⊥)::Γ) (C, e)}
--   : (let2 a b).packed (Δ := Δ)
--   = Eqv.split ;;' ((a.packed ;;' braid) ⋉' _) ;;' assoc ;;' b.packed := by
--   sorry

-- theorem Eqv.packed_case_den {Γ : Ctx α ε} {A B : Ty α}
--   {a : Eqv φ Γ (A.coprod B, e)} {l : Eqv φ ((A, ⊥)::Γ) (C, e)} {r : Eqv φ ((B, ⊥)::Γ) (C, e)}
--   : (case a l r).packed (Δ := Δ)
--   = Eqv.split ;;' (a.packed ⋉' _) ;;' distr_inv ;;' sorry := by
--   sorry

-- @[simp]
-- theorem Eqv.packed_inl_den {Γ : Ctx α ε} {A B : Ty α} {a : Eqv φ Γ (A, e)}
--   : (inl (B := B) a).packed (Δ := Δ) = inl a.packed := sorry

-- @[simp]
-- theorem Eqv.packed_inr_den {Γ : Ctx α ε} {A B : Ty α} {a : Eqv φ Γ (B, e)}
--   : (inr (A := A) a).packed (Δ := Δ) = inr a.packed := sorry

-- @[simp]
-- theorem Eqv.packed_abort_den {Γ : Ctx α ε} {A : Ty α} {a : Eqv φ Γ (Ty.empty, e)}
--   : (abort a A).packed (Δ := Δ) = abort a.packed A := sorry
