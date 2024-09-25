import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Product
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Cast
import DeBruijnSSA.BinSyntax.Rewrite.Term.Structural.Distrib

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

open Term.Eqv

theorem Eqv.packed_in_pack_coprod {Γ : Ctx α ε} {R L : LCtx α}
  {G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) L}
  : (pack_coprod G).packed_in (Δ := Δ)
  = vsubst (distl_pack (e := ⊥) (R := R) (X := Γ.pack)).subst0 (
    pack_coprod (λi => ((G (i.cast R.length_dist)).packed_in).cast (by rw [LCtx.get_dist]; rfl) rfl)
  )
  := sorry

theorem Eqv.packed_in_pack_coprod_arr {Γ : Ctx α ε} {R L : LCtx α}
  {G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (A::L)}
  : (pack_coprod G).packed_in (Δ := Δ)
  = ret (distl_pack (X := Γ.pack))
    ;; pack_coprod (λi => acast R.get_dist ;; (G (i.cast R.length_dist)).packed_in)
  := by
    rw [packed_in_pack_coprod, ret_seq]; congr;
    rw [vwk1_pack_coprod]; congr; funext i
    rw [vwk1_seq, vwk1_packed_in, vwk1_acast, acast_seq]
