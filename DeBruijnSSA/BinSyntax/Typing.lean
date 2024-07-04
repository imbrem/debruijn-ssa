import DeBruijnSSA.BinSyntax.Typing.Ctx
import DeBruijnSSA.BinSyntax.Typing.LCtx
import DeBruijnSSA.BinSyntax.Typing.Term
import DeBruijnSSA.BinSyntax.Typing.Region
import DeBruijnSSA.BinSyntax.Typing.Terminator
import DeBruijnSSA.BinSyntax.Typing.Body
import DeBruijnSSA.BinSyntax.Typing.Block
import DeBruijnSSA.BinSyntax.Typing.BBRegion
import DeBruijnSSA.BinSyntax.Typing.TRegion

-- namespace BinSyntax

-- section Minimal

-- variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

-- def Term.WfD.var0_pure {ty} {Γ : Ctx α ε} {effect}
--   : WfD (⟨ty, ⊥⟩::Γ) (@Term.var φ 0) ⟨ty, effect⟩
--   := var (by simp)

-- def Term.WfD.var1_pure {head ty} {Γ : Ctx α ε} {effect}
--   : WfD (head::⟨ty, ⊥⟩::Γ) (@Term.var φ 1) ⟨ty, effect⟩
--   := var (by simp)

-- theorem Term.WfD.effect_le
--   {Γ : Ctx α ε} {a : Term φ} {A e} (h : WfD Γ a ⟨A, e⟩) : a.effect Γ.effect ≤ e
--   := match h with
--   | var dv => by
--     simp only [effect, Ctx.effect, dv.length, ↓reduceDIte, List.get_eq_getElem]; exact dv.get.2
--   | op df de => sup_le_iff.mpr ⟨df.effect, de.effect_le⟩
--   | let1 da db => sorry
--   | pair dl dr => sup_le_iff.mpr ⟨dl.effect_le, dr.effect_le⟩
--   | let2 da db => sorry
--   | inl dl => dl.effect_le
--   | inr dr => dr.effect_le
--   | case da dl dr => sorry
--   | abort da => da.effect_le
--   | unit _ => bot_le

-- end Minimal

-- -- == SPECULATIVE ==

-- -- TODO: FWfD, FWf, associated lore

-- -- TODO: propositional variants for below...

-- -- TODO: substitution-terminator typing

-- -- TODO: substitution-CFG typing

-- -- TODO: _partial_ substitutions for more standard SSA? parameter tagging?

-- -- TODO: 3 address code via var-only substitution; everything trivially SSA with preserved vars
-- -- via id-substitution.

-- end BinSyntax
