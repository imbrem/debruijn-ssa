import DeBruijnSSA.BinSyntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Rewrite

namespace BinSyntax

variable [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

def Term.WfD.subst₂ {Γ : Ctx α ε} {a b : Term φ}
  (ha : a.WfD Γ ⟨A, e⟩) (hb : b.WfD Γ ⟨B, e'⟩)
  : (a.subst₂ b).WfD Γ (⟨A, e⟩::⟨B, e'⟩::Γ)
  | ⟨0, _⟩ => ha
  | ⟨1, _⟩ => hb
  | ⟨n + 2, h⟩ => var ⟨by simp at h; exact h, le_refl _⟩

def Region.PureBeta.WfD {Γ : Ctx α ε} {r r' : Region φ}
  : Region.PureBeta Γ.effect r r' → r.WfD Γ A → r'.WfD Γ A
  | h, WfD.let1 de dr => h.let1_trg ▸ dr.vsubst (h.let1_pure ▸ de.toeffect.subst0)

def Region.Reduce.WfD {Γ : Ctx α ε} {r r' : Region φ}
  : Region.Reduce r r' → r.WfD Γ A → r'.WfD Γ A
  | h, WfD.let2 (Term.WfD.pair da db) dr
    => h.let2_pair_trg ▸ (WfD.let1 da $ WfD.let1 (db.wk (Ctx.Wkn.id.step)) $ dr)
  | h, WfD.case (Term.WfD.inl de) dr _ => h.case_inl_trg ▸ dr.let1 de
  | h, WfD.case (Term.WfD.inr de) _ ds => h.case_inr_trg ▸ ds.let1 de

-- def Region.TermEta1.WfD {Γ : Ctx α ε} {r r' : Region φ}
--   : Region.TermEta1 r r' → r.WfD Γ L → r'.WfD Γ L
--   | h, WfD.let1 (Term.WfD.op df de) dr => h.let1_op_trg ▸ (
--       WfD.let1 de
--       $ WfD.let1 (Term.WfD.op df (Term.WfD.var Ctx.var_bot_head))
--       $ dr.vwk Ctx.Wkn.id.step.slift)
--   | h, WfD.let1 (Term.WfD.pair da db) dr => h.let1_pair_trg ▸ (
--       WfD.let1 da
--       $ WfD.let1 (db.wk Ctx.Wkn.id.step) sorry)
--       -- $ WfD.let1 (Term.WfD.pair (Term.WfD.var Ctx.var_bot_head.step) (Term.WfD.var Ctx.var_bot_head))
--       -- $ dr.vwk Ctx.Wkn.id.step.step.slift)
--   | h, WfD.let1 (Term.WfD.inl de) dr => sorry
--   | h, WfD.let1 (Term.WfD.inr de) ds => sorry
--   | h, WfD.let1 (Term.WfD.abort de) dr => sorry

-- TODO: WfD preservation for TermEta1

-- TODO: WfD preservation for TermEta2

end BinSyntax
