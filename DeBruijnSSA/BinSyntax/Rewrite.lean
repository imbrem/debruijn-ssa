import DeBruijnSSA.BinSyntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Rewrite

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

def Term.WfD.subst₂ {Γ : Ctx α ε} {a b : Term φ}
  (ha : a.WfD Γ ⟨A, e⟩) (hb : b.WfD Γ ⟨B, e'⟩)
  : (a.subst₂ b).WfD Γ (⟨A, e⟩::⟨B, e'⟩::Γ)
  | ⟨0, _⟩ => ha
  | ⟨1, _⟩ => hb
  | ⟨n + 2, h⟩ => var ⟨by simp at h; exact h, le_refl _⟩

def Region.PureBeta.wfD {Γ : Ctx α ε} {r r' : Region φ}
  : Region.PureBeta Γ.effect r r' → r.WfD Γ A → r'.WfD Γ A
  | h, WfD.let1 de dr => h.let1_trg ▸ dr.vsubst (h.let1_pure ▸ de.toEffect.subst0)

def Region.PRwD.wfD {Γ : Ctx α ε} {r r' : Region φ} {A}
  : PRwD r r' → r.WfD Γ A → r'.WfD Γ A
  | let1_op f e r, WfD.let1 (Term.WfD.op hf he) hr
    => WfD.let1 he (WfD.let1 (Term.WfD.op hf Term.WfD.var0_pure) hr.vwk1)
  | let1_pair a b r, WfD.let1 (Term.WfD.pair ha hb) hr
    => WfD.let1 ha $
      WfD.let1 hb.wk0 $
      WfD.let1 (Term.WfD.pair Term.WfD.var1 Term.WfD.var0) hr.vwk1.vwk1
  | let1_inl a r, WfD.let1 (Term.WfD.inl ha) hr
    => WfD.let1 ha $ WfD.let1 (Term.WfD.inl Term.WfD.var0) hr.vwk1
  | let1_inr b r, WfD.let1 (Term.WfD.inr hb) hr
    => WfD.let1 hb $ WfD.let1 (Term.WfD.inr Term.WfD.var0) hr.vwk1
  | let1_abort A r, WfD.let1 (Term.WfD.abort ha) hr
    => WfD.let1 ha $ WfD.let1 (Term.WfD.abort Term.WfD.var0) hr.vwk1
  | let2_op f e r, WfD.let2 (Term.WfD.op hf he) hr
    => WfD.let1 he (WfD.let2 (Term.WfD.op hf Term.WfD.var0_pure) (hr.vwk sorry))
  | _, _ => sorry

end BinSyntax
