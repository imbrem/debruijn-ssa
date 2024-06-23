import DeBruijnSSA.BinSyntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Rewrite

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

-- TODO: rewrite to use subst.cons...

def Term.WfD.subst₂ {Γ : Ctx α ε} {a b : Term φ}
  (ha : a.WfD Γ ⟨A, e⟩) (hb : b.WfD Γ ⟨B, e'⟩)
  : (a.subst₂ b).WfD Γ (⟨A, e⟩::⟨B, e'⟩::Γ)
  | ⟨0, _⟩ => ha
  | ⟨1, _⟩ => hb
  | ⟨n + 2, h⟩ => var ⟨by simp at h; exact h, le_refl _⟩

def Region.RewriteD.wfD {Γ : Ctx α ε} {r r' : Region φ} {A}
  : RewriteD r r' → r.WfD Γ A → r'.WfD Γ A
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
    => WfD.let1 he
      (WfD.let2 (Term.WfD.op hf Term.WfD.var0_pure)
      (hr.vwk (by simp [Nat.liftnWk_two])))
  | let2_pair a b r, _ => sorry
  | let2_abort e r, _ => sorry
  | case_op f e r s, _ => sorry
  | case_abort e r s, _ => sorry
  | let1_case a b r s, _ => sorry
  | let2_case a b r s, _ => sorry
  | cfg_br_lt ℓ e n G h, _ => sorry
  | cfg_let1 a β n G, _ => sorry
  | cfg_let2 a β n G, _ => sorry
  | cfg_case e r s n G, _ => sorry
  | cfg_cfg β n G n' G', _ => sorry
  | cfg_zero β G, _ => sorry
  | cfg_fuse β n G k ρ hρ, _ => sorry
  | let2_eta r, _ => sorry

def Region.RewriteD.wfD_inv {Γ : Ctx α ε} {r r' : Region φ} {A}
  : RewriteD r r' → r'.WfD Γ A → r.WfD Γ A
  | let1_op f e r, _ => sorry
  | let1_pair a b r, _ => sorry
  | let1_inl a r, _ => sorry
  | let1_inr b r, _ => sorry
  | let1_abort A r, _ => sorry
  | let2_op f e r, _=> sorry
  | let2_pair a b r, _ => sorry
  | let2_abort e r, _ => sorry
  | case_op f e r s, _ => sorry
  | case_abort e r s, _ => sorry
  | let1_case a b r s, _ => sorry
  | let2_case a b r s, _ => sorry
  | cfg_br_lt ℓ e n G h, _ => sorry
  | cfg_let1 a β n G, _ => sorry
  | cfg_let2 a β n G, _ => sorry
  | cfg_case e r s n G, _ => sorry
  | cfg_cfg β n G n' G', _ => sorry
  | cfg_zero β G, _ => sorry
  | cfg_fuse β n G k ρ hρ, _ => sorry
  | let2_eta r, _ => sorry

def Region.ReduceD.wfD {Γ : Ctx α ε} {r r' : Region φ} {A}
  : ReduceD Γ.effect r r' → r.WfD Γ A → r'.WfD Γ A
  | let1_beta e r he, _ => sorry
  | case_inl e r s, _ => sorry
  | case_inr e r s, _ => sorry
  | wk_cfg β n G k ρ, _ => sorry
  | dead_cfg_left β n G m G', _ => sorry

end BinSyntax
