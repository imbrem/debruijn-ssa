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

structure Region.HaveTrg (Γ : Ctx α ε) (L : LCtx α) (r r' : Region φ) where
  left : r.WfD Γ L
  right : r'.WfD Γ L

inductive Region.WfD.Cong (P : Ctx α ε → LCtx α → Region φ → Region φ → Type _)
  : Ctx α ε → LCtx α → Region φ → Region φ → Type _
  | step : P Γ L r r' → Cong P Γ L r r'
  | case_left : e.WfD Γ ⟨Ty.coprod A B, ⊥⟩ → Cong P (⟨A, ⊥⟩::Γ) L r r' → s.WfD (⟨B, ⊥⟩::Γ) L
    → Cong P Γ L (Region.case e r s) (Region.case e r' s)
  | case_right : e.WfD Γ ⟨Ty.coprod A B, ⊥⟩ → r.WfD (⟨A, ⊥⟩::Γ) L → Cong P (⟨B, ⊥⟩::Γ) L s s'
    → Cong P Γ L (Region.case e r s) (Region.case e r s')
  | let1 : e.WfD Γ ⟨A, e'⟩ → Cong P (⟨A, ⊥⟩::Γ) L r r'
    → Cong P Γ L (Region.let1 e r) (Region.let1 e r')
  | let2 : e.WfD Γ ⟨Ty.prod A B, e'⟩ → Cong P (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L r r'
    → Cong P Γ L (Region.let2 e r) (Region.let2 e r')
  | cfg_entry (R : LCtx α) :
    (hR : R.length = n) →
    Cong P Γ (R ++ L) β β' →
    (∀i : Fin n, (G i).WfD (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    Cong P Γ L (Region.cfg β n G) (Region.cfg β' n G)
  | cfg_block (R : LCtx α) :
    (hR : R.length = n) →
    β.WfD Γ (R ++ L) →
    (hG : ∀i : Fin n, (G i).WfD (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    (i : Fin n) →
    Cong P (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L) r r' →
    Cong P Γ L (Region.cfg β n (Function.update G i r)) (Region.cfg β n (Function.update G i r'))

def Region.WfD.Cong.left {P : Ctx α ε → LCtx α → Region φ → Region φ → Type _} {Γ L r r'}
  (toLeft : ∀{Γ L r r'}, P Γ L r r' → r.WfD Γ L) : Cong P Γ L r r' → r.WfD Γ L
  | step p => toLeft p
  | case_left de pr ds => case de (pr.left toLeft) ds
  | case_right de dr ps => case de dr (ps.left toLeft)
  | let1 de pr => WfD.let1 de (pr.left toLeft)
  | let2 de pr => WfD.let2 de (pr.left toLeft)
  | cfg_entry R hR pβ dG => WfD.cfg _ R hR (pβ.left toLeft) dG
  | cfg_block R hR dβ dG i pr => WfD.cfg _ R hR dβ (λk => by
    if h : k = i then
      cases h
      simp only [Function.update_same]
      exact (pr.left toLeft)
    else
      simp only [ne_eq, h, not_false_eq_true, Function.update_noteq]
      exact dG k
  )

def Region.WfD.Cong.right {P : Ctx α ε → LCtx α → Region φ → Region φ → Type _} {Γ L r r'}
  (toRight : ∀{Γ L r r'}, P Γ L r r' → r'.WfD Γ L) : Cong P Γ L r r' → r'.WfD Γ L
  | step p => toRight p
  | case_left de pr ds => case de (pr.right toRight) ds
  | case_right de dr ps => case de dr (ps.right toRight)
  | let1 de pr => WfD.let1 de (pr.right toRight)
  | let2 de pr => WfD.let2 de (pr.right toRight)
  | cfg_entry R hR pβ dG => WfD.cfg _ R hR (pβ.right toRight) dG
  | cfg_block R hR dβ dG i pr => WfD.cfg _ R hR dβ (λk => by
    if h : k = i then
      cases h
      simp only [Function.update_same]
      exact (pr.right toRight)
    else
      simp only [ne_eq, h, not_false_eq_true, Function.update_noteq]
      exact dG k
  )

-- TODO: therefore, a prefunctor to HaveTrg lifts via Cong...

def Region.RewriteD.wfD {Γ : Ctx α ε} {r r' : Region φ} {L}
  : RewriteD r r' → r.WfD Γ L → r'.WfD Γ L
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

def Region.RewriteD.wfD_inv {Γ : Ctx α ε} {r r' : Region φ} {L}
  : RewriteD r r' → r'.WfD Γ L → r.WfD Γ L
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

def Region.ReduceD.wfD {Γ : Ctx α ε} {r r' : Region φ} {L}
  : ReduceD Γ.effect r r' → r.WfD Γ L → r'.WfD Γ L
  | let1_beta e r he, _ => sorry
  | case_inl e r s, _ => sorry
  | case_inr e r s, _ => sorry
  | wk_cfg β n G k ρ, _ => sorry
  | dead_cfg_left β n G m G', _ => sorry

def Region.StepD.wfD {Γ : Ctx α ε} {r r' : Region φ} {L}
  : StepD Γ.effect r r' → r.WfD Γ L → r'.WfD Γ L
  | reduce p => p.wfD
  | rw p => p.wfD
  | rw_symm p => p.wfD_inv

end BinSyntax
