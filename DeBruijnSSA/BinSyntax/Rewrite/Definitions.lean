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

namespace Region

structure HaveTrg (Γ : Ctx α ε) (L : LCtx α) (r r' : Region φ) where
  left : r.WfD Γ L
  right : r'.WfD Γ L

inductive WfD.CongD (P : Ctx α ε → LCtx α → Region φ → Region φ → Sort _)
  : Ctx α ε → LCtx α → Region φ → Region φ → Sort _
  | step : P Γ L r r' → CongD P Γ L r r'
  | case_left : e.WfD Γ ⟨Ty.coprod A B, ⊥⟩ → CongD P (⟨A, ⊥⟩::Γ) L r r' → s.WfD (⟨B, ⊥⟩::Γ) L
    → CongD P Γ L (Region.case e r s) (Region.case e r' s)
  | case_right : e.WfD Γ ⟨Ty.coprod A B, ⊥⟩ → r.WfD (⟨A, ⊥⟩::Γ) L → CongD P (⟨B, ⊥⟩::Γ) L s s'
    → CongD P Γ L (Region.case e r s) (Region.case e r s')
  | let1 : e.WfD Γ ⟨A, e'⟩ → CongD P (⟨A, ⊥⟩::Γ) L r r'
    → CongD P Γ L (Region.let1 e r) (Region.let1 e r')
  | let2 : e.WfD Γ ⟨Ty.prod A B, e'⟩ → CongD P (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L r r'
    → CongD P Γ L (Region.let2 e r) (Region.let2 e r')
  | cfg_entry (R : LCtx α) :
    (hR : R.length = n) →
    CongD P Γ (R ++ L) β β' →
    (∀i : Fin n, (G i).WfD (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    CongD P Γ L (Region.cfg β n G) (Region.cfg β' n G)
  | cfg_block (R : LCtx α) :
    (hR : R.length = n) →
    β.WfD Γ (R ++ L) →
    (hG : ∀i : Fin n, (G i).WfD (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    (i : Fin n) →
    CongD P (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L) r r' →
    CongD P Γ L (Region.cfg β n (Function.update G i r)) (Region.cfg β n (Function.update G i r'))

def WfD.CongD.left {P : Ctx α ε → LCtx α → Region φ → Region φ → Sort _} {Γ L r r'}
  (toLeft : ∀{Γ L r r'}, P Γ L r r' → r.WfD Γ L) : CongD P Γ L r r' → r.WfD Γ L
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

def WfD.CongD.right {P : Ctx α ε → LCtx α → Region φ → Region φ → Sort _} {Γ L r r'}
  (toRight : ∀{Γ L r r'}, P Γ L r r' → r'.WfD Γ L) : CongD P Γ L r r' → r'.WfD Γ L
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

-- TODO: therefore, a prefunctor to HaveTrg lifts via CongD...

-- def RewriteD.wfD {Γ : Ctx α ε} {r r' : Region φ} {L}
--   : RewriteD r r' → r.WfD Γ L → r'.WfD Γ L
--   | let1_op f e r, WfD.let1 (Term.WfD.op hf he) hr
--     => WfD.let1 he (WfD.let1 (Term.WfD.op hf Term.WfD.var0_pure) hr.vwk1)
--   | let1_pair a b r, WfD.let1 (Term.WfD.pair ha hb) hr
--     => WfD.let1 ha $
--       WfD.let1 hb.wk0 $
--       WfD.let1 (Term.WfD.pair Term.WfD.var1 Term.WfD.var0) hr.vwk1.vwk1
--   | let1_inl a r, WfD.let1 (Term.WfD.inl ha) hr
--     => WfD.let1 ha $ WfD.let1 (Term.WfD.inl Term.WfD.var0) hr.vwk1
--   | let1_inr b r, WfD.let1 (Term.WfD.inr hb) hr
--     => WfD.let1 hb $ WfD.let1 (Term.WfD.inr Term.WfD.var0) hr.vwk1
--   | let1_abort A r, WfD.let1 (Term.WfD.abort ha) hr
--     => WfD.let1 ha $ WfD.let1 (Term.WfD.abort Term.WfD.var0) hr.vwk1
--   | let2_op f e r, WfD.let2 (Term.WfD.op hf he) hr
--     => WfD.let1 he
--       (WfD.let2 (Term.WfD.op hf Term.WfD.var0_pure)
--       (hr.vwk (by simp [Nat.liftnWk_two])))
--   | let2_pair a b r, _ => sorry
--   | let2_abort e r, _ => sorry
--   | case_op f e r s, _ => sorry
--   | case_abort e r s, _ => sorry
--   | let1_case a b r s, _ => sorry
--   | let2_case a b r s, _ => sorry
--   | cfg_br_lt ℓ e n G h, _ => sorry
--   | cfg_let1 a β n G, _ => sorry
--   | cfg_let2 a β n G, _ => sorry
--   | cfg_case e r s n G, _ => sorry
--   | cfg_cfg β n G n' G', _ => sorry
--   | cfg_zero β G, WfD.cfg _ [] rfl dβ dG => dβ
--   | cfg_fuse β n G k ρ hρ, WfD.cfg _ R hR dβ dG => sorry
--   | let2_eta r, _ => sorry

-- def RewriteD.wfD_inv {Γ : Ctx α ε} {r r' : Region φ} {L}
--   : RewriteD r r' → r'.WfD Γ L → r.WfD Γ L
--   | let1_op f e r, _ => sorry
--   | let1_pair a b r, _ => sorry
--   | let1_inl a r, _ => sorry
--   | let1_inr b r, _ => sorry
--   | let1_abort A r, _ => sorry
--   | let2_op f e r, _=> sorry
--   | let2_pair a b r, _ => sorry
--   | let2_abort e r, _ => sorry
--   | case_op f e r s, _ => sorry
--   | case_abort e r s, _ => sorry
--   | let1_case a b r s, _ => sorry
--   | let2_case a b r s, _ => sorry
--   | cfg_br_lt ℓ e n G h, _ => sorry
--   | cfg_let1 a β n G, _ => sorry
--   | cfg_let2 a β n G, _ => sorry
--   | cfg_case e r s n G, _ => sorry
--   | cfg_cfg β n G n' G', _ => sorry
--   | cfg_zero β G, dβ => WfD.cfg 0 [] rfl dβ (λi => i.elim0)
--   | cfg_fuse β n G k ρ hρ, WfD.cfg _ R hR dβ dG => sorry
--   | let2_eta r, _ => sorry

-- def ReduceD.wfD {Γ : Ctx α ε} {r r' : Region φ} {L}
--   : ReduceD r r' → r.WfD Γ L → r'.WfD Γ L
--   | case_inl e r s, WfD.case (Term.WfD.inl de) dr ds => dr.let1 de
--   | case_inr e r s, WfD.case (Term.WfD.inr de) dr ds => ds.let1 de
--   | wk_cfg β n G k ρ, WfD.cfg _ R hR dβ dG =>
--     sorry
--   | dead_cfg_left β n G m G', WfD.cfg _ R hR dβ dG =>
--     sorry

-- def StepD.wfD {Γ : Ctx α ε} {r r' : Region φ} {L}
--   : StepD Γ.effect r r' → r.WfD Γ L → r'.WfD Γ L
--   | let1_beta e r he
--     => λ | _ => sorry
--   | reduce p => p.wfD
--   | rw p => p.wfD
--   | rw_op p => p.wfD_inv

-- def BCongD.wfD {Γ : Ctx α ε} {r r' : Region φ} {L}
--   : BCongD StepD Γ.effect r r' → r.WfD Γ L → r'.WfD Γ L
--   | step s, d => s.wfD d
--   | let1 e p, WfD.let1 de dr => ((Γ.effect_append_bot ▸ p).wfD dr).let1 de
--   | let2 e p, WfD.let2 de dr => ((Γ.effect_append_bot₂ ▸ p).wfD dr).let2 de
--   | case_left e p s, WfD.case de dr ds => ((Γ.effect_append_bot ▸ p).wfD dr).case de ds
--   | case_right e r p, WfD.case de dr ds => dr.case de ((Γ.effect_append_bot ▸ p).wfD ds)
--   | cfg_entry p n G, WfD.cfg _ R hR dβ dG => (p.wfD dβ).cfg _ R hR dG
--   | cfg_block β n G i p, WfD.cfg _ R hR dβ dG => dβ.cfg _ R hR (λk => by
--     if h : i = k then
--       cases h
--       simp only [Function.update_same]
--       exact wfD (Γ.effect_append_bot ▸ p) (dG i)
--     else
--       rw [Function.update_noteq (Ne.symm h)]
--       exact dG k)

-- -- TODO: fix this...
-- set_option linter.unusedVariables false in
-- def RWD.wfD {Γ : Ctx α ε} {r r' : Region φ} {L}
--   : RWD StepD Γ.effect r r' → r.WfD Γ L → r'.WfD Γ L
--   | RWD.refl _, d => d
--   | RWD.cons p s, d => s.wfD (p.wfD d)

inductive TStepD : (Γ : Ctx α ε) → (L : LCtx α) → (r r' : Region φ) → Type _
  -- TODO: do we need to require r.WfD for rw?
  | step {Γ L r r'} : r.WfD Γ L → r'.WfD Γ L → StepD Γ.effect r r' → TStepD Γ L r r'
  | step_op {Γ L r r'} : r.WfD Γ L → r'.WfD Γ L → StepD Γ.effect r' r → TStepD Γ L r r'
  | initial {Γ L} : Γ.IsInitial → r.WfD Γ L → r'.WfD Γ L → TStepD Γ L r r'
  | terminal {Γ L} : e.WfD Γ ⟨Ty.unit, ⊥⟩ → e'.WfD Γ ⟨Ty.unit, ⊥⟩ → r.WfD (⟨Ty.unit, ⊥⟩::Γ) L
    → TStepD Γ L (let1 e r) (let1 e' r)

def TStepD.symm {Γ L} {r r' : Region φ} : TStepD Γ L r r' → TStepD Γ L r' r
  | step d d' p => step_op d' d p
  | step_op d d' p => step d' d p
  | initial i d d' => initial i d' d
  | terminal e e' d => terminal e' e d

inductive TStep : (Γ : Ctx α ε) → (L : LCtx α) → (r r' : Region φ) → Prop
  | step {Γ L r r'} : r.WfD Γ L → r'.WfD Γ L → StepD Γ.effect r r' → TStep Γ L r r'
  | step_op {Γ L r r'} : r.WfD Γ L → r'.WfD Γ L → StepD Γ.effect r' r → TStep Γ L r r'
  | initial {Γ L} : Γ.IsInitial → r.WfD Γ L → r'.WfD Γ L → TStep Γ L r r'
  | terminal {Γ L} : e.WfD Γ ⟨Ty.unit, ⊥⟩ → e'.WfD Γ ⟨Ty.unit, ⊥⟩ → r.WfD (⟨Ty.unit, ⊥⟩::Γ) L
    → TStep Γ L (let1 e r) (let1 e' r)

theorem TStep.symm {Γ L} {r r' : Region φ} : TStep Γ L r r' → TStep Γ L r' r
  | step d d' p => step_op d' d p
  | step_op d d' p => step d' d p
  | initial i d d' => initial i d' d
  | terminal e e' d => terminal e' e d

inductive WfD.Cong (P : Ctx α ε → LCtx α → Region φ → Region φ → Prop)
  : Ctx α ε → LCtx α → Region φ → Region φ → Prop
  | step : P Γ L r r' → Cong P Γ L r r'
  | case_left : e.WfD Γ ⟨Ty.coprod A B, e'⟩ → Cong P (⟨A, ⊥⟩::Γ) L r r' → s.WfD (⟨B, ⊥⟩::Γ) L
    → Cong P Γ L (Region.case e r s) (Region.case e r' s)
  | case_right : e.WfD Γ ⟨Ty.coprod A B, e'⟩ → r.WfD (⟨A, ⊥⟩::Γ) L → Cong P (⟨B, ⊥⟩::Γ) L s s'
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
  -- | collapse {Γ L} : IsEmpty (r.WfD Γ L) → IsEmpty (r'.WfD Γ L) → Cong P Γ L r r'

def Eqv (φ)
  [EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]
  (Γ : Ctx α ε) (L : LCtx α)
  := Quot (WfD.Cong (TStep (φ := φ)) Γ L)

def Eqv.br (ℓ : ℕ) (e : Term φ) : Eqv φ Γ L := Quot.mk _ (Region.br ℓ e)

def Eqv.let1 {e : Term φ} (de : e.WfD Γ ⟨A, e'⟩)
  : Eqv φ (⟨A, ⊥⟩::Γ) L → Eqv φ Γ L
  := Quot.lift (λr => Quot.mk _ (r.let1 e)) (λ_ _ h => Quot.sound (h.let1 de))

def Eqv.let2 {e : Term φ} (de : e.WfD Γ ⟨Ty.prod A B, e'⟩)
  : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L → Eqv φ Γ L
  := Quot.lift (λr => Quot.mk _ (r.let2 e)) (λ_ _ h => Quot.sound (h.let2 de))

-- def Eqv.case {e : Term φ} (de : e.WfD Γ ⟨Ty.coprod A B, e'⟩)
--   : Eqv φ (⟨A, ⊥⟩::Γ) L → Eqv φ (⟨B, ⊥⟩::Γ) L → Eqv φ Γ L
--   := Quot.lift₂ (λr s => Quot.mk _ (Region.case e r s))
--       (λr s s' ps => Quot.sound (
--         open Classical in
--         if h : Nonempty (r.WfD (⟨A, ⊥⟩::Γ) L) then
--           let ⟨dr⟩ := h;
--           WfD.Cong.case_right de dr ps
--         else
--           WfD.Cong.case_left de (WfD.Cong.collapse ⟨λ dr => h ⟨dr⟩⟩ sorry) sorry
--           -- WfD.Cong.collapse (Γ := ⟨A, ⊥⟩::Γ) (L := L) (r := r) ⟨λ | h' => h ⟨dr⟩⟩ sorry
--       ))
--       (λr r' s h => Quot.sound sorry)

-- TODO: Eqv.br, Eqv.case, Eqv.let1, Eqv2.let2, Eqv.cfg ...

end Region

end BinSyntax
