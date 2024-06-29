import DeBruijnSSA.BinSyntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Rewrite

import Mathlib.Data.Fintype.Quotient

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
    CongD P (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L) (G i) g' →
    CongD P Γ L (Region.cfg β n G) (Region.cfg β n (Function.update G i g'))
  | rel : P Γ L r r' → CongD P Γ L r r'

def WfD.CongD.left {P : Ctx α ε → LCtx α → Region φ → Region φ → Sort _} {Γ L r r'}
  (toLeft : ∀{Γ L r r'}, P Γ L r r' → r.WfD Γ L) : CongD P Γ L r r' → r.WfD Γ L
  | case_left de pr ds => case de (pr.left toLeft) ds
  | case_right de dr ps => case de dr (ps.left toLeft)
  | let1 de pr => WfD.let1 de (pr.left toLeft)
  | let2 de pr => WfD.let2 de (pr.left toLeft)
  | cfg_entry R hR pβ dG => WfD.cfg _ R hR (pβ.left toLeft) dG
  | cfg_block R hR dβ dG i pr => WfD.cfg _ R hR dβ (λk => by
    if h : k = i then
      cases h
      exact (pr.left toLeft)
    else
      exact dG k
  )
  | rel p => toLeft p

def WfD.CongD.right {P : Ctx α ε → LCtx α → Region φ → Region φ → Sort _} {Γ L r r'}
  (toRight : ∀{Γ L r r'}, P Γ L r r' → r'.WfD Γ L) : CongD P Γ L r r' → r'.WfD Γ L
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
  | rel p => toRight p

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
  | step {Γ L r r'} : r.WfD Γ L → r'.WfD Γ L → FStepD Γ.effect r r' → TStepD Γ L r r'
  | step_op {Γ L r r'} : r.WfD Γ L → r'.WfD Γ L → FStepD Γ.effect r' r → TStepD Γ L r r'
  | initial {Γ L} : Γ.IsInitial → r.WfD Γ L → r'.WfD Γ L → TStepD Γ L r r'
  | terminal {Γ L} : e.WfD Γ ⟨Ty.unit, ⊥⟩ → e'.WfD Γ ⟨Ty.unit, ⊥⟩ → r.WfD (⟨Ty.unit, ⊥⟩::Γ) L
    → TStepD Γ L (let1 e r) (let1 e' r)

def TStepD.symm {Γ L} {r r' : Region φ} : TStepD Γ L r r' → TStepD Γ L r' r
  | step d d' p => step_op d' d p
  | step_op d d' p => step d' d p
  | initial i d d' => initial i d' d
  | terminal e e' d => terminal e' e d

inductive TStep : (Γ : Ctx α ε) → (L : LCtx α) → (r r' : Region φ) → Prop
  | step {Γ L r r'} : r.Wf Γ L → r'.Wf Γ L → FStep Γ.effect r r' → TStep Γ L r r'
  | step_op {Γ L r r'} : r.Wf Γ L → r'.Wf Γ L → FStep Γ.effect r' r → TStep Γ L r r'
  | initial {Γ L} : Γ.IsInitial → r.Wf Γ L → r'.Wf Γ L → TStep Γ L r r'
  | terminal {Γ L} : e.Wf Γ ⟨Ty.unit, ⊥⟩ → e'.Wf Γ ⟨Ty.unit, ⊥⟩ → r.Wf (⟨Ty.unit, ⊥⟩::Γ) L
    → TStep Γ L (let1 e r) (let1 e' r)

theorem TStep.symm {Γ L} {r r' : Region φ} : TStep Γ L r r' → TStep Γ L r' r
  | step d d' p => step_op d' d p
  | step_op d d' p => step d' d p
  | initial i d d' => initial i d' d
  | terminal e e' d => terminal e' e d

theorem TStep.left {Γ L} {r r' : Region φ} : TStep Γ L r r' → r.Wf Γ L
  | TStep.step d _ _ => d
  | TStep.step_op d _ _ => d
  | TStep.initial _ d _ => d
  | TStep.terminal de _ dr => dr.let1 de

theorem TStep.right {Γ L} {r r' : Region φ} : TStep Γ L r r' → r'.Wf Γ L
  | TStep.step _ d _ => d
  | TStep.step_op _ d _ => d
  | TStep.initial _ _ d => d
  | TStep.terminal _ de dr => dr.let1 de

theorem TStep.vwk {Γ Δ : Ctx α ε} {L r r' ρ} (hρ : Γ.Wkn Δ ρ)
  : TStep (φ := φ) Δ L r r' → TStep Γ L (r.vwk ρ) (r'.vwk ρ)
  | TStep.step d d' p => TStep.step (d.vwk hρ) (d'.vwk hρ)
    ((p.wk_eff (λi hi => by
      have hi : i < Δ.length := d.fvs hi
      have hρ := hρ i hi
      simp [Ctx.effect, hρ.length, hi, hρ.get.2]
      )).vwk ρ)
  | TStep.step_op d d' p => TStep.step_op (d.vwk hρ) (d'.vwk hρ)
    ((p.wk_eff (λi hi => by
      have hi : i < Δ.length := d'.fvs hi
      have hρ := hρ i hi
      simp [Ctx.effect, hρ.length, hi, hρ.get.2]
      )).vwk ρ)
  | TStep.initial di d d' => TStep.initial (di.wk hρ) (d.vwk hρ) (d'.vwk hρ)
  | TStep.terminal de de' dr => TStep.terminal (de.wk hρ) (de'.wk hρ) (dr.vwk hρ.slift)

inductive Wf.Cong (P : Ctx α ε → LCtx α → Region φ → Region φ → Prop)
  : Ctx α ε → LCtx α → Region φ → Region φ → Prop
  | case_left : e.Wf Γ ⟨Ty.coprod A B, e'⟩ → Cong P (⟨A, ⊥⟩::Γ) L r r' → s.Wf (⟨B, ⊥⟩::Γ) L
    → Cong P Γ L (Region.case e r s) (Region.case e r' s)
  | case_right : e.Wf Γ ⟨Ty.coprod A B, e'⟩ → r.Wf (⟨A, ⊥⟩::Γ) L → Cong P (⟨B, ⊥⟩::Γ) L s s'
    → Cong P Γ L (Region.case e r s) (Region.case e r s')
  | let1 : a.Wf Γ ⟨A, e⟩ → Cong P (⟨A, ⊥⟩::Γ) L r r'
    → Cong P Γ L (Region.let1 a r) (Region.let1 a r')
  | let2 : a.Wf Γ ⟨Ty.prod A B, e⟩ → Cong P (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L r r'
    → Cong P Γ L (Region.let2 a r) (Region.let2 a r')
  | cfg_entry (R : LCtx α) :
    (hR : R.length = n) →
    Cong P Γ (R ++ L) β β' →
    (∀i : Fin n, (G i).Wf (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    Cong P Γ L (Region.cfg β n G) (Region.cfg β' n G)
  | cfg_block (R : LCtx α) :
    (hR : R.length = n) →
    β.Wf Γ (R ++ L) →
    (hG : ∀i : Fin n, (G i).Wf (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    (i : Fin n) →
    Cong P (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L) (G i) g' →
    Cong P Γ L (Region.cfg β n G) (Region.cfg β n (Function.update G i g'))
  | rel : P Γ L r r' → Cong P Γ L r r'

theorem Wf.Cong.left {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ L r r'}
  (toLeft : ∀{Γ L r r'}, P Γ L r r' → r.Wf Γ L) : Wf.Cong P Γ L r r' → r.Wf Γ L
  | case_left de pr ds => case de (pr.left toLeft) ds
  | case_right de dr ps => case de dr (ps.left toLeft)
  | let1 de pr => Wf.let1 de (pr.left toLeft)
  | let2 de pr => Wf.let2 de (pr.left toLeft)
  | cfg_entry R hR pβ dG => Wf.cfg _ R hR (pβ.left toLeft) dG
  | cfg_block R hR dβ dG i pr => Wf.cfg _ R hR dβ (λk => by
    if h : k = i then
      cases h
      exact (pr.left toLeft)
    else
      exact dG k
  )
  | rel p => toLeft p

theorem Wf.Cong.right {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ L r r'}
  (toRight : ∀{Γ L r r'}, P Γ L r r' → r'.Wf Γ L) : Wf.Cong P Γ L r r' → r'.Wf Γ L
  | case_left de pr ds => case de (pr.right toRight) ds
  | case_right de dr ps => case de dr (ps.right toRight)
  | let1 de pr => Wf.let1 de (pr.right toRight)
  | let2 de pr => Wf.let2 de (pr.right toRight)
  | cfg_entry R hR pβ dG => Wf.cfg _ R hR (pβ.right toRight) dG
  | cfg_block R hR dβ dG i pr => Wf.cfg _ R hR dβ (λk => by
    if h : k = i then
      cases h
      simp only [Function.update_same]
      exact (pr.right toRight)
    else
      simp only [ne_eq, h, not_false_eq_true, Function.update_noteq]
      exact dG k
  )
  | rel p => toRight p

theorem Wf.Cong.vwk {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop}
  (toVwk : ∀Γ Δ L r r' ρ, Γ.Wkn Δ ρ → P Δ L r r' → P Γ L (r.vwk ρ) (r'.vwk ρ))
  {Γ L r r'}
  {ρ : ℕ → ℕ} (hρ : Γ.Wkn Δ ρ)
  : Wf.Cong P Δ L r r' → Wf.Cong P Γ L (r.vwk ρ) (r'.vwk ρ)
  | case_left de pr ds => case_left (de.wk hρ) (pr.vwk toVwk hρ.slift) (ds.vwk hρ.slift)
  | case_right de dr ps => case_right (de.wk hρ) (dr.vwk hρ.slift) (ps.vwk toVwk hρ.slift)
  | let1 de pr => let1 (de.wk hρ) (pr.vwk toVwk hρ.slift)
  | let2 de pr => let2 (de.wk hρ) (pr.vwk toVwk hρ.sliftn₂)
  | cfg_entry R hR pβ dG => cfg_entry R hR (pβ.vwk toVwk hρ) (λi => (dG i).vwk hρ.slift)
  | cfg_block R hR dβ dG i pr => by
    simp only [Region.vwk, Function.comp_update_apply]
    exact cfg_block R hR (dβ.vwk hρ) (λi => (dG i).vwk hρ.slift) i (pr.vwk toVwk hρ.slift)
  | rel p => rel $ toVwk _ _ _ _ _ _ hρ p

theorem Wf.Cong.eqv_iff {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ L r r'}
  (toLeft : ∀{Γ L r r'}, P Γ L r r' → r.Wf Γ L)
  (toRight : ∀{Γ L r r'}, P Γ L r r' → r'.Wf Γ L)
  (p : EqvGen (Wf.Cong P Γ L) r r') : r.Wf Γ L ↔ r'.Wf Γ L
  := by induction p with
  | rel _ _ h => exact ⟨λ_ => h.right toRight, λ_ => h.left toLeft⟩
  | refl => rfl
  | symm _ _ _ I => exact I.symm
  | trans _ _ _ _ _ Il Ir => exact Il.trans Ir

theorem Wf.Cong.case_left_eqv
  {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {r r' s : Region φ}
  (he : e.Wf Γ ⟨Ty.coprod A B, e'⟩)
  (p : EqvGen (Wf.Cong P (⟨A, ⊥⟩::Γ) L) r r')
  (hs : s.Wf (⟨B, ⊥⟩::Γ) L)
  : EqvGen (Wf.Cong P Γ L) (Region.case e r s) (Region.case e r' s)
  := by induction p with
  | rel _ _ h => exact EqvGen.rel _ _ (h.case_left he hs)
  | refl _ => exact EqvGen.refl _
  | symm _ _ _ I => exact I.symm
  | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

theorem Wf.Cong.case_right_eqv
  {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {r s s' : Region φ}
  (he : e.Wf Γ ⟨Ty.coprod A B, e'⟩)
  (hr : r.Wf (⟨A, ⊥⟩::Γ) L)
  (p : EqvGen (Wf.Cong P (⟨B, ⊥⟩::Γ) L) s s')
  : EqvGen (Wf.Cong P Γ L) (Region.case e r s) (Region.case e r s')
  := by induction p with
  | rel _ _ h => exact EqvGen.rel _ _ (h.case_right he hr)
  | refl _ => exact EqvGen.refl _
  | symm _ _ _ I => exact I.symm
  | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

theorem Wf.Cong.let1_eqv
  {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop}
  {a : Term φ} (ha : a.Wf Γ ⟨A, e⟩)
  (p : EqvGen (Wf.Cong P (⟨A, ⊥⟩::Γ) L) r r')
  : EqvGen (Wf.Cong P Γ L) (Region.let1 a r) (Region.let1 a r')
  := by induction p with
  | rel _ _ h => exact EqvGen.rel _ _ (h.let1 ha)
  | refl _ => exact EqvGen.refl _
  | symm _ _ _ I => exact I.symm
  | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

theorem Wf.Cong.let2_eqv
  {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop}
  {a : Term φ} (ha : a.Wf Γ ⟨Ty.prod A B, e⟩)
  (p : EqvGen (Wf.Cong P (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L) r r')
  : EqvGen (Wf.Cong P Γ L) (Region.let2 a r) (Region.let2 a r')
  := by induction p with
  | rel _ _ h => exact EqvGen.rel _ _ (h.let2 ha)
  | refl _ => exact EqvGen.refl _
  | symm _ _ _ I => exact I.symm
  | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

theorem Wf.Cong.cfg_entry_eqv
  {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop}
  (R : LCtx α) (hR : R.length = n)
  (p : EqvGen (Wf.Cong P Γ (R ++ L)) β β')
  (dG : ∀i : Fin n, (G i).Wf (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L))
  : EqvGen (Wf.Cong P Γ L) (Region.cfg β n G) (Region.cfg β' n G)
  := by induction p with
  | rel _ _ h => exact EqvGen.rel _ _ (h.cfg_entry R hR dG)
  | refl _ => exact EqvGen.refl _
  | symm _ _ _ I => exact I.symm
  | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

theorem Wf.Cong.cfg_block_eqv
  {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop}
  (R : LCtx α) (hR : R.length = n)
  (β)
  (dβ : β.Wf Γ (R ++ L))
  (dG : ∀i : Fin n, (G i).Wf (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L))
  (i : Fin n)
  (p : EqvGen (Wf.Cong P (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) (G i) g')
  (toLeft : ∀{Γ L r r'}, P Γ L r r' → r.Wf Γ L)
  (toRight : ∀{Γ L r r'}, P Γ L r r' → r'.Wf Γ L)
  : EqvGen (Wf.Cong P Γ L) (Region.cfg β n G) (Region.cfg β n (Function.update G i g'))
  := by
  generalize hg : G i = g
  rw [hg] at p
  induction p generalizing G with
  | rel _ _ h => exact EqvGen.rel _ _ $ (hg ▸ h).cfg_block _ hR dβ dG i
  | refl _ =>
    rw [<-hg, Function.update_eq_self]
    exact EqvGen.refl _
  | symm x y hxy I =>
    have I := @I (Function.update G i x)
    rw [Function.update_idem, <-hg, Function.update_eq_self] at I
    apply (I _ (by simp)).symm
    intro k
    if h : k = i then
      cases h
      rw [Function.update_same]
      apply (eqv_iff toLeft toRight hxy).mpr
      rw [<-hg]
      apply dG
    else
      rw [Function.update_noteq h]
      exact dG k
  | trans x y z hxy _ Il Ir =>
    apply EqvGen.trans _ _ _ (Il dG hg)
    have h : Function.update G i z = Function.update (Function.update G i y) i z
      := by simp
    rw [h]
    apply Ir _ (by simp)
    intro k
    if h : k = i then
      cases h
      rw [Function.update_same]
      apply (eqv_iff toLeft toRight hxy).mp
      rw [<-hg]
      apply dG
    else
      rw [Function.update_noteq h]
      exact dG k

def CStep (Γ : Ctx α ε) (L : LCtx α) (r r' : Region φ) : Prop
  := Wf.Cong TStep Γ L r r'

theorem CStep.case_left {Γ : Ctx α ε} {L : LCtx α} {r r' s : Region φ}
  (de : e.Wf Γ ⟨Ty.coprod A B, ⊥⟩) (pr : CStep (⟨A, ⊥⟩::Γ) L r r')
  (ds : s.Wf (⟨B, ⊥⟩::Γ) L)
  : CStep Γ L (Region.case e r s) (Region.case e r' s)
  := Wf.Cong.case_left de pr ds

theorem CStep.case_right {Γ : Ctx α ε} {L : LCtx α} {r s s' : Region φ}
  (de : e.Wf Γ ⟨Ty.coprod A B, ⊥⟩) (dr : r.Wf (⟨A, ⊥⟩::Γ) L)
  (ps : CStep (⟨B, ⊥⟩::Γ) L s s')
  : CStep Γ L (Region.case e r s) (Region.case e r s')
  := Wf.Cong.case_right de dr ps

theorem CStep.let1 {Γ : Ctx α ε} {L : LCtx α} {r r' : Region φ}
  (da : a.Wf Γ ⟨A, e⟩) (h : CStep (⟨A, ⊥⟩::Γ) L r r')
  : CStep Γ L (Region.let1 a r) (Region.let1 a r')
  := Wf.Cong.let1 da h

theorem CStep.let2 {Γ : Ctx α ε} {L : LCtx α} {r r' : Region φ}
  (da : a.Wf Γ ⟨Ty.prod A B, e⟩) (h : CStep (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L r r')
  : CStep Γ L (Region.let2 a r) (Region.let2 a r')
  := Wf.Cong.let2 da h

theorem CStep.cfg_entry {Γ : Ctx α ε} {L : LCtx α} {R : LCtx α} {n β β' G}
  (hR : R.length = n) (pβ : CStep (φ := φ) Γ (R ++ L) β β')
  (dG : ∀i : Fin n, (G i).Wf (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L))
  : CStep Γ L (Region.cfg β n G) (Region.cfg β' n G)
  := Wf.Cong.cfg_entry R hR pβ dG

theorem CStep.cfg_block {Γ : Ctx α ε} {L : LCtx α} {R : LCtx α} {n β G i g'}
  (hR : R.length = n) (dβ : β.Wf Γ (R ++ L))
  (dG : ∀i : Fin n, (G i).Wf (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L))
  (pr : CStep (φ := φ) (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L) (G i) g')
  : CStep Γ L (Region.cfg β n G) (Region.cfg β n (Function.update G i g'))
  := Wf.Cong.cfg_block R hR dβ dG i pr

theorem CStep.vwk {Γ : Ctx α ε} {L : LCtx α} {r r' : Region φ}
  {ρ : ℕ → ℕ} (hρ : Γ.Wkn Δ ρ)
  (p : CStep Δ L r r') : CStep Γ L (r.vwk ρ) (r'.vwk ρ)
  := Wf.Cong.vwk (λ_ _ _ _ _ _ hρ p => p.vwk hρ) hρ p

theorem CStep.left {Γ : Ctx α ε} {L : LCtx α} {r r' : Region φ}
  (h : CStep Γ L r r') : r.Wf Γ L
  := Wf.Cong.left TStep.left h

theorem CStep.right {Γ : Ctx α ε} {L : LCtx α} {r r' : Region φ}
  (h : CStep Γ L r r') : r'.Wf Γ L
  := Wf.Cong.right TStep.right h

theorem CStep.eqv_iff {Γ : Ctx α ε} {L : LCtx α} {r r' : Region φ}
  (h : EqvGen (CStep Γ L) r r') : r.Wf Γ L ↔ r'.Wf Γ L
  := Wf.Cong.eqv_iff TStep.left TStep.right h

theorem CStep.case_left_eqv {Γ : Ctx α ε} {L : LCtx α} {r r' s : Region φ}
  (de : e.Wf Γ ⟨Ty.coprod A B, e'⟩)
  (p : EqvGen (CStep (⟨A, ⊥⟩::Γ) L) r r')
  (ds : s.Wf (⟨B, ⊥⟩::Γ) L)
  : EqvGen (CStep Γ L) (Region.case e r s) (Region.case e r' s)
  := Wf.Cong.case_left_eqv de p ds

theorem CStep.case_right_eqv {Γ : Ctx α ε} {L : LCtx α} {r s s' : Region φ}
  (de : e.Wf Γ ⟨Ty.coprod A B, e'⟩)
  (dr : r.Wf (⟨A, ⊥⟩::Γ) L)
  (ps : EqvGen (CStep (⟨B, ⊥⟩::Γ) L) s s')
  : EqvGen (CStep Γ L) (Region.case e r s) (Region.case e r s')
  := Wf.Cong.case_right_eqv de dr ps

theorem CStep.let1_eqv {Γ : Ctx α ε} {L : LCtx α} {r r' : Region φ}
  (da : a.Wf Γ ⟨A, e⟩) (h : EqvGen (CStep (⟨A, ⊥⟩::Γ) L) r r')
  : EqvGen (CStep Γ L) (Region.let1 a r) (Region.let1 a r')
  := Wf.Cong.let1_eqv da h

theorem CStep.let2_eqv {Γ : Ctx α ε} {L : LCtx α} {r r' : Region φ}
  (da : a.Wf Γ ⟨Ty.prod A B, e⟩) (h : EqvGen (CStep (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L) r r')
  : EqvGen (CStep Γ L) (Region.let2 a r) (Region.let2 a r')
  := Wf.Cong.let2_eqv da h

theorem CStep.cfg_entry_eqv {Γ : Ctx α ε} {L : LCtx α} {R : LCtx α} {n β β' G}
  (hR : R.length = n) (pβ : EqvGen (CStep (φ := φ) Γ (R ++ L)) β β')
  (dG : ∀i : Fin n, (G i).Wf (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L))
  : EqvGen (CStep Γ L) (Region.cfg β n G) (Region.cfg β' n G)
  := Wf.Cong.cfg_entry_eqv R hR pβ dG

theorem CStep.cfg_block_eqv {Γ : Ctx α ε} {L : LCtx α} {R : LCtx α} {n β G i g'}
  (hR : R.length = n) (dβ : β.Wf Γ (R ++ L))
  (dG : ∀i : Fin n, (G i).Wf (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L))
  (pr : EqvGen (CStep (φ := φ) (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) (G i) g')
  : EqvGen (CStep Γ L) (Region.cfg β n G) (Region.cfg β n (Function.update G i g'))
  := Wf.Cong.cfg_block_eqv R hR β dβ dG i pr TStep.left TStep.right

theorem CStep.vwk_eqv {Γ Δ : Ctx α ε} {L : LCtx α} {r r' : Region φ}
  {ρ : ℕ → ℕ} (hρ : Γ.Wkn Δ ρ)
  (p : EqvGen (CStep Δ L) r r') : EqvGen (CStep Γ L) (r.vwk ρ) (r'.vwk ρ)
  := by induction p with
  | rel _ _ p => exact EqvGen.rel _ _ (p.vwk hρ)
  | symm _ _ _ I => exact I.symm
  | refl => exact EqvGen.refl _
  | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

def InS.CStep {Γ : Ctx α ε} {L : LCtx α} (r r' : InS φ Γ L) : Prop
  := Region.CStep (φ := φ) Γ L r r'

theorem CStep.toIns {Γ : Ctx α ε} {L : LCtx α} {r r' : Region φ}
  (hr : r.Wf Γ L) (hr' : r'.Wf Γ L)
  (h : CStep Γ L r r') : InS.CStep ⟨r, hr⟩ ⟨r', hr'⟩
  := h

theorem CStep.eqv_toIns {Γ : Ctx α ε} {L : LCtx α} {r r' : Region φ}
  (hr : r.Wf Γ L) (hr' : r'.Wf Γ L)
  (h : EqvGen (CStep Γ L) r r') : EqvGen InS.CStep ⟨r, hr⟩ ⟨r', hr'⟩
  := by induction h with
  | rel _ _ h => exact EqvGen.rel _ _ h
  | refl => exact EqvGen.refl _
  | symm _ _ _ I => exact (I hr' hr).symm
  | trans _ y _ hxy _ Il Ir =>
    exact EqvGen.trans _ _ _ (Il hr ((eqv_iff hxy).mp hr)) (Ir _ hr')

instance InS.Setoid (φ) [EffInstSet φ (Ty α) ε] (Γ : Ctx α ε) (L : LCtx α) : Setoid (InS φ Γ L)
  := EqvGen.Setoid InS.CStep

theorem InS.CStep.eqv_to_region {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ Γ L}
  (h : r ≈ r') : EqvGen (Region.CStep (φ := φ) Γ L) r r'
  := by induction h with
  | rel _ _ h => exact EqvGen.rel _ _ h
  | refl => exact EqvGen.refl _
  | symm _ _ _ I => exact I.symm
  | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

theorem InS.CStep.of_region {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ Γ L}
  (h : EqvGen (Region.CStep (φ := φ) Γ L) r r') : r ≈ r'
  := CStep.eqv_toIns r.prop r'.prop h

theorem InS.eqv_iff {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ Γ L}
  : r ≈ r' ↔ EqvGen (Region.CStep (φ := φ) Γ L) r r'
  := ⟨CStep.eqv_to_region, CStep.of_region⟩

theorem InS.let1_congr {Γ : Ctx α ε} {L : LCtx α}
  {r r' : InS φ _ L} (a : Term.InS φ Γ ⟨A, e⟩)
    : r ≈ r' → InS.let1 a r ≈ InS.let1 a r' := by
  simp only [eqv_iff]
  apply Region.CStep.let1_eqv a.prop

theorem InS.let2_congr {Γ : Ctx α ε} {L : LCtx α}
  {r r' : InS φ _ L} (a : Term.InS φ Γ ⟨Ty.prod A B, e⟩)
    : r ≈ r' → InS.let2 a r ≈ InS.let2 a r' := by
  simp only [eqv_iff]
  apply Region.CStep.let2_eqv a.prop

theorem InS.case_left_congr {Γ : Ctx α ε} {L : LCtx α}
  {r r' : InS φ _ L} (e : Term.InS φ Γ ⟨Ty.coprod A B, e⟩)
    : r ≈ r' → (s : _) → InS.case e r s ≈ InS.case e r' s := by
  simp only [eqv_iff]
  intro pr s
  apply Region.CStep.case_left_eqv e.prop pr s.prop

theorem InS.case_right_congr {Γ : Ctx α ε} {L : LCtx α}
  {s s' : InS φ _ L} (e : Term.InS φ Γ ⟨Ty.coprod A B, e'⟩)
    : (r : _) → s ≈ s' → InS.case e r s ≈ InS.case e r s' := by
  simp only [eqv_iff]
  intro r pr
  apply Region.CStep.case_right_eqv e.prop r.prop pr

theorem InS.case_congr {Γ : Ctx α ε} {L : LCtx α}
  {r r' s s' : InS φ _ L} (e : Term.InS φ Γ ⟨Ty.coprod A B, e'⟩)
  (hr : r ≈ r') (hs : s ≈ s') : InS.case e r s ≈ InS.case e r' s' :=
  (case_left_congr e hr s).trans _ _ _ (case_right_congr e _ hs)

theorem InS.cfg_entry_congr {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {β β' : InS φ Γ (R ++ L)} {G} (pβ : β ≈ β')
  : InS.cfg R β G ≈ InS.cfg R β' G := by
  simp only [eqv_iff]
  apply Region.CStep.cfg_entry_eqv rfl
  rw [eqv_iff] at pβ
  exact pβ
  exact λi => (G i).prop

theorem InS.cfg_block_congr {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α) (β : InS φ Γ (R ++ L)) (G) (i) {g' : InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  (pG : (G i) ≈ g')
  : InS.cfg R β G ≈ InS.cfg R β (Function.update G i g') := by
  simp only [eqv_iff, cfg]
  rw [coe_update]
  apply Region.CStep.cfg_block_eqv
  exact β.prop
  exact (λi => (G i).prop)
  rw [<-eqv_iff]
  apply pG
  rfl

theorem InS.cfg_blocks_partial_congr {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α) (β : InS φ Γ (R ++ L)) {G G'} (pG : G ≈ G') (k : ℕ)
  : InS.cfg R β G ≈ InS.cfg R β (λi => if i < k then (G' i) else (G i)) := by
  induction k with
  | zero => simp only [not_lt_zero', ↓reduceIte]; exact Setoid.refl _
  | succ k I =>
    apply Setoid.trans I
    if h : R.length ≤ k then
      have h : ∀i : Fin R.length, i < k ↔ i < k + 1 := λi =>
        ⟨λ_ => Nat.lt_of_lt_of_le i.prop (Nat.le_succ_of_le h),
         λ_ => Nat.lt_of_lt_of_le i.prop h⟩
      simp only [h]
      apply Setoid.refl
    else
      have h' :
        (λi : Fin R.length => if i < k + 1 then (G' i) else (G i))
        = (Function.update
          (λi : Fin R.length => if i < k then (G' i) else (G i))
          ⟨k, Nat.lt_of_not_le h⟩ (G' ⟨k, Nat.lt_of_not_le h⟩))
        := funext (λi => by
          split
          case isTrue h =>
            cases h with
            | refl => simp
            | step h =>
              have h := Nat.lt_of_succ_le h
              rw [Function.update_noteq]
              simp [h]
              simp only [ne_eq, Fin.ext_iff]
              exact Nat.ne_of_lt h
          case isFalse h =>
            have h := Nat.lt_of_succ_le $ Nat.le_of_not_lt h
            have h' := Nat.not_lt_of_lt $ h
            rw [Function.update_noteq]
            simp [h']
            simp only [ne_eq, Fin.ext_iff]
            exact Ne.symm $ Nat.ne_of_lt h)
      rw [h']
      apply cfg_block_congr
      simp [pG ⟨k, Nat.lt_of_not_le h⟩]

theorem InS.cfg_blocks_congr {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α) (β : InS φ Γ (R ++ L)) {G G'} (pG : G ≈ G')
  : InS.cfg R β G ≈ InS.cfg R β G' := by
  have h : G' = λi : Fin R.length => if i < R.length then (G' i) else (G i) := by simp
  rw [h]
  apply cfg_blocks_partial_congr
  exact pG

theorem InS.cfg_congr {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α) {β β' : InS φ Γ (R ++ L)} (pβ : β ≈ β') {G G'} (pG : G ≈ G')
  : InS.cfg R β G ≈ InS.cfg R β' G' := by
  apply Setoid.trans
  apply cfg_entry_congr
  assumption
  apply cfg_blocks_congr
  assumption

theorem InS.vwk_congr {Γ Δ : Ctx α ε} {L : LCtx α} {r r' : InS φ Δ L}
  (ρ : ℕ → ℕ) (hρ : Γ.Wkn Δ ρ) : r ≈ r' → r.vwk ρ hρ ≈ r'.vwk ρ hρ := by
  simp only [eqv_iff]
  apply CStep.vwk_eqv
  assumption

-- theorem InS.wk_congr {Γ : Ctx α ε} {L : LCtx α} {ρ : ℕ → ℕ}
--   {r r' : InS φ Δ L} (h : r ≈ r') (hρ : Γ.Wkn Δ ρ) : r.vwk ρ hρ ≈ r'.vwk ρ hρ := by
--   induction r with

def Eqv (φ) [EffInstSet φ (Ty α) ε] (Γ : Ctx α ε) (L : LCtx α) := Quotient (InS.Setoid φ Γ L)

def InS.q (a : InS φ Γ L) : Eqv φ Γ L := Quotient.mk _ a

theorem Eqv.sound {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ Γ L}
  (h : r ≈ r') : r.q = r'.q := Quotient.sound h

theorem Eqv.eq {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ Γ L}
  : r.q = r'.q ↔ r ≈ r' := Quotient.eq

def Eqv.let1 (a : Term.InS φ Γ ⟨A, e⟩) (r : Eqv φ (⟨A, ⊥⟩::Γ) L) : Eqv φ Γ L
  := Quotient.liftOn r (λr => InS.q (r.let1 a)) (λ_ _ h => Quotient.sound (InS.let1_congr a h))

theorem InS.let1_q {a : Term.InS φ Γ ⟨A, e⟩} {r : InS φ (⟨A, ⊥⟩::Γ) L}
  : r.q.let1 a = (r.let1 a).q := rfl

def Eqv.let2 (a : Term.InS φ Γ ⟨Ty.prod A B, e⟩) (r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L) : Eqv φ Γ L
  := Quotient.liftOn r (λr => InS.q (r.let2 a)) (λ_ _ h => Quotient.sound (InS.let2_congr a h))

theorem InS.let2_q {a : Term.InS φ Γ ⟨Ty.prod A B, e⟩} {r : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  : r.q.let2 a = (r.let2 a).q := rfl

def Eqv.case
  (e : Term.InS φ Γ ⟨Ty.coprod A B, e⟩) (r : Eqv φ (⟨A, ⊥⟩::Γ) L) (s : Eqv φ (⟨B, ⊥⟩::Γ) L)
  : Eqv φ Γ L := Quotient.liftOn₂ r s (λr s => InS.q (InS.case e r s))
    (λ_ _ _ _ h1 h2 => Quotient.sound (InS.case_congr e h1 h2))

theorem InS.case_q {e : Term.InS φ Γ ⟨Ty.coprod A B, e⟩}
  {r : InS φ (⟨A, ⊥⟩::Γ) L} {s : InS φ (⟨B, ⊥⟩::Γ) L}
  : (r.q).case e s.q = (r.case e s).q := rfl

def Eqv.cfg
  (R : LCtx α)
  (β : Eqv φ Γ (R ++ L)) (G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : Eqv φ Γ L := let G' := Quotient.finChoice G; Quotient.liftOn₂ β G'
    (λβ G => InS.q (InS.cfg R β G)) (λ_ _ _ _ h1 h2 => Quotient.sound (InS.cfg_congr R h1 h2))

def Eqv.vwk
  {Γ Δ : Ctx α ε} {L : LCtx α} (ρ : ℕ → ℕ) (hρ : Γ.Wkn Δ ρ) (r : Eqv φ Δ L)
  : Eqv φ Γ L := Quotient.liftOn r
    (λr => InS.q (r.vwk ρ hρ))
    (λ_ _ h => Quotient.sound (InS.vwk_congr ρ hρ h))

theorem InS.cfg_q {R : LCtx α} {β : InS φ Γ (R ++ L)} {G : ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : (β.q).cfg R (λi => (G i).q) = (β.cfg R G).q := by simp [Eqv.cfg, q, Quotient.finChoice_eq]

theorem InS.let1_op {Γ : Ctx α ε} {L : LCtx α}
  {r r' : InS φ (⟨B, ⊥⟩::Γ) L}
  (f : φ) (hf : Φ.EFn f A B e)
  (a : Term.InS φ Γ ⟨A, e⟩)
    : r.let1 (a.op f hf)
    ≈ (r.vwk1.let1 ((Term.InS.var 0 (by simp)).op f hf)).let1 a
  := sorry

-- theorem Eqv.let1_op {Γ : Ctx α ε} {L : LCtx α}
--   {r r' : Eqv φ (⟨B, ⊥⟩::Γ) L}
--   (f : φ) (hf : Φ.EFn f A B e)
--   (a : Term.InS φ Γ ⟨A, e⟩)
--     : Eqv.let1 (a.op f hf) r = (r.vwk1.let1 ((Term.InS.var 0 (by simp)).op f hf)).let1 a
--   := sorry

theorem InS.let1_pair {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α} (e' := ⊥)
  {r r' : InS φ (⟨Ty.prod A B, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩) (b : Term.InS φ Γ ⟨B, e⟩)
    : r.let1 (a.pair b) ≈ (
      let1 a $
      let1 (b.wk Nat.succ (by simp)) $
      let1 ((Term.InS.var 1 (by simp)).pair (e := e') (Term.InS.var 0 (by simp))) $
      r.vwk1.vwk1)
  := sorry

theorem InS.let1_inl {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α} (e' := ⊥)
  {r r' : InS φ (⟨A.coprod B, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩)
    : r.let1 a.inl
    ≈ (r.vwk1.let1 ((Term.InS.var 0 (by simp)).inl (e := e'))).let1 a
  := sorry

theorem InS.let1_inr {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α} (e' := ⊥)
  {r r' : InS φ (⟨A.coprod B, ⊥⟩::Γ) L}
  (b : Term.InS φ Γ ⟨B, e⟩)
    : r.let1 b.inr
    ≈ (r.vwk1.let1 ((Term.InS.var 0 (by simp)).inr (e := e'))).let1 b
  := sorry

theorem InS.let1_abort {Γ : Ctx α ε} {L : LCtx α} {A : Ty α} (e' := ⊥)
  {r r' : InS φ (⟨A, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨Ty.empty, e⟩)
    : r.let1 (a.abort _)
    ≈ (r.vwk1.let1 ((Term.InS.var 0 (by simp)).abort (e := e') _)).let1 a
  := sorry

theorem InS.let2_op {Γ : Ctx α ε} {L : LCtx α}
  {r r' : InS φ (⟨C, ⊥⟩::⟨B, ⊥⟩::Γ) L}
  (f : φ) (hf : Φ.EFn f A (Ty.prod B C) e)
  (a : Term.InS φ Γ ⟨A, e⟩)
    : r.let2 (a.op f hf) ≈ (
      let1 a $
      let2 ((Term.InS.var 0 (by simp)).op f hf) $
      r.vwk (ρ := Nat.liftnWk 2 Nat.succ) (by apply Ctx.Wkn.sliftn₂; simp))
  := sorry

theorem InS.let2_pair {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
  {r r' : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩)
  (b : Term.InS φ Γ ⟨B, e⟩)
    : r.let2 (a.pair b) ≈ (
      let1 a $
      let1 (b.wk Nat.succ (by simp)) r)
  := sorry

theorem InS.let2_abort {Γ : Ctx α ε} {L : LCtx α} {A : Ty α} (e' := ⊥)
  {r r' : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨Ty.empty, e⟩)
    : r.let2 (a.abort _) ≈ (
      let1 a $
      let2 ((Term.InS.var 0 (by simp)).abort (e := e') (A.prod B)) $
      r.vwk (Nat.liftnWk 2 Nat.succ) (by apply Ctx.Wkn.sliftn₂; simp))
  := sorry


end Region

end BinSyntax
