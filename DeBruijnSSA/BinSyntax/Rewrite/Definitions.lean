import DeBruijnSSA.BinSyntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Rewrite

import Discretion.Utils.Quotient

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
--   | let2_eta e r, _ => sorry

-- def RewriteD.wfD_inv {Γ : Ctx α ε} {r r' : Region φ} {L}
--   : RewriteD r r' → r'.WfD Γ L → r.WfD Γ L
--   | let1_op f e r, WfD.let1 (A := A) he (WfD.let1 (Term.WfD.op hf hv) hr)
--     => sorry --WfD.let1 (Term.WfD.op sorry he) sorry
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
--   | let2_eta e r, _ => sorry

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
  -- | step_op {Γ L r r'} : r.WfD Γ L → r'.WfD Γ L → FStepD Γ.effect r' r → TStepD Γ L r r'
  | initial {Γ L} : Γ.IsInitial → r.WfD Γ L → r'.WfD Γ L → TStepD Γ L r r'
  | terminal {Γ L} : e.WfD Γ ⟨Ty.unit, ⊥⟩ → e'.WfD Γ ⟨Ty.unit, ⊥⟩ → r.WfD (⟨Ty.unit, ⊥⟩::Γ) L
    → TStepD Γ L (let1 e r) (let1 e' r)

-- def TStepD.symm {Γ L} {r r' : Region φ} : TStepD Γ L r r' → TStepD Γ L r' r
--   | step d d' p => step_op d' d p
--   | step_op d d' p => step d' d p
--   | initial i d d' => initial i d' d
--   | terminal e e' d => terminal e' e d

inductive TStep : (Γ : Ctx α ε) → (L : LCtx α) → (r r' : Region φ) → Prop
  | step {Γ L r r'} : r.Wf Γ L → r'.Wf Γ L → FStep Γ.effect r r' → TStep Γ L r r'
  -- | step_op {Γ L r r'} : r.Wf Γ L → r'.Wf Γ L → FStep Γ.effect r' r → TStep Γ L r r'
  | initial {Γ L} : Γ.IsInitial → r.Wf Γ L → r'.Wf Γ L → TStep Γ L r r'
  | terminal {Γ L} : e.Wf Γ ⟨Ty.unit, ⊥⟩ → e'.Wf Γ ⟨Ty.unit, ⊥⟩ → r.Wf (⟨Ty.unit, ⊥⟩::Γ) L
    → TStep Γ L (let1 e r) (let1 e' r)

-- theorem TStep.symm {Γ L} {r r' : Region φ} : TStep Γ L r r' → TStep Γ L r' r
--   | step d d' p => step_op d' d p
--   | step_op d d' p => step d' d p
--   | initial i d d' => initial i d' d
--   | terminal e e' d => terminal e' e d

theorem TStep.left {Γ L} {r r' : Region φ} : TStep Γ L r r' → r.Wf Γ L
  | TStep.step d _ _ => d
  -- | TStep.step_op d _ _ => d
  | TStep.initial _ d _ => d
  | TStep.terminal de _ dr => dr.let1 de

theorem TStep.right {Γ L} {r r' : Region φ} : TStep Γ L r r' → r'.Wf Γ L
  | TStep.step _ d _ => d
  -- | TStep.step_op _ d _ => d
  | TStep.initial _ _ d => d
  | TStep.terminal _ de dr => dr.let1 de

theorem TStep.vwk {Γ Δ : Ctx α ε} {L r r' ρ} (hρ : Γ.Wkn Δ ρ)
  : TStep (φ := φ) Δ L r r' → TStep Γ L (r.vwk ρ) (r'.vwk ρ)
  | TStep.step d d' p => TStep.step (d.vwk hρ) (d'.vwk hρ)
    ((p.wk_eff (λi hi => by
      have hi : i < Δ.length := d.fvs hi
      have hρ := hρ i hi
      simp only [Function.comp_apply, Ctx.effect, hρ.length, ↓reduceDIte, List.get_eq_getElem, hi,
        ge_iff_le]
      exact hρ.get.2
      )).vwk ρ)
  -- | TStep.step_op d d' p => TStep.step_op (d.vwk hρ) (d'.vwk hρ)
  --   ((p.wk_eff (λi hi => by
  --     have hi : i < Δ.length := d'.fvs hi
  --     have hρ := hρ i hi
  --     simp [Ctx.effect, hρ.length, hi, hρ.get.2]
  --     )).vwk ρ)
  | TStep.initial di d d' => TStep.initial (di.wk hρ) (d.vwk hρ) (d'.vwk hρ)
  | TStep.terminal de de' dr => TStep.terminal (de.wk hρ) (de'.wk hρ) (dr.vwk hρ.slift)

theorem TStep.lwk {Γ : Ctx α ε} {L K r r' ρ} (hρ : L.Wkn K ρ)
  : TStep (φ := φ) Γ L r r' → TStep Γ K (r.lwk ρ) (r'.lwk ρ)
  | TStep.step d d' p => TStep.step (d.lwk hρ) (d'.lwk hρ) (p.lwk ρ)
  | TStep.initial di d d' => TStep.initial di (d.lwk hρ) (d'.lwk hρ)
  | TStep.terminal de de' dr => TStep.terminal de de' (dr.lwk hρ)

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

-- TODO: Wf.Cong.lwk

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

-- TODO: lwk_eqv

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

theorem InS.cfg_congr' {Γ : Ctx α ε} {L : LCtx α}
  (n : ℕ) (R : LCtx α) (hR : R.length = n)
  {β β' : InS φ Γ (R ++ L)} (pβ : β ≈ β') {G G'} (pG : G ≈ G')
  : InS.cfg' n R hR β G ≈ InS.cfg' n R hR β' G' := by
  cases hR
  apply cfg_congr <;> assumption

theorem InS.vwk_congr {Γ Δ : Ctx α ε} {L : LCtx α} {r r' : InS φ Δ L}
  (ρ : Γ.InS Δ) : r ≈ r' → r.vwk ρ ≈ r'.vwk ρ := by
  simp only [eqv_iff]
  apply CStep.vwk_eqv
  exact ρ.prop

-- TODO: InS.lwk_congr

-- theorem InS.wk_congr {Γ : Ctx α ε} {L : LCtx α} {ρ : ℕ → ℕ}
--   {r r' : InS φ Δ L} (h : r ≈ r') (hρ : Γ.Wkn Δ ρ) : r.vwk ρ hρ ≈ r'.vwk ρ hρ := by
--   induction r with

def Eqv (φ) [EffInstSet φ (Ty α) ε] (Γ : Ctx α ε) (L : LCtx α) := Quotient (InS.Setoid φ Γ L)

def Eqv.cast {Γ : Ctx α ε} {L : LCtx α} (hΓ : Γ = Γ') (hL : L = L') (r : Eqv φ Γ L)
  : Eqv φ Γ' L' := hΓ ▸ hL ▸ r

def InS.q (a : InS φ Γ L) : Eqv φ Γ L := Quotient.mk _ a

theorem Eqv.inductionOn {Γ : Ctx α ε} {L : LCtx α} {motive : Eqv φ Γ L → Prop}
  (r : Eqv φ Γ L) (h : ∀a : InS φ Γ L, motive a.q) : motive r := Quotient.inductionOn r h

theorem Eqv.sound {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ Γ L}
  (h : r ≈ r') : r.q = r'.q := Quotient.sound h

theorem Eqv.eq {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ Γ L}
  : r.q = r'.q ↔ r ≈ r' := Quotient.eq

def Eqv.let1 (a : Term.InS φ Γ ⟨A, e⟩) (r : Eqv φ (⟨A, ⊥⟩::Γ) L) : Eqv φ Γ L
  := Quotient.liftOn r (λr => InS.q (r.let1 a)) (λ_ _ h => Quotient.sound (InS.let1_congr a h))

theorem Eqv.quot_def {Γ : Ctx α ε} {L : LCtx α} {r : InS φ Γ L}
  : ⟦r⟧ = r.q := rfl

@[simp]
theorem InS.let1_q {a : Term.InS φ Γ ⟨A, e⟩} {r : InS φ (⟨A, ⊥⟩::Γ) L}
  : r.q.let1 a = (r.let1 a).q := rfl

@[simp]
theorem Eqv.let1_quot {a : Term.InS φ Γ ⟨A, e⟩} {r : InS φ (⟨A, ⊥⟩::Γ) L}
  : let1 a ⟦r⟧ = ⟦r.let1 a⟧ := rfl

def Eqv.let2 (a : Term.InS φ Γ ⟨Ty.prod A B, e⟩) (r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L) : Eqv φ Γ L
  := Quotient.liftOn r (λr => InS.q (r.let2 a)) (λ_ _ h => Quotient.sound (InS.let2_congr a h))

@[simp]
theorem InS.let2_q {a : Term.InS φ Γ ⟨Ty.prod A B, e⟩} {r : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  : r.q.let2 a = (r.let2 a).q := rfl

@[simp]
theorem Eqv.let2_quot {a : Term.InS φ Γ ⟨Ty.prod A B, e⟩} {r : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  : let2 a ⟦r⟧ = ⟦r.let2 a⟧ := rfl

def Eqv.case
  (e : Term.InS φ Γ ⟨Ty.coprod A B, e⟩) (r : Eqv φ (⟨A, ⊥⟩::Γ) L) (s : Eqv φ (⟨B, ⊥⟩::Γ) L)
  : Eqv φ Γ L := Quotient.liftOn₂ r s (λr s => InS.q (InS.case e r s))
    (λ_ _ _ _ h1 h2 => Quotient.sound (InS.case_congr e h1 h2))

@[simp]
theorem InS.case_q {e : Term.InS φ Γ ⟨Ty.coprod A B, e⟩}
  {r : InS φ (⟨A, ⊥⟩::Γ) L} {s : InS φ (⟨B, ⊥⟩::Γ) L}
  : (r.q).case e s.q = (r.case e s).q := rfl

@[simp]
theorem Eqv.case_quot {e : Term.InS φ Γ ⟨Ty.coprod A B, e⟩}
  {r : InS φ (⟨A, ⊥⟩::Γ) L} {s : InS φ (⟨B, ⊥⟩::Γ) L}
  : case e ⟦r⟧ ⟦s⟧ = ⟦r.case e s⟧ := rfl

def Eqv.cfg_inner
  (R : LCtx α)
  (β : Eqv φ Γ (R ++ L)) (G : Quotient (α := ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)) inferInstance)
  : Eqv φ Γ L := Quotient.liftOn₂ β G
    (λβ G => InS.q (InS.cfg R β G)) (λ_ _ _ _ h1 h2 => Quotient.sound (InS.cfg_congr R h1 h2))

def Eqv.cfg
  (R : LCtx α)
  (β : Eqv φ Γ (R ++ L)) (G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : Eqv φ Γ L := cfg_inner R β (Quotient.finChoice G)

def Eqv.cfg_inner'
  (n : ℕ) (R : LCtx α) (hR : R.length = n)
  (β : Eqv φ Γ (R ++ L))
  (G : Quotient (α := ∀i : Fin n, InS φ (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) inferInstance)
  : Eqv φ Γ L := Quotient.liftOn₂ β G
    (λβ G => InS.q (InS.cfg' n R hR β G))
    (λ_ _ _ _ h1 h2 => Quotient.sound (InS.cfg_congr' n R hR h1 h2))

def Eqv.cfg'
  (n : ℕ) (R : LCtx α) (hR : R.length = n)
  (β : Eqv φ Γ (R ++ L))
  (G : ∀i : Fin n, Eqv φ (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L))
  : Eqv φ Γ L := cfg_inner' n R hR β (Quotient.finChoice G)

@[simp]
theorem InS.cfg_inner_q
  {R : LCtx α} {β : InS φ Γ (R ++ L)}
  {G : ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : (β.q).cfg_inner R ⟦G⟧ = (β.cfg R G).q
  := by simp [Eqv.cfg_inner, q]

@[simp]
theorem Eqv.cfg_inner_quot
  {R : LCtx α} {β : InS φ Γ (R ++ L)}
  {G : ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : cfg_inner R ⟦β⟧ ⟦G⟧ = ⟦InS.cfg R β G⟧ := rfl

@[simp]
theorem InS.cfg_q {R : LCtx α} {β : InS φ Γ (R ++ L)} {G : ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : (β.q).cfg R (λi => (G i).q) = (β.cfg R G).q
  := by simp [Eqv.cfg, Eqv.cfg_inner, q, Quotient.finChoice_eq]

@[simp]
theorem Eqv.cfg_quot
  {R : LCtx α} {β : InS φ Γ (R ++ L)} {G : ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : cfg R ⟦β⟧ (λi => ⟦G i⟧) = ⟦InS.cfg R β G⟧ := InS.cfg_q

def Eqv.vwk
  {Γ Δ : Ctx α ε} {L : LCtx α} (ρ : Γ.InS Δ) (r : Eqv φ Δ L)
  : Eqv φ Γ L := Quotient.liftOn r
    (λr => InS.q (r.vwk ρ))
    (λ_ _ h => Quotient.sound (InS.vwk_congr ρ h))

def Eqv.vwk_id
  {Γ Δ : Ctx α ε} {L : LCtx α} (hρ : Γ.Wkn Δ id) (r : Eqv φ Δ L)
  : Eqv φ Γ L := Quotient.liftOn r
    (λr => InS.q (r.vwk_id hρ))
    (λ_ _ h => Quotient.sound (by
      have h := InS.vwk_congr ⟨id, hρ⟩ h;
      simp only [InS.vwk, Set.mem_setOf_eq, vwk_of_id, id_eq, InS.vwk_id] at *
      exact h
      ))

def Eqv.lwk {Γ : Ctx α ε} {L K : LCtx α} (ρ : L.InS K) (r : Eqv φ Γ L)
  : Eqv φ Γ K := Quotient.liftOn r
    (λr => InS.q (r.lwk ρ))
    (λ_ _ h => Quotient.sound sorry)

def Eqv.lwk_id {Γ : Ctx α ε} {L K : LCtx α} (hρ : L.Wkn K id) (r : Eqv φ Γ L)
  : Eqv φ Γ K := Quotient.liftOn r
    (λr => InS.q (r.lwk_id hρ))
    (λ_ _ h => Quotient.sound sorry)

def Eqv.vsubst {Γ Δ : Ctx α ε} {L : LCtx α} (σ : Term.Subst.InS φ Γ Δ) (r : Eqv φ Δ L)
  : Eqv φ Γ L := Quotient.liftOn r
    (λr => InS.q (r.vsubst σ))
    (λ_ _ h => Quotient.sound sorry)

@[simp]
theorem InS.vwk_q {Γ Δ : Ctx α ε} {L : LCtx α} {ρ : Γ.InS Δ} {r : InS φ Δ L}
   : (r.q).vwk ρ = (r.vwk ρ).q := rfl

@[simp]
theorem Eqv.vwk_quot {Γ Δ : Ctx α ε} {L : LCtx α} {ρ : Γ.InS Δ} {r : InS φ Δ L}
   : Eqv.vwk ρ ⟦r⟧ = ⟦r.vwk ρ⟧ := rfl

@[simp]
theorem InS.vwk_id_q {Γ Δ : Ctx α ε} {L : LCtx α} {r : InS φ Δ L}
  (hρ : Γ.Wkn Δ id) : (r.q).vwk_id hρ = (r.vwk_id hρ).q := rfl

@[simp]
theorem Eqv.vwk_id_quot {Γ Δ : Ctx α ε} {L : LCtx α} {r : InS φ Δ L}
  (hρ : Γ.Wkn Δ id) : Eqv.vwk_id hρ ⟦r⟧ = ⟦r.vwk_id hρ⟧ := rfl

theorem Eqv.vwk_vwk {Γ Δ Ξ : Ctx α ε} {L : LCtx α} {r : Eqv φ Ξ L}
  (ρ : Γ.InS Δ) (σ : Δ.InS Ξ)
  : Eqv.vwk ρ (Eqv.vwk σ r) = Eqv.vwk (ρ.comp σ) r := by
  induction r using Quotient.inductionOn; simp [InS.vwk_vwk]

@[simp]
theorem Eqv.vwk_let1 {Γ : Ctx α ε} {L : LCtx α}
  {ρ : Γ.InS Δ} {a : Term.InS φ Δ ⟨A, e⟩} {r : Eqv φ (⟨A, ⊥⟩::Δ) L}
  : Eqv.vwk ρ (Eqv.let1 a r) = Eqv.let1 (a.wk ρ) (Eqv.vwk (ρ.lift (le_refl _)) r) := by
  induction r using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.vwk_let2 {Γ : Ctx α ε} {L : LCtx α}
  {ρ : Γ.InS Δ} {a : Term.InS φ Δ ⟨Ty.prod A B, e⟩} {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Δ) L}
  : Eqv.vwk ρ (Eqv.let2 a r)
  = Eqv.let2 (a.wk ρ) (Eqv.vwk (ρ.liftn₂ (le_refl _) (le_refl _)) r) := by
  induction r using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.vwk_case {Γ : Ctx α ε} {L : LCtx α}
  {ρ : Γ.InS Δ} {e : Term.InS φ Δ ⟨Ty.coprod A B, e⟩}
  {r : Eqv φ (⟨A, ⊥⟩::Δ) L} {s : Eqv φ (⟨B, ⊥⟩::Δ) L}
  : Eqv.vwk ρ (Eqv.case e r s)
  = Eqv.case (e.wk ρ) (Eqv.vwk (ρ.lift (le_refl _)) r) (Eqv.vwk (ρ.lift (le_refl _)) s) := by
  induction r using Quotient.inductionOn; induction s using Quotient.inductionOn; rfl

-- @[simp]
-- theorem Eqv.vwk_cfg {Γ : Ctx α ε} {L : LCtx α}
--   {R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
--   {ρ : Γ.InS Δ}
--   : Eqv.vwk ρ (Eqv.cfg R β G)
--   = Eqv.cfg R (Eqv.vwk (ρ.lift (le_refl _)) β) sorry := by
--   stop induction β using Quotient.inductionOn; simp [Eqv.cfg, Eqv.cfg_inner, Quotient.finChoice_eq]

@[simp]
theorem InS.lwk_q {Γ : Ctx α ε} {L K : LCtx α} {ρ : L.InS K} {r : InS φ Γ L}
   : (r.q).lwk ρ = (r.lwk ρ).q := rfl

@[simp]
theorem Eqv.lwk_quot {Γ : Ctx α ε} {L K : LCtx α} {ρ : L.InS K} {r : InS φ Γ L}
   : Eqv.lwk ρ ⟦r⟧ = ⟦r.lwk ρ⟧ := rfl

@[simp]
theorem InS.vsubst_q {Γ Δ : Ctx α ε} {L : LCtx α} {σ : Term.Subst.InS φ Γ Δ} {r : InS φ Δ L}
   : (r.q).vsubst σ = (r.vsubst σ).q := rfl

@[simp]
theorem Eqv.vsubst_quot {Γ Δ : Ctx α ε} {L : LCtx α} {σ : Term.Subst.InS φ Γ Δ} {r : InS φ Δ L}
   : Eqv.vsubst σ ⟦r⟧ = ⟦r.vsubst σ⟧ := rfl

theorem Eqv.vsubst_vsubst {Γ Δ Ξ : Ctx α ε} {L : LCtx α} {r : Eqv φ Ξ L}
  {σ : Term.Subst.InS φ Γ Δ} {τ : Term.Subst.InS φ Δ Ξ}
  : (r.vsubst τ).vsubst σ = r.vsubst (σ.comp τ) := by
  induction r using Quotient.inductionOn;
  simp [InS.vsubst_vsubst]

@[simp]
theorem Eqv.vsubst_let1 {Γ : Ctx α ε} {L : LCtx α}
  {σ : Term.Subst.InS φ Γ Δ} {a : Term.InS φ Δ ⟨A, e⟩} {r : Eqv φ (⟨A, ⊥⟩::Δ) L}
  : Eqv.vsubst σ (Eqv.let1 a r) = Eqv.let1 (a.subst σ) (Eqv.vsubst (σ.lift (le_refl _)) r) := by
  induction r using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.vsubst_let2 {Γ : Ctx α ε} {L : LCtx α}
  {σ : Term.Subst.InS φ Γ Δ} {a : Term.InS φ Δ ⟨Ty.prod A B, e⟩} {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Δ) L}
  : Eqv.vsubst σ (Eqv.let2 a r)
  = Eqv.let2 (a.subst σ) (Eqv.vsubst (σ.liftn₂ (le_refl _) (le_refl _)) r) := by
  induction r using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.vsubst_case {Γ : Ctx α ε} {L : LCtx α}
  {σ : Term.Subst.InS φ Γ Δ} {e : Term.InS φ Δ ⟨Ty.coprod A B, e⟩}
  {r : Eqv φ (⟨A, ⊥⟩::Δ) L} {s : Eqv φ (⟨B, ⊥⟩::Δ) L}
  : Eqv.vsubst σ (Eqv.case e r s)
  = Eqv.case (e.subst σ) (Eqv.vsubst (σ.lift (le_refl _)) r) (Eqv.vsubst (σ.lift (le_refl _)) s)
  := by induction r using Quotient.inductionOn; induction s using Quotient.inductionOn; rfl

@[simp]
theorem InS.lwk_id_q {Γ : Ctx α ε} {L K : LCtx α} {r : InS φ Γ L}
  (hρ : L.Wkn K id) : (r.q).lwk_id hρ = (r.lwk_id hρ).q := rfl

@[simp]
theorem InS.lwk_id_quot {Γ : Ctx α ε} {L K : LCtx α} {r : InS φ Γ L}
  (hρ : L.Wkn K id) : Eqv.lwk_id hρ ⟦r⟧ = ⟦r.lwk_id hρ⟧ := rfl

theorem Eqv.lwk_lwk {Γ : Ctx α ε} {L K J : LCtx α}
  {ρ : L.InS K} {σ : K.InS J}
  {r : Eqv φ Γ L}
  : (r.lwk ρ).lwk σ = r.lwk (σ.comp ρ) := by
  induction r using Quotient.inductionOn; simp [InS.lwk_lwk]

theorem Eqv.lwk_vwk {Γ Δ : Ctx α ε} {L K : LCtx α}
  {ρ : L.InS K} {σ : Γ.InS Δ}
  {r : Eqv φ Δ L}
  : (r.vwk σ).lwk ρ = (r.lwk ρ).vwk σ := by
  induction r using Quotient.inductionOn; simp [InS.lwk_vwk]

theorem Eqv.vwk_lwk {Γ Δ : Ctx α ε} {L K : LCtx α}
  {ρ : L.InS K} {σ : Γ.InS Δ}
  {r : Eqv φ Δ L}
  : (r.lwk ρ).vwk σ = (r.vwk σ).lwk ρ := by
  induction r using Quotient.inductionOn; simp [InS.vwk_lwk]

def Eqv.vwk0
  {Γ : Ctx α ε} {L : LCtx α} (r : Eqv φ Γ L)
  : Eqv φ (head::Γ) L := Eqv.vwk ⟨Nat.succ, by simp⟩ r

@[simp]
theorem InS.vwk0_q {Γ : Ctx α ε} {L : LCtx α} {r : InS φ Γ L}
  : (r.q).vwk0 (head := head) = (r.vwk0).q := rfl

@[simp]
theorem Eqv.vwk0_quot {Γ : Ctx α ε} {L : LCtx α} {r : InS φ Γ L}
  : Eqv.vwk0 (head := head) ⟦r⟧ = ⟦r.vwk0⟧ := rfl

def Eqv.vwk1
  {Γ : Ctx α ε} {L : LCtx α} (r : Eqv φ (head::Γ) L)
  : Eqv φ (head::inserted::Γ) L := Eqv.vwk ⟨Nat.liftWk Nat.succ, by simp⟩ r

@[simp]
theorem InS.vwk1_q {Γ : Ctx α ε} {L : LCtx α} {r : InS φ (head::Γ) L}
  : (r.q).vwk1 (inserted := inserted) = (r.vwk1).q := rfl

@[simp]
theorem Eqv.vwk1_quot {Γ : Ctx α ε} {L : LCtx α} {r : InS φ (head::Γ) L}
  : Eqv.vwk1 (inserted := inserted) ⟦r⟧ = ⟦r.vwk1⟧ := rfl

theorem Eqv.lwk_vwk1 {Γ : Ctx α ε} {L K : LCtx α} {ρ : L.InS K}
  {r : Eqv φ (head::Γ) L}
  : (r.vwk1 (inserted := inserted)).lwk ρ = (r.lwk ρ).vwk1 := by
  induction r using Quotient.inductionOn; simp [InS.lwk_vwk1]

theorem Eqv.vwk1_lwk {Γ : Ctx α ε} {L K : LCtx α} {ρ : L.InS K}
  {r : Eqv φ (head::Γ) L}
  : (r.lwk ρ).vwk1 = (r.vwk1 (inserted := inserted)).lwk ρ := by
  induction r using Quotient.inductionOn; simp [InS.vwk1_lwk]

theorem InS.let1_op {Γ : Ctx α ε} {L : LCtx α}
  {r : InS φ (⟨B, ⊥⟩::Γ) L}
  (f : φ) (hf : Φ.EFn f A B e)
  (a : Term.InS φ Γ ⟨A, e⟩)
    : r.let1 (a.op f hf)
    ≈ (r.vwk1.let1 ((Term.InS.var 0 (by simp)).op f hf)).let1 a
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.let1_op {Γ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨B, ⊥⟩::Γ) L}
  (f : φ) (hf : Φ.EFn f A B e)
  (a : Term.InS φ Γ ⟨A, e⟩)
    : Eqv.let1 (a.op f hf) r = (r.vwk1.let1 ((Term.InS.var 0 (by simp)).op f hf)).let1 a
  := by induction r using Quotient.inductionOn with
  | h r =>
    simp only [let1_quot, vwk1_quot]
    apply Eqv.sound
    apply InS.let1_op

theorem InS.let1_let1 {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
  {r : InS φ (⟨B, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩) (b : Term.InS φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩)
    : let1 (a.let1 b) r
    ≈ (let1 a $ let1 b $ r.vwk1)
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.let1_let1 {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
  {r : Eqv φ (⟨B, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩) (b : Term.InS φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩)
    : Eqv.let1 (a.let1 b) r = (let1 a $ let1 b $ r.vwk1)
  := by induction r using Quotient.inductionOn with
  | h r =>
    simp only [let1_quot, vwk1_quot]
    apply Eqv.sound
    apply InS.let1_let1

theorem InS.let1_pair {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α} (e' := ⊥)
  {r : InS φ (⟨Ty.prod A B, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩) (b : Term.InS φ Γ ⟨B, e⟩)
    : r.let1 (a.pair b) ≈ (
      let1 a $
      let1 (b.wk ⟨Nat.succ, (by simp)⟩) $
      let1 ((Term.InS.var 1 (by simp)).pair (e := e') (Term.InS.var 0 (by simp))) $
      r.vwk1.vwk1)
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.let1_pair {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α} (e' := ⊥)
  {r : Eqv φ (⟨Ty.prod A B, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩) (b : Term.InS φ Γ ⟨B, e⟩)
    : Eqv.let1 (a.pair b) r = (
      let1 a $
      let1 (b.wk ⟨Nat.succ, (by simp)⟩) $
      let1 ((Term.InS.var 1 (by simp)).pair (e := e') (Term.InS.var 0 (by simp))) $
      r.vwk1.vwk1)
  := by induction r using Quotient.inductionOn with
  | h r =>
    simp only [let1_quot, vwk1_quot]
    apply Eqv.sound
    apply InS.let1_pair

theorem InS.let1_inl {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α} (e' := ⊥)
  {r : InS φ (⟨A.coprod B, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩)
    : r.let1 a.inl
    ≈ (r.vwk1.let1 ((Term.InS.var 0 (by simp)).inl (e := e'))).let1 a
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.let1_inl {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α} (e' := ⊥)
  {r : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩)
    : Eqv.let1 a.inl r
    = (r.vwk1.let1 ((Term.InS.var 0 (by simp)).inl (e := e'))).let1 a
  := by induction r using Quotient.inductionOn with
  | h r =>
    simp only [let1_quot, vwk1_quot]
    apply Eqv.sound
    apply InS.let1_inl

theorem InS.let1_inr {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α} (e' := ⊥)
  {r : InS φ (⟨A.coprod B, ⊥⟩::Γ) L}
  (b : Term.InS φ Γ ⟨B, e⟩)
    : r.let1 b.inr
    ≈ (r.vwk1.let1 ((Term.InS.var 0 (by simp)).inr (e := e'))).let1 b
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.let1_inr {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α} (e' := ⊥)
  {r : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) L}
  (b : Term.InS φ Γ ⟨B, e⟩)
    : Eqv.let1 b.inr r
    = (r.vwk1.let1 ((Term.InS.var 0 (by simp)).inr (e := e'))).let1 b
  := by induction r using Quotient.inductionOn with
  | h r =>
    simp only [let1_quot, vwk1_quot]
    apply Eqv.sound
    apply InS.let1_inr

theorem InS.let1_case_t {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
  {s : InS φ (⟨C, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨Ty.coprod A B, e⟩)
  (l : Term.InS φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩)
  (r : Term.InS φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩)
    : let1 (a.case l r) s
    ≈ case a (let1 l s.vwk1) (let1 r s.vwk1)
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.let1_case_t {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
  {s : Eqv φ (⟨C, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨Ty.coprod A B, e⟩)
  (l : Term.InS φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩)
  (r : Term.InS φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩)
    : Eqv.let1 (a.case l r) s = case a (Eqv.let1 l s.vwk1) (Eqv.let1 r s.vwk1)
  := by induction s using Quotient.inductionOn with
  | h s =>
    simp only [let1_quot, vwk1_quot]
    apply Eqv.sound
    apply InS.let1_case_t

theorem InS.let1_abort {Γ : Ctx α ε} {L : LCtx α} {A : Ty α} (e' := ⊥)
  {r : InS φ (⟨A, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨Ty.empty, e⟩)
    : r.let1 (a.abort _)
    ≈ (r.vwk1.let1 ((Term.InS.var 0 (by simp)).abort (e := e') _)).let1 a
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.let1_abort {Γ : Ctx α ε} {L : LCtx α} {A : Ty α} (e' := ⊥)
  {r : Eqv φ (⟨A, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨Ty.empty, e⟩)
    : Eqv.let1 (a.abort _) r
    = (r.vwk1.let1 ((Term.InS.var 0 (by simp)).abort (e := e') _)).let1 a
  := by induction r using Quotient.inductionOn with
  | h r =>
    simp only [let1_quot, vwk1_quot]
    apply Eqv.sound
    apply InS.let1_abort

theorem InS.let2_op {Γ : Ctx α ε} {L : LCtx α}
  {r : InS φ (⟨C, ⊥⟩::⟨B, ⊥⟩::Γ) L}
  (f : φ) (hf : Φ.EFn f A (Ty.prod B C) e)
  (a : Term.InS φ Γ ⟨A, e⟩)
    : r.let2 (a.op f hf) ≈ (
      let1 a $
      let2 ((Term.InS.var 0 (by simp)).op f hf) $
      r.vwk (ρ := ⟨Nat.liftnWk 2 Nat.succ, by apply Ctx.Wkn.sliftn₂; simp⟩))
  := sorry
  -- := EqvGen.rel _ _ $ Wf.Cong.rel $
  -- TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.let2_op {Γ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨C, ⊥⟩::⟨B, ⊥⟩::Γ) L}
  (f : φ) (hf : Φ.EFn f A (Ty.prod B C) e)
  (a : Term.InS φ Γ ⟨A, e⟩)
    : Eqv.let2 (a.op f hf) r = (
      let1 a $
      let2 ((Term.InS.var 0 (by simp)).op f hf) $
      r.vwk (ρ := ⟨Nat.liftnWk 2 Nat.succ, by apply Ctx.Wkn.sliftn₂; simp⟩))
  := by induction r using Quotient.inductionOn with
  | h r =>
    simp only [let2_quot, vwk_quot, let1_quot]
    apply Eqv.sound
    apply InS.let2_op

theorem InS.let2_pair {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
  {r : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩)
  (b : Term.InS φ Γ ⟨B, e⟩)
    : r.let2 (a.pair b) ≈ (
      let1 a $
      let1 (b.wk ⟨Nat.succ, (by simp)⟩) r)
  := sorry
  -- := EqvGen.rel _ _ $ Wf.Cong.rel $
  -- TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.let2_pair {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
  {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩)
  (b : Term.InS φ Γ ⟨B, e⟩)
    : Eqv.let2 (a.pair b) r = (
      let1 a $
      let1 (b.wk ⟨Nat.succ, (by simp)⟩) r)
  := by induction r using Quotient.inductionOn with
  | h r =>
    have h : ⟦r⟧ = r.q := rfl
    simp [h]
    apply Eqv.sound
    apply InS.let2_pair

theorem InS.let2_abort {Γ : Ctx α ε} {L : LCtx α} {A : Ty α} (e' := ⊥)
  {r : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨Ty.empty, e⟩)
    : r.let2 (a.abort _) ≈ (
      let1 a $
      let2 ((Term.InS.var 0 (by simp)).abort (e := e') (A.prod B)) $
      r.vwk ⟨Nat.liftnWk 2 Nat.succ, by apply Ctx.Wkn.sliftn₂; simp⟩)
    := sorry
  -- := EqvGen.rel _ _ $ Wf.Cong.rel $
  -- TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.let2_abort {Γ : Ctx α ε} {L : LCtx α} {A : Ty α} (e' := ⊥)
  {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨Ty.empty, e⟩)
    : Eqv.let2 (a.abort _) r = (
      let1 a $
      let2 ((Term.InS.var 0 (by simp)).abort (e := e') (A.prod B)) $
      r.vwk ⟨Nat.liftnWk 2 Nat.succ, by apply Ctx.Wkn.sliftn₂; simp⟩)
  := by induction r using Quotient.inductionOn with
  | h r =>
    simp only [let2_quot, vwk_quot, let1_quot]
    apply Eqv.sound
    apply InS.let2_abort

theorem InS.case_op {Γ : Ctx α ε} {L : LCtx α}
  (f : φ) (hf : Φ.EFn f A (B.coprod C) e)
  (a : Term.InS φ Γ ⟨A, e⟩) (r : InS φ (⟨B, ⊥⟩::Γ) L) (s : InS φ (⟨C, ⊥⟩::Γ) L)
  : r.case (a.op f hf) s ≈
    (let1 a $ case (Term.InS.op f hf (Term.InS.var 0 (by simp))) r.vwk1 s.vwk1)
  := sorry
  -- := EqvGen.rel _ _ $ Wf.Cong.rel $
  -- TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.case_op {Γ : Ctx α ε} {L : LCtx α}
  (f : φ) (hf : Φ.EFn f A (B.coprod C) e)
  (a : Term.InS φ Γ ⟨A, e⟩) (r : Eqv φ (⟨B, ⊥⟩::Γ) L) (s : Eqv φ (⟨C, ⊥⟩::Γ) L)
  : Eqv.case (a.op f hf) r s =
    (let1 a $ case (Term.InS.op f hf (Term.InS.var 0 (by simp))) r.vwk1 s.vwk1)
  := by induction r using Quotient.inductionOn with
  | h r =>
    induction s using Quotient.inductionOn with
    | h s =>
      simp only [case_quot, vwk1_quot, let1_quot]
      apply Eqv.sound
      apply InS.case_op

theorem InS.case_abort {Γ : Ctx α ε} {L : LCtx α} (e' := ⊥)
  (a : Term.InS φ Γ ⟨Ty.empty, e⟩) (r : InS φ (⟨A, ⊥⟩::Γ) L) (s : InS φ (⟨B, ⊥⟩::Γ) L)
  : r.case (a.abort _) s ≈
    (let1 a $ case (Term.InS.abort (e := e') (Term.InS.var 0 (by simp)) (A.coprod B)) r.vwk1 s.vwk1)
  := sorry
  -- := EqvGen.rel _ _ $ Wf.Cong.rel $
  -- TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.case_abort {Γ : Ctx α ε} {L : LCtx α} (e' := ⊥)
  (a : Term.InS φ Γ ⟨Ty.empty, e⟩) (r : Eqv φ (⟨A, ⊥⟩::Γ) L) (s : Eqv φ (⟨B, ⊥⟩::Γ) L)
  : Eqv.case (a.abort _) r s =
    (let1 a $ case (Term.InS.abort (e := e') (Term.InS.var 0 (by simp)) (A.coprod B)) r.vwk1 s.vwk1)
  := by induction r using Quotient.inductionOn with
  | h r =>
    induction s using Quotient.inductionOn with
    | h s =>
      simp only [case_quot, vwk1_quot, let1_quot]
      apply Eqv.sound
      apply InS.case_abort

theorem InS.let1_case {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨A, ea⟩)
  (b : Term.InS φ Γ ⟨B.coprod C, eb⟩)
  {r : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  (s : InS φ (⟨C, ⊥⟩::⟨A, ⊥⟩::Γ) L)
    : (let1 a $ case (b.wk ⟨Nat.succ, (by simp)⟩) r s) ≈
      case b
        (let1 (a.wk ⟨Nat.succ, (by simp)⟩) (r.vwk ⟨Nat.swap0 1, Ctx.Wkn.swap01⟩))
        (let1 (a.wk ⟨Nat.succ, (by simp)⟩) (s.vwk ⟨Nat.swap0 1, Ctx.Wkn.swap01⟩))
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.let1_case {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨A, ea⟩)
  (b : Term.InS φ Γ ⟨B.coprod C, eb⟩)
  {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  (s : Eqv φ (⟨C, ⊥⟩::⟨A, ⊥⟩::Γ) L)
    : (Eqv.let1 a $ Eqv.case (b.wk ⟨Nat.succ, (by simp)⟩) r s) =
      Eqv.case b
        (Eqv.let1 (a.wk ⟨Nat.succ, (by simp)⟩) (r.vwk ⟨Nat.swap0 1, Ctx.Wkn.swap01⟩))
        (Eqv.let1 (a.wk ⟨Nat.succ, (by simp)⟩) (s.vwk ⟨Nat.swap0 1, Ctx.Wkn.swap01⟩))
  := by induction r using Quotient.inductionOn with
  | h r =>
    induction s using Quotient.inductionOn with
    | h s =>
      simp only [case_quot, let1_quot, vwk_quot]
      apply Eqv.sound
      apply InS.let1_case

theorem InS.let2_case {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨A.prod B, ea⟩)
  (b : Term.InS φ Γ ⟨C.coprod D, eb⟩)
  {r : InS φ (⟨C, ⊥⟩::⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  (s : InS φ (⟨D, ⊥⟩::⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L)
    : (let2 a $ case (b.wk ⟨(· + 2), (by simp)⟩) r s) ≈
      case b
        (let2 (a.wk ⟨Nat.succ, (by simp)⟩) (r.vwk ⟨Nat.swap0 2, Ctx.Wkn.swap02⟩))
        (let2 (a.wk ⟨Nat.succ, (by simp)⟩) (s.vwk ⟨Nat.swap0 2, Ctx.Wkn.swap02⟩))
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.let2_case {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨A.prod B, ea⟩)
  (b : Term.InS φ Γ ⟨C.coprod D, eb⟩)
  {r : Eqv φ (⟨C, ⊥⟩::⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  (s : Eqv φ (⟨D, ⊥⟩::⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L)
    : (Eqv.let2 a $ Eqv.case (b.wk ⟨(· + 2), (by simp)⟩) r s) =
      Eqv.case b
        (Eqv.let2 (a.wk ⟨Nat.succ, (by simp)⟩) (r.vwk ⟨Nat.swap0 2, Ctx.Wkn.swap02⟩))
        (Eqv.let2 (a.wk ⟨Nat.succ, (by simp)⟩) (s.vwk ⟨Nat.swap0 2, Ctx.Wkn.swap02⟩))
  := by induction r using Quotient.inductionOn with
  | h r =>
    induction s using Quotient.inductionOn with
    | h s =>
      simp only [case_quot, let2_quot, vwk_quot]
      apply Eqv.sound
      apply InS.let2_case

theorem InS.cfg_br_lt {Γ : Ctx α ε} {L : LCtx α}
  (ℓ) (a : Term.InS φ Γ ⟨A, ⊥⟩)
  (R : LCtx α)  (G : (i : Fin R.length) → InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  (hℓ : (R ++ L).Trg ℓ A) (hℓ' : ℓ < R.length)
  : (InS.br ℓ a hℓ).cfg R G
  ≈ (let1 a $ (G ⟨ℓ, hℓ'⟩).vwk_id (by simp only [Ctx.Wkn.lift_id_iff,
    Prod.mk_le_mk, le_refl, and_true, Ctx.Wkn.id]; exact List.get_append ℓ hℓ' ▸ hℓ.get)).cfg R G
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.cfg_br_lt {Γ : Ctx α ε} {L : LCtx α}
  (ℓ) (a : Term.InS φ Γ ⟨A, ⊥⟩)
  (R : LCtx α)  (G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  (hℓ : (R ++ L).Trg ℓ A) (hℓ' : ℓ < R.length)
  : (InS.br ℓ a hℓ).q.cfg R G
  = (let1 a $ (G ⟨ℓ, hℓ'⟩).vwk_id (by simp only [Ctx.Wkn.lift_id_iff,
    Prod.mk_le_mk, le_refl, and_true, Ctx.Wkn.id]; exact List.get_append ℓ hℓ' ▸ hℓ.get)).cfg R G
  := by
  simp only [cfg]
  generalize hG : Quotient.finChoice G = G'
  generalize hg : G ⟨ℓ, hℓ'⟩ = g
  induction G' using Quotient.inductionOn with
  | h G' =>
    induction g using Quotient.inductionOn with
    | h g =>
      have hg : ⟦g⟧ = (G' ⟨ℓ, hℓ'⟩).q := by
        rw [<-hg, InS.q]
        apply Quotient.forall_of_finChoice_eq hG
      simp only [InS.cfg_inner_q, hg, InS.vwk_id_q, InS.let1_q]
      apply Eqv.sound
      apply InS.cfg_br_lt

theorem InS.cfg_let1 {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨A, ea⟩)
  (R : LCtx α) (β : InS φ (⟨A, ⊥⟩::Γ) (R ++ L))
  (G : (i : Fin R.length) → InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
    : (let1 a β).cfg R G ≈ (let1 a $ β.cfg R (λi => (G i).vwk1))
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.cfg_let1 {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨A, ea⟩)
  (R : LCtx α) (β : Eqv φ (⟨A, ⊥⟩::Γ) (R ++ L))
  (G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
    : (let1 a β).cfg R G = (let1 a $ β.cfg R (λi => (G i).vwk1))
  := by
  simp only [cfg]
  generalize hG : Quotient.finChoice G = G'
  induction β using Quotient.inductionOn with
  | h β =>
    induction G' using Quotient.inductionOn with
    | h G' =>
      have hβ : ⟦β⟧ = β.q := rfl
      simp only [hβ, InS.let1_q, InS.cfg_inner_q]
      apply Eq.trans
      apply Eqv.sound
      apply InS.cfg_let1
      rw [<-InS.let1_q, <-InS.cfg_q]
      congr
      funext i
      rw [<-InS.vwk1_q]
      rw [InS.q]
      congr
      apply Eq.symm
      apply Quotient.forall_of_finChoice_eq hG

theorem InS.cfg_let2 {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨Ty.prod A B, ea⟩)
  (R : LCtx α) (β : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) (R ++ L))
  (G : (i : Fin R.length) → InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
    : (let2 a β).cfg R G ≈ (let2 a $ β.cfg R (λi => (G i).vwk1.vwk1))
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.cfg_let2 {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨Ty.prod A B, ea⟩)
  (R : LCtx α) (β : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) (R ++ L))
  (G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
    : (let2 a β).cfg R G = (let2 a $ β.cfg R (λi => (G i).vwk1.vwk1))
  := by
  simp only [cfg]
  generalize hG : Quotient.finChoice G = G'
  induction β using Quotient.inductionOn with
  | h β =>
    induction G' using Quotient.inductionOn with
    | h G' =>
      have hβ : ⟦β⟧ = β.q := rfl
      simp only [hβ, InS.let2_q, InS.cfg_inner_q]
      apply Eq.trans
      apply Eqv.sound
      apply InS.cfg_let2
      rw [<-InS.let2_q, <-InS.cfg_q]
      congr
      funext i
      simp only [<-InS.vwk1_q]
      rw [InS.q]
      congr
      apply Eq.symm
      apply Quotient.forall_of_finChoice_eq hG

theorem InS.cfg_case {Γ : Ctx α ε} {L : LCtx α}
  (e : Term.InS φ Γ ⟨Ty.coprod A B, ea⟩)
  (R : LCtx α)
  (r : InS φ (⟨A, ⊥⟩::Γ) (R ++ L))
  (s : InS φ (⟨B, ⊥⟩::Γ) (R ++ L))
  (G : (i : Fin R.length) → InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
    : (InS.case e r s).cfg R G
    ≈ InS.case e (r.cfg R (λi => (G i).vwk1)) (s.cfg R (λi => (G i).vwk1))
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.cfg_case {Γ : Ctx α ε} {L : LCtx α}
  (e : Term.InS φ Γ ⟨Ty.coprod A B, ea⟩)
  (R : LCtx α)
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (R ++ L))
  (s : Eqv φ (⟨B, ⊥⟩::Γ) (R ++ L))
  (G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
    : (Eqv.case e r s).cfg R G
    = Eqv.case e (r.cfg R (λi => (G i).vwk1)) (s.cfg R (λi => (G i).vwk1))
  := by
  simp only [cfg]
  generalize hG : Quotient.finChoice G = G'
  induction r using Quotient.inductionOn
  induction s using Quotient.inductionOn
  induction G' using Quotient.inductionOn
  case _ r s G =>
    have hr : ⟦r⟧ = r.q := rfl
    have hs : ⟦s⟧ = s.q := rfl
    simp only [hr, hs, InS.case_q, InS.cfg_inner_q]
    apply Eq.trans
    apply Eqv.sound
    apply InS.cfg_case
    rw [<-InS.case_q, <-InS.cfg_q]
    congr
    funext i
    simp only [<-InS.vwk1_q]
    rw [InS.q]
    congr
    apply Eq.symm
    apply Quotient.forall_of_finChoice_eq hG
    rw [<-InS.cfg_q, cfg]
    congr
    funext i
    simp only [<-InS.vwk1_q]
    rw [InS.q]
    congr
    apply Eq.symm
    apply Quotient.forall_of_finChoice_eq hG

theorem InS.cfg_cfg_eqv_cfg' {Γ : Ctx α ε} {L : LCtx α}
  (R S : LCtx α) (β : InS φ Γ (R ++ (S ++ L)))
  (G : (i : Fin R.length) → InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ (S ++ L)))
  (G' : (i : Fin S.length) → InS φ (⟨S.get i, ⊥⟩::Γ) (S ++ L))
    : (β.cfg R G).cfg S G'
    ≈ (β.cast rfl (by rw [List.append_assoc])).cfg'
      (R.length + S.length) (R ++ S) (by rw [List.length_append])
      (Fin.addCases
        (λi => (G i).cast (by
          simp only [List.get_eq_getElem, Fin.cast, Fin.coe_castAdd]
          rw [List.getElem_append]
          -- TODO: put in discretion
          ) (by rw [List.append_assoc]))
        (λi => ((G' i).lwk (LCtx.InS.add_left_append (S ++ L) R)).cast (by
          simp only [List.get_eq_getElem, Fin.cast, Fin.coe_natAdd]
          -- TODO: put in discretion
          sorry
        )
          (by rw [List.append_assoc])))
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by
    simp only [Set.mem_setOf_eq, coe_cfg, id_eq, coe_cfg', coe_cast]
    apply Rewrite.cast_trg
    apply Rewrite.cfg_cfg
    congr
    funext i
    if h : i < R.length then
      have hi : i = Fin.castAdd S.length ⟨i, h⟩ := rfl
      rw [hi]
      simp only [Fin.addCases_left]
      rfl
    else
      let hi := Fin.natAdd_subNat_cast (le_of_not_lt h)
      rw [<-hi]
      simp only [Fin.addCases_right]
      rfl
    ))

-- theorem Eqv.cfg_eqv_cfg' {Γ : Ctx α ε} {L : LCtx α}
--   (R S : LCtx α) (β : Eqv φ Γ (R ++ (S ++ L)))
--   (G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ (S ++ L)))
--   (G' : (i : Fin S.length) → Eqv φ (⟨S.get i, ⊥⟩::Γ) (S ++ L))
--     : (β.cfg R G).cfg S G'
--     = (β.cast rfl (by rw [List.append_assoc])).cfg'
--       (R.length + S.length) (R ++ S) (by rw [List.length_append])
--       (Fin.addCases (λi => (G i).cast (by sorry) (by rw [List.append_assoc]))
--                     (λi => ((G' i).lwk (· + R.length) sorry).cast sorry
--                       (by rw [List.append_assoc]))
--       )
--   := sorry

theorem InS.cfg_zero {Γ : Ctx α ε} {L : LCtx α}
  (β : InS φ Γ L)
  : β.cfg [] (λi => i.elim0) ≈ β
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.cfg_zero {Γ : Ctx α ε} {L : LCtx α}
  (β : Eqv φ Γ L)
  : β.cfg [] (λi => i.elim0) = β
  := by induction β using Quotient.inductionOn with | h β => exact Eqv.sound $ β.cfg_zero

theorem InS.let2_eta {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨Ty.prod A B, ea⟩)
  (r : InS φ (⟨A.prod B, ⊥⟩::Γ) L)
    : (let2 a $
        let1 ((Term.InS.var 1 ⟨by simp, le_refl _⟩).pair (Term.InS.var 0 (by simp))) r.vwk1.vwk1)
    ≈ let1 a r
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.rw (by constructor))

theorem Eqv.let2_eta {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨Ty.prod A B, ea⟩)
  (r : Eqv φ (⟨A.prod B, ⊥⟩::Γ) L)
    : (let2 a $
        let1 ((Term.InS.var 1 ⟨by simp, le_refl _⟩).pair (Term.InS.var 0 (by simp))) r.vwk1.vwk1)
    = let1 a r
  := by induction r using Quotient.inductionOn with | h r => exact Eqv.sound $ InS.let2_eta a r

theorem InS.wk_cfg {Γ : Ctx α ε} {L : LCtx α}
  (R S : LCtx α) (β : InS φ Γ (R ++ L))
  (G : (i : Fin S.length) → InS φ ((List.get S i, ⊥)::Γ) (R ++ L))
  (ρ : Fin R.length → Fin S.length)
  (hρ : LCtx.Wkn (R ++ L) (S ++ L) (Fin.toNatWk ρ))
  : cfg S (β.lwk ⟨Fin.toNatWk ρ, hρ⟩) (λi => (G i).lwk ⟨Fin.toNatWk ρ, hρ⟩)
  ≈ cfg R β (λi => (G (ρ i)).vwk_id (Ctx.Wkn.id.toFinWk_id hρ i))
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.reduce (by constructor))

theorem Eqv.wk_cfg {Γ : Ctx α ε} {L : LCtx α}
  (R S : LCtx α) (β : Eqv φ Γ (R ++ L))
  (G : (i : Fin S.length) → Eqv φ ((List.get S i, ⊥)::Γ) (R ++ L))
  (ρ : Fin R.length → Fin S.length)
  (hρ : LCtx.Wkn (R ++ L) (S ++ L) (Fin.toNatWk ρ))
  : cfg S (β.lwk ⟨Fin.toNatWk ρ, hρ⟩) (λi => (G i).lwk ⟨Fin.toNatWk ρ, hρ⟩)
  = cfg R β (λi => (G (ρ i)).vwk_id (Ctx.Wkn.id.toFinWk_id hρ i))
  := by
  induction β using Quotient.inductionOn with
  | h β =>
    simp only [cfg]
    generalize hG : Quotient.finChoice G = G'
    induction G' using Quotient.inductionOn with
    | h G' =>
      have hG := Quotient.forall_of_finChoice_eq hG
      simp only [Set.mem_setOf_eq, lwk_quot, List.get_eq_getElem, hG, Fin.getElem_fin, vwk_id_quot,
        Quotient.finChoice_eq, Eqv.cfg_inner_quot]
      apply Eqv.sound
      apply InS.wk_cfg

theorem InS.case_inl {Γ : Ctx α ε} {L : LCtx α}
  (e : Term.InS φ Γ ⟨A, ea⟩)
  (r : InS φ (⟨A, ⊥⟩::Γ) L)
  (s : InS φ (⟨B, ⊥⟩::Γ) L)
    : case e.inl r s ≈ let1 e r
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.reduce (by constructor))

theorem Eqv.case_inl {Γ : Ctx α ε} {L : LCtx α}
  (e : Term.InS φ Γ ⟨A, ea⟩)
  (r : Eqv φ (⟨A, ⊥⟩::Γ) L)
  (s : Eqv φ (⟨B, ⊥⟩::Γ) L)
    : case e.inl r s = let1 e r
  := by
  induction r using Quotient.inductionOn
  induction s using Quotient.inductionOn
  case _ r s =>
  exact Eqv.sound (InS.case_inl e r s)

theorem InS.case_inr {Γ : Ctx α ε} {L : LCtx α}
  (e : Term.InS φ Γ ⟨B, ea⟩)
  (r : InS φ (⟨A, ⊥⟩::Γ) L)
  (s : InS φ (⟨B, ⊥⟩::Γ) L)
    : case e.inr r s ≈ let1 e s
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (FStep.reduce (by constructor))

theorem Eqv.case_inr {Γ : Ctx α ε} {L : LCtx α}
  (e : Term.InS φ Γ ⟨B, ea⟩)
  (r : Eqv φ (⟨A, ⊥⟩::Γ) L)
  (s : Eqv φ (⟨B, ⊥⟩::Γ) L)
    : case e.inr r s = let1 e s
  := by
  induction r using Quotient.inductionOn
  induction s using Quotient.inductionOn
  case _ r s =>
  exact Eqv.sound (InS.case_inr e r s)

theorem InS.dead_cfg_left {Γ : Ctx α ε} {L : LCtx α}
  (R S : LCtx α) (β : InS φ Γ (S ++ L))
  (G : (i : Fin R.length) → InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ S ++ L))
  (G' : (i : Fin S.length) → InS φ (⟨S.get i, ⊥⟩::Γ) (S ++ L))
  : (β.lwk ((LCtx.InS.add_left_append (S ++ L) R).cast rfl (by rw [List.append_assoc]))).cfg'
    (R.length + S.length) (R ++ S) (by rw [List.length_append])
      (Fin.addCases
        (λi => (G i).cast sorry rfl)
        (λi => ((G' i).cast sorry rfl).lwk
          ((LCtx.InS.add_left_append (S ++ L) R).cast rfl (by rw [List.append_assoc]))))
    ≈ β.cfg S G'
  := sorry

-- TODO: Eqv.dead_cfg_left; after Eqv.lwk

theorem InS.let1_beta {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨A, ⊥⟩)
  (r : InS φ (⟨A, ⊥⟩::Γ) L)
    : let1 a r ≈ r.vsubst a.subst0
  := EqvGen.rel _ _ $ Wf.Cong.rel $
  TStep.step InS.coe_wf InS.coe_wf (by
    constructor
    sorry
  )

theorem Eqv.let1_beta {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨A, ⊥⟩)
  (r : Eqv φ (⟨A, ⊥⟩::Γ) L)
    : let1 a r = r.vsubst a.subst0
  := by
  induction r using Quotient.inductionOn
  exact Eqv.sound (InS.let1_beta a _)

theorem InS.initial {Γ : Ctx α ε} {L : LCtx α} (hi : Γ.IsInitial) (r r' : InS φ Γ L) : r ≈ r'
  := EqvGen.rel _ _ $ Wf.Cong.rel (TStep.initial hi r.2 r'.2)

theorem Eqv.initial {Γ : Ctx α ε} {L : LCtx α} (hi : Γ.IsInitial) (r r' : Eqv φ Γ L) : r = r'
  := by
  induction r using Quotient.inductionOn
  induction r' using Quotient.inductionOn
  exact Eqv.sound (InS.initial hi _ _)

theorem InS.terminal {Γ : Ctx α ε} {L : LCtx α}
  (e e' : Term.InS φ Γ ⟨Ty.unit, ⊥⟩) (r : InS φ (⟨Ty.unit, ⊥⟩::Γ) L)
  : let1 e r ≈ let1 e' r
  := EqvGen.rel _ _ $ Wf.Cong.rel (TStep.terminal e.2 e'.2 r.2)

theorem Eqv.terminal {Γ : Ctx α ε} {L : LCtx α}
  (e e' : Term.InS φ Γ ⟨Ty.unit, ⊥⟩) (r : Eqv φ (⟨Ty.unit, ⊥⟩::Γ) L)
  : let1 e r = let1 e' r
  := by
  induction r using Quotient.inductionOn
  exact Eqv.sound (InS.terminal e e' _)

end Region

end BinSyntax
