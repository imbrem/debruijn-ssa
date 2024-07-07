import DeBruijnSSA.BinSyntax.Typing.Region
import DeBruijnSSA.BinSyntax.Syntax.Rewrite.Region.Step
import DeBruijnSSA.BinSyntax.Rewrite.Region.Cong

import Discretion.Utils.Quotient

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

-- TODO: rewrite to use subst.cons...

-- def Term.WfD.subst₂ {Γ : Ctx α ε} {a b : Term φ}
--   (ha : a.WfD Γ ⟨A, e⟩) (hb : b.WfD Γ ⟨B, e'⟩)
--   : (a.subst₂ b).WfD Γ (⟨A, e⟩::⟨B, e'⟩::Γ)
--   | ⟨0, _⟩ => ha
--   | ⟨1, _⟩ => hb
--   | ⟨n + 2, h⟩ => var ⟨by simp at h; exact h, le_refl _⟩

namespace Region

structure HaveTrg (Γ : Ctx α ε) (L : LCtx α) (r r' : Region φ) where
  left : r.WfD Γ L
  right : r'.WfD Γ L

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

-- inductive TStepD : (Γ : Ctx α ε) → (L : LCtx α) → (r r' : Region φ) → Type _
--   -- TODO: do we need to require r.WfD for rw?
--   | step {Γ L r r'} : r.WfD Γ L → r'.WfD Γ L → FStepD Γ.effect r r' → TStepD Γ L r r'
--   | initial {Γ L} : Γ.IsInitial → r.WfD Γ L → r'.WfD Γ L → TStepD Γ L r r'
--   | terminal {Γ L} : e.WfD Γ ⟨Ty.unit, ⊥⟩ → e'.WfD Γ ⟨Ty.unit, ⊥⟩ → r.WfD (⟨Ty.unit, ⊥⟩::Γ) L
--     → TStepD Γ L (let1 e r) (let1 e' r)

inductive TStep : (Γ : Ctx α ε) → (L : LCtx α) → (r r' : Region φ) → Prop
  | let1_beta {e r} : e.Wf Γ ⟨A, ⊥⟩ → r.Wf (⟨A, ⊥⟩::Γ) L
    → TStep Γ L (let1 e r) (r.vsubst e.subst0)
  | rewrite {Γ L r r'} : r.Wf Γ L → r'.Wf Γ L → Rewrite r r' → TStep Γ L r r'
  | reduce {Γ L r r'} : r.Wf Γ L → r'.Wf Γ L → Reduce r r' → TStep Γ L r r'
  | initial {Γ L} : Γ.IsInitial → r.Wf Γ L → r'.Wf Γ L → TStep Γ L r r'
  | terminal {Γ L} : e.Wf Γ ⟨Ty.unit, ⊥⟩ → e'.Wf Γ ⟨Ty.unit, ⊥⟩ → r.Wf (⟨Ty.unit, ⊥⟩::Γ) L
    → TStep Γ L (let1 e r) (let1 e' r)

theorem TStep.left {Γ L} {r r' : Region φ} : TStep Γ L r r' → r.Wf Γ L
  | let1_beta de dr => dr.let1 de
  | rewrite d _ _ => d
  | reduce d _ _ => d
  | initial _ d _ => d
  | terminal de _ dr => dr.let1 de

theorem TStep.right {Γ L} {r r' : Region φ} : TStep Γ L r r' → r'.Wf Γ L
  | let1_beta de dr => dr.vsubst de.subst0
  | rewrite _ d _ => d
  | reduce _ d _ => d
  | initial _ _ d => d
  | terminal _ de dr => dr.let1 de

theorem TStep.cast_src {Γ L} {r₀' r₀ r₁ : Region φ} (h : r₀' = r₀) (p : TStep Γ L r₀ r₁)
  : TStep Γ L r₀' r₁ := h ▸ p

theorem TStep.cast_trg {Γ L} {r₀ r₁' r₁ : Region φ} (p : TStep Γ L r₀ r₁) (h : r₁ = r₁')
  : TStep Γ L r₀ r₁' := h ▸ p

theorem TStep.wf {Γ L} {r r' : Region φ} (h : TStep Γ L r r') : r.Wf Γ L ∧ r'.Wf Γ L
  := ⟨left h, right h⟩

theorem TStep.vwk {Γ Δ : Ctx α ε} {L r r' ρ} (hρ : Γ.Wkn Δ ρ)
  : TStep (φ := φ) Δ L r r' → TStep Γ L (r.vwk ρ) (r'.vwk ρ)
  | let1_beta de dr => (let1_beta (de.wk hρ) (dr.vwk hρ.slift)).cast_trg
    (by simp [vsubst_subst0_vwk])
  | rewrite d d' p => rewrite (d.vwk hρ) (d'.vwk hρ) (p.vwk ρ)
  | reduce d d' p => reduce (d.vwk hρ) (d'.vwk hρ) (p.vwk ρ)
  | initial di d d' => initial (di.wk hρ) (d.vwk hρ) (d'.vwk hρ)
  | terminal de de' dr => terminal (de.wk hρ) (de'.wk hρ) (dr.vwk hρ.slift)

theorem TStep.lwk {Γ : Ctx α ε} {L K r r' ρ} (hρ : L.Wkn K ρ)
  : TStep (φ := φ) Γ L r r' → TStep Γ K (r.lwk ρ) (r'.lwk ρ)
  | let1_beta de dr => (let1_beta de (dr.lwk hρ)).cast_trg (by simp [lwk_vsubst])
  | rewrite d d' p => rewrite (d.lwk hρ) (d'.lwk hρ) (p.lwk ρ)
  | reduce d d' p => reduce (d.lwk hρ) (d'.lwk hρ) (p.lwk ρ)
  | initial di d d' => initial di (d.lwk hρ) (d'.lwk hρ)
  | terminal de de' dr => terminal de de' (dr.lwk hρ)

-- Note: vsubst needs InS lore for initiality, so that's in Setoid.lean

theorem TStep.lsubst {Γ : Ctx α ε} {L K} {r r' : Region φ} {σ : Subst φ}
  (hσ : σ.Wf Γ L K) : (h : TStep Γ L r r') → TStep Γ K (r.lsubst σ) (r'.lsubst σ)
  | let1_beta de dr => (let1_beta de (dr.lsubst hσ.vlift)).cast_trg sorry
  | rewrite d d' p => sorry--rewrite (d.lsubst hσ) (d'.lsubst hσ) (p.lsubst σ)
  | reduce d d' p => sorry
  | initial di d d' => initial di (d.lsubst hσ) (d'.lsubst hσ)
  | terminal de de' dr => terminal de de' (dr.lsubst hσ.vlift)

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
