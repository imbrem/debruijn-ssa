import DeBruijnSSA.BinSyntax.Typing.Region
import DeBruijnSSA.BinSyntax.Syntax.Rewrite

import Discretion.Utils.Quotient

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

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
