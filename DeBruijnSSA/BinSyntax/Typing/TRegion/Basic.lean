import Discretion.Wk.List
import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Fv.Basic
import DeBruijnSSA.BinSyntax.Syntax.Effect.Definitions

import DeBruijnSSA.BinSyntax.Typing.Terminator.Basic

namespace BinSyntax

section Basic

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]

inductive TRegion.WfD : Ctx α ε → TRegion φ → LCtx α → Type _
  | let1 : a.WfD Γ ⟨A, e⟩ → t.WfD (⟨A, ⊥⟩::Γ) L → (let1 a t).WfD Γ L
  | let2 : a.WfD Γ ⟨(Ty.prod A B), e⟩ → t.WfD (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L → (let2 a t).WfD Γ L
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.WfD Γ (R ++ L) →
    (∀i : Fin n, (G i).WfD (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    WfD Γ (cfg β n G) L

inductive TRegion.Wf : Ctx α ε → TRegion φ → LCtx α → Prop
  | let1 : a.Wf Γ ⟨A, e⟩ → t.Wf (⟨A, ⊥⟩::Γ) L → (let1 a t).Wf Γ L
  | let2 : a.Wf Γ ⟨(Ty.prod A B), e⟩ → t.Wf (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L → (let2 a t).Wf Γ L
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.Wf Γ (R ++ L) →
    (∀i : Fin n, (G i).Wf (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    Wf Γ (cfg β n G) L

def TRegion.WfD.vwk {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} {L} {r : TRegion φ} (h : Γ.Wkn Δ ρ)
  : WfD Δ r L → WfD Γ (r.vwk ρ) L
  | let1 ha ht => let1 (ha.wk h) (ht.vwk h.slift)
  | let2 ha ht => let2 (ha.wk h) (ht.vwk h.sliftn₂)
  | cfg n R hR hr hG => cfg n R hR (hr.vwk h) (λi => (hG i).vwk h.slift)

def TRegion.WfD.vwk_id {Γ Δ : Ctx α ε} {L} {r : TRegion φ} (h : Γ.Wkn Δ id)
  : WfD Δ r L → WfD Γ r L
  | let1 ha ht => let1 (ha.wk_id h) (ht.vwk_id h.slift_id)
  | let2 ha ht => let2 (ha.wk_id h) (ht.vwk_id (h.slift_id₂ _ _))
  | cfg n R hR hr hG => cfg n R hR (hr.vwk_id h) (λi => (hG i).vwk_id h.slift_id)

def TRegion.WfD.lwk {Γ : Ctx α ε} {ρ : ℕ → ℕ} {L K : LCtx α} {r : TRegion φ} (h : L.Wkn K ρ)
  : WfD Γ r L → WfD Γ (r.lwk ρ) K
  | let1 ha ht => let1 ha (ht.lwk h)
  | let2 ha ht => let2 ha (ht.lwk h)
  | cfg n R hR hr hG =>
    have trg_wk : (R ++ L).Wkn (R ++ K) (Nat.liftnWk n ρ) := hR ▸ h.liftn_append R
    cfg n R hR (hr.lwk trg_wk) (λi => (hG i).lwk trg_wk)
