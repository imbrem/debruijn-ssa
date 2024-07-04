import Discretion.Wk.List
import Discretion.Basic
import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Fv.Basic
import DeBruijnSSA.BinSyntax.Syntax.Effect.Definitions

import DeBruijnSSA.BinSyntax.Typing.Block

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]

inductive BBRegion.WfD : Ctx α ε → BBRegion φ → LCtx α → Type _
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.WfD Γ Δ (R ++ L) →
    (∀i : Fin n, (G i).WfD (⟨R.get (i.cast hR.symm), ⊥⟩::(Δ ++ Γ)) (R ++ L)) →
    WfD Γ (cfg β n G) L

inductive BBRegion.Wf : Ctx α ε → BBRegion φ → LCtx α → Prop
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.Wf Γ Δ (R ++ L) →
    (∀i : Fin n, (G i).Wf (⟨R.get (i.cast hR.symm), ⊥⟩::(Δ ++ Γ)) (R ++ L)) →
    Wf Γ (cfg β n G) L

def BBRegion.WfD.vwk {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} {L} {r : BBRegion φ} (h : Γ.Wkn Δ ρ)
  : WfD Δ r L → WfD Γ (r.vwk ρ) L
  | cfg n R hR hβ hG =>
    cfg n R hR (hβ.vwk h) (λi => (hG i).vwk (hβ.body.num_defs_eq_length ▸ h.liftn_append_cons _ _))

def BBRegion.WfD.vwk_id {Γ Δ : Ctx α ε} {L} {r : BBRegion φ} (h : Γ.Wkn Δ id)
  : WfD Δ r L → WfD Γ r L
  | cfg n R hR hβ hG =>
    cfg n R hR (hβ.vwk_id h) (λi => (hG i).vwk_id (h.liftn_append_cons_id _ _))

def BBRegion.WfD.lwk {Γ : Ctx α ε} {ρ : ℕ → ℕ} {L K : LCtx α} {r : BBRegion φ} (h : L.Wkn K ρ)
  : WfD Γ r L → WfD Γ (r.lwk ρ) K
  | cfg n R hR hβ hG =>
    have trg_wk : (R ++ L).Wkn (R ++ K) (Nat.liftnWk n ρ) := hR ▸ h.liftn_append R
    cfg n R hR (hβ.lwk trg_wk) (λi => (hG i).lwk trg_wk)
