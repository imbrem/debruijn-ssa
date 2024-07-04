import Discretion.Wk.List
import Discretion.Basic
import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Fv.Basic
import DeBruijnSSA.BinSyntax.Syntax.Effect.Definitions

import DeBruijnSSA.BinSyntax.Typing.Ctx
import DeBruijnSSA.BinSyntax.Typing.LCtx
import DeBruijnSSA.BinSyntax.Typing.Term.Basic

namespace BinSyntax

section Basic

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]

inductive Terminator.WfD : Ctx α ε → Terminator φ → LCtx α → Type _
  | br : L.Trg n A → a.WfD Γ ⟨A, ⊥⟩ → WfD Γ (br n a) L
  | case : a.WfD Γ ⟨Ty.coprod A B, e⟩
    → s.WfD (⟨A, ⊥⟩::Γ) L
    → t.WfD (⟨B, ⊥⟩::Γ) L
    → WfD Γ (case a s t) L

inductive Terminator.Wf : Ctx α ε → Terminator φ → LCtx α → Prop
  | br : L.Trg n A → a.Wf Γ ⟨A, ⊥⟩ → Wf Γ (br n a) L
  | case : a.Wf Γ ⟨Ty.coprod A B, e⟩
    → s.Wf (⟨A, ⊥⟩::Γ) L
    → t.Wf (⟨B, ⊥⟩::Γ) L
    → Wf Γ (case a s t) L

def Terminator.WfD.vwk {Γ Δ : Ctx α ε} {ρ} {t : Terminator φ} (h : Γ.Wkn Δ ρ)
  : WfD Δ t L → WfD Γ (t.vwk ρ) L
  | br hL ha => br hL (ha.wk h)
  | case he hs ht => case (he.wk h) (hs.vwk h.slift) (ht.vwk h.slift)

def Terminator.WfD.vwk_id {Γ Δ : Ctx α ε} {t : Terminator φ} (h : Γ.Wkn Δ id)
  : WfD Δ t L → WfD Γ t L
  | br hL ha => br hL (ha.wk_id h)
  | case he hs ht => case (he.wk_id h) (hs.vwk_id h.slift_id) (ht.vwk_id h.slift_id)

def Terminator.WfD.lwk {Γ : Ctx α ε} {t : Terminator φ} (h : L.Wkn K ρ)
  : WfD Γ t L → WfD Γ (t.lwk ρ) K
  | br hL ha => br (hL.wk h) ha
  | case he hs ht => case he (hs.lwk h) (ht.lwk h)
