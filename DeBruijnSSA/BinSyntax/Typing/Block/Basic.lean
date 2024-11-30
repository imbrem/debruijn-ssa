import Discretion.Wk.List
import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Fv.Basic
import DeBruijnSSA.BinSyntax.Syntax.Effect.Definitions

import DeBruijnSSA.BinSyntax.Typing.Body.Basic
import DeBruijnSSA.BinSyntax.Typing.Terminator.Basic

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]

structure Block.WfD (Γ : Ctx α ε) (β : Block φ) (Δ : Ctx α ε) (L : LCtx α) where
  body : β.body.WfD Γ Δ
  terminator : β.terminator.WfD (Δ.reverse ++ Γ) L

structure Block.Wf (Γ : Ctx α ε) (β : Block φ) (Δ : Ctx α ε) (L : LCtx α) : Prop where
  body : β.body.Wf Γ Δ
  terminator : β.terminator.Wf (Δ.reverse ++ Γ) L

def Block.WfD.vwk {β : Block φ} (h : Γ.Wkn Δ ρ) (hβ : WfD Δ β Ξ L) : WfD Γ (β.vwk ρ) Ξ L where
  body := hβ.body.wk h
  terminator := hβ.terminator.vwk
    (hβ.body.num_defs_eq_length ▸ (h.liftn_append' (by simp [Ctx.reverse])))

def Block.WfD.vwk_id {β : Block φ} (h : Γ.Wkn Δ id) (hβ : WfD Δ β Ξ L) : WfD Γ β Ξ L where
  body := hβ.body.wk_id h
  terminator := hβ.terminator.vwk_id (h.liftn_append_id _)

def Block.WfD.lwk {β : Block φ} (h : L.Wkn K ρ) (hβ : WfD Γ β Ξ L) : WfD Γ (β.lwk ρ) Ξ K where
  body := hβ.body
  terminator := hβ.terminator.lwk h
