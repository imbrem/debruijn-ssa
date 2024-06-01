import Discretion.Wk.Order

import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.InstSet

namespace BinSyntax

variable [Φ : EffectSet φ ε] [Bot ε] [Sup ε]

/-- Infer the effect of a term -/
def Term.effect (Γ : ℕ → ε) : Term φ → ε
  | var n => Γ n
  | op f e => Φ.effect f ⊔ e.effect Γ
  | pair a b => a.effect Γ ⊔ b.effect Γ
  | inl a => a.effect Γ
  | inr b => b.effect Γ
  | abort e => e.effect Γ
  | unit => ⊥

/-- Infer the effect of a body -/
def Body.effect (Γ : ℕ → ε) : Body φ → ε
  | nil => ⊥
  | let1 e b => e.effect Γ ⊔ b.effect (Nat.liftBot Γ)
  | let2 e b => e.effect Γ ⊔ b.effect (Nat.liftnBot 2 Γ)

-- TODO: this is currently asserting that the arguments to `case` and `br` always have effect `⊥`!

/-- Infer the effect of a `BBRegion`, _without_ taking control-flow into account -/
def BBRegion.effect (Γ : ℕ → ε) : BBRegion φ → ε
  | cfg β _ G => β.body.effect Γ ⊔ Fin.sup (λi => (G i).effect (Nat.liftnBot β.body.num_defs Γ))

/-- Infer the effect of a `TRegion`, _without_ taking control-flow into account -/
def TRegion.effect (Γ : ℕ → ε) : TRegion φ → ε
  | let1 e r => e.effect Γ ⊔ r.effect (Nat.liftBot Γ)
  | let2 e r => e.effect Γ ⊔ r.effect (Nat.liftnBot 2 Γ)
  | cfg _ _ G => Fin.sup (λi => (G i).effect Γ)

/-- Infer the effect of a `Region`, _without_ taking control-flow into account -/
def Region.effect (Γ : ℕ → ε) : Region φ → ε
  | br _ _ => ⊥
  | let1 e r => e.effect Γ ⊔ r.effect (Nat.liftBot Γ)
  | let2 e r => e.effect Γ ⊔ r.effect (Nat.liftnBot 2 Γ)
  | case _ s t => s.effect Γ ⊔ t.effect Γ
  | cfg β _ G => β.effect Γ ⊔ Fin.sup (λi => (G i).effect Γ)

end BinSyntax
