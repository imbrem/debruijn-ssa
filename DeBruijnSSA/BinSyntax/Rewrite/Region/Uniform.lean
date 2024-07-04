import DeBruijnSSA.BinSyntax.Typing.Region.Basic
import DeBruijnSSA.BinSyntax.Syntax.Compose.Region
import DeBruijnSSA.BinSyntax.Syntax.Compose.Term

import Discretion.Utils.Quotient

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

inductive Uniform (P : Ctx α ε → LCtx α → Region φ → Region φ → Prop)
  : Ctx α ε → LCtx α → Region φ → Region φ → Prop
  | refl : ∀ x, Uniform P Γ L x x
  | symm : Uniform P Γ L x y → Uniform P Γ L y x
  | trans : Uniform P Γ L x y → Uniform P Γ L y z → Uniform P Γ L x z
  | uniform {e : Term φ} {r s : Region φ}
    : e.Wf (⟨A, ⊥⟩::Γ) (B, ⊥)
    → r.Wf (⟨B, ⊥⟩::Γ) ((C.coprod B)::L)
    → s.Wf (⟨A, ⊥⟩::Γ) ((C.coprod A)::L)
    → Uniform P (⟨A, ⊥⟩::Γ) ((C.coprod B)::L) (r.vsubst e.subst0) (s.lsubst (ret sorry).lsubst0)
    → Uniform P (⟨A, ⊥⟩::Γ) (C::L) r s
  | rel : P Γ L x y → Uniform P Γ L x y
