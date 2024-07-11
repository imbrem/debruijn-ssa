import DeBruijnSSA.BinSyntax.Rewrite.Term.Eqv
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Seq
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Product
import DeBruijnSSA.BinSyntax.Typing.Term.Compose

import Discretion.Utils.Quotient


namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

def Eqv.coprod {A B C : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩) (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩)
  : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) ⟨C, e⟩ := case nil l.wk1 r.wk1

def Eqv.inj_l {A B : Ty α} {Γ : Ctx α ε} : Eqv (φ := φ) (⟨A, ⊥⟩::Γ) ⟨A.coprod B, e⟩
  := inl nil

def Eqv.inj_r {A B : Ty α} {Γ : Ctx α ε} : Eqv (φ := φ) (⟨B, ⊥⟩::Γ) ⟨A.coprod B, e⟩
  := inr nil

def Eqv.sum {A A' B B' : Ty α} {Γ : Ctx α ε}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A', e⟩) (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨B', e⟩)
  : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) ⟨A'.coprod B', e⟩ := coprod (l.seq inj_l) (r.seq inj_r)
