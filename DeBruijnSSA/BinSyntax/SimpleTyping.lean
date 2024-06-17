import Discretion.Wk.List
import Discretion.Basic
import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Effect
import DeBruijnSSA.BinSyntax.Typing

namespace BinSyntax

variable [Φ: InstSet φ (Ty α)] [PartialOrder α] [PartialOrder ε] [Bot ε]

/-- A derivation that a term is well-formed -/
inductive Term.SWfD : List (Ty α) → Term φ → Ty α → Type _
  | var {A : Ty α} : Γ.get? n = some A → SWfD Γ (var n) A
  | op : Φ.Fn f A B → SWfD Γ a A → SWfD Γ (op f a) B
  | pair : SWfD Γ a A → SWfD Γ b B → SWfD Γ (pair a b) (Ty.prod A B)
  | inl : SWfD Γ a A → SWfD Γ (inl a) (Ty.coprod A B)
  | inr : SWfD Γ b B → SWfD Γ (inr b) (Ty.coprod A B)
  | abort : SWfD Γ a Ty.empty → SWfD Γ (abort a) A
  | unit : SWfD Γ unit Ty.unit

end BinSyntax
