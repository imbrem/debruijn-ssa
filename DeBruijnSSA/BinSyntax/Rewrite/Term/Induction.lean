import DeBruijnSSA.BinSyntax.Rewrite.Term.Eqv

import Discretion.Utils.Quotient

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

theorem Eqv.induction
  {motive : (Γ : Ctx α ε) → (V : Ty α × ε) → Eqv φ Γ V → Prop}
  (var : ∀{Γ V} (n) (hv : Γ.Var n V), motive Γ V (var n hv))
  (op : ∀{Γ A B e} (f a) (hf : Φ.EFn f A B e) (_ha : motive Γ ⟨A, e⟩ a),
    motive Γ ⟨B, e⟩ (op f hf a))
  (let1 : ∀{Γ A B e} (a b) (_ha : motive Γ ⟨A, e⟩ a) (_hb : motive (⟨A, ⊥⟩::Γ) ⟨B, e⟩ b),
    motive Γ ⟨B, e⟩ (let1 a b))
  (pair : ∀{Γ A B e} (a b) (_ha : motive Γ ⟨A, e⟩ a) (_hb : motive Γ ⟨B, e⟩ b),
    motive Γ ⟨Ty.prod A B, e⟩ (pair a b))
  (let2 : ∀{Γ A B C e} (a c)
    (_ha : motive Γ ⟨A.prod B, e⟩ a) (_hc : motive (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩ c),
    motive Γ ⟨C, e⟩ (let2 a c))
  (inl : ∀{Γ A B e} (a) (_ha : motive Γ ⟨A, e⟩ a), motive Γ ⟨Ty.coprod A B, e⟩ (inl a))
  (inr : ∀{Γ A B e} (b) (_hb : motive Γ ⟨B, e⟩ b), motive Γ ⟨Ty.coprod A B, e⟩ (inr b))
  (case : ∀{Γ A B C e} (a l r)
    (_ha : motive Γ ⟨Ty.coprod A B, e⟩ a)
    (_hl : motive (⟨A, ⊥⟩::Γ) ⟨C, e⟩ l)
    (_hr : motive (⟨B, ⊥⟩::Γ) ⟨C, e⟩ r),
    motive Γ ⟨C, e⟩ (case a l r))
  (abort : ∀{Γ A e} (a) (_ha : motive Γ ⟨Ty.empty, e⟩ a), motive Γ ⟨A, e⟩ (abort a A))
  (unit : ∀{Γ e}, motive Γ ⟨Ty.unit, e⟩ (unit e))
  (h : Eqv φ Γ V) : motive Γ V h := by induction h using Quotient.inductionOn with
  | h a => induction a using InS.induction with
  | var n hv => exact var n hv
  | op f a hf Ia => exact op f ⟦a⟧ hf Ia
  | let1 a b Ia Ib => exact let1 ⟦a⟧ ⟦b⟧ Ia Ib
  | pair a b Ia Ib => exact pair ⟦a⟧ ⟦b⟧ Ia Ib
  | let2 a c Ia Ic => exact let2 ⟦a⟧ ⟦c⟧ Ia Ic
  | inl a Ia => exact inl ⟦a⟧ Ia
  | inr b Ib => exact inr ⟦b⟧ Ib
  | case a l r Ia Il Ir => exact case ⟦a⟧ ⟦l⟧ ⟦r⟧ Ia Il Ir
  | abort a Ia => exact abort ⟦a⟧ Ia
  | unit => exact unit
