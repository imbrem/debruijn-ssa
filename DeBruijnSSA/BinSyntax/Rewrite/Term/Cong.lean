import DeBruijnSSA.BinSyntax.Typing.Term
import DeBruijnSSA.BinSyntax.Syntax.Rewrite

import Discretion.Utils.Quotient

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

inductive Wf.Cong (P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop)
  : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop
  | op : Φ.EFn f A B e → Cong P Γ (A, e) a a' → Cong P Γ (B, e) (Term.op f a) (Term.op f a')
  | let1_bound : Cong P Γ (A, e) a a' → Wf (⟨A, ⊥⟩::Γ) b (B, e)
    → Cong P Γ (B, e) (Term.let1 a b) (Term.let1 a' b)
  | let1_body : Wf Γ a (A, e) → Cong P (⟨A, ⊥⟩::Γ) (B, e) b b'
    → Cong P Γ (B, e) (Term.let1 a b) (Term.let1 a b')
  | pair_left : Cong P Γ (A, e) a a' → Wf Γ b (B, e)
    → Cong P Γ (A.prod B, e) (Term.pair a b) (Term.pair a' b)
  | pair_right : Wf Γ a (A, e) → Cong P Γ (B, e) b b'
    → Cong P Γ (A.prod B, e) (Term.pair a b) (Term.pair a b')
  | let2_bound : Cong P Γ (A.prod B, e) a a' → Wf (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) b (C, e)
    → Cong P Γ (C, e) (Term.let2 a b) (Term.let2 a' b)
  | let2_body : Wf Γ a (A.prod B, e) → Cong P (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) (C, e) b b'
    → Cong P Γ (C, e) (Term.let2 a b) (Term.let2 a b')
  | inl : Cong P Γ (A, e) a a' → Cong P Γ (Ty.coprod A B, e) (Term.inl a) (Term.inl a')
  | inr : Cong P Γ (B, e) b b' → Cong P Γ (Ty.coprod A B, e) (Term.inr b) (Term.inr b')
  | case_disc : Cong P Γ (Ty.coprod A B, e) a a' → Wf (⟨A, ⊥⟩::Γ) b (C, e) → Wf (⟨B, ⊥⟩::Γ) c (C, e)
    → Cong P Γ (C, e) (Term.case a b c) (Term.case a' b c)
  | case_left : Wf Γ a (Ty.coprod A B, e) → Cong P (⟨A, ⊥⟩::Γ) (C, e) b b' → Wf (⟨B, ⊥⟩::Γ) c (C, e)
    → Cong P Γ (C, e) (Term.case a b c) (Term.case a b' c)
  | case_right : Wf Γ a (Ty.coprod A B, e) → Wf (⟨A, ⊥⟩::Γ) b (C, e) → Cong P (⟨B, ⊥⟩::Γ) (C, e) c c'
    → Cong P Γ (C, e) (Term.case a b c) (Term.case a b c')
  | abort : Cong P Γ (Ty.empty, e) a a' → Cong P Γ (A, e) (Term.abort a) (Term.abort a')
  | rel : P Γ (A, e) a a' → Wf.Cong P Γ (A, e) a a'

theorem Wf.Cong.left {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ V a a'} (toLeft : ∀{Γ V a a'}, P Γ V a a' → Wf Γ a V) (h : Wf.Cong P Γ V a a')
  : Wf Γ a V := by induction h with
  | rel h => exact toLeft h
  | _ => constructor <;> assumption

theorem Wf.Cong.right {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ V a a'} (toRight : ∀{Γ V a a'}, P Γ V a a' → Wf Γ a' V) (h : Wf.Cong P Γ V a a')
  : Wf Γ a' V := by induction h with
  | rel h => exact toRight h
  | _ => constructor <;> assumption

-- TODO: vwk, lwk, lsubst, vsubst...

theorem Wf.Cong.eqv_iff {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop} {Γ V r r'}
  (toLeft : ∀{Γ V r r'}, P Γ V r r' → r.Wf Γ V)
  (toRight : ∀{Γ V r r'}, P Γ V r r' → r'.Wf Γ V)
  (p : EqvGen (Wf.Cong P Γ V) r r') : r.Wf Γ V ↔ r'.Wf Γ V
  := by induction p with
  | rel _ _ h => exact ⟨λ_ => h.right toRight, λ_ => h.left toLeft⟩
  | refl => rfl
  | symm _ _ _ I => exact I.symm
  | trans _ _ _ _ _ Il Ir => exact Il.trans Ir
