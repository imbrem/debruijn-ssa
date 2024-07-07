import DeBruijnSSA.BinSyntax.Typing.Term

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

theorem Wf.Cong.wf {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ V a a'} (toWf : ∀{Γ V a a'}, P Γ V a a' → Wf Γ a V ∧ Wf Γ a' V)
  (h : Wf.Cong P Γ V a a') : Wf Γ a V ∧ Wf Γ a' V
  := ⟨h.left (λh => (toWf h).1), h.right (λh => (toWf h).2)⟩

theorem Wf.Cong.map {P Q : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ V a a'} (f : ∀{Γ V a a'}, P Γ V a a' → Q Γ V a a') (h : Wf.Cong P Γ V a a')
  : Wf.Cong Q Γ V a a' := by induction h with
  | rel h => exact rel (f h)
  | _ => constructor <;> assumption

theorem Wf.Cong.flatten {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ V a a'} (h : Wf.Cong (Wf.Cong P) Γ V a a') : Wf.Cong P Γ V a a' := by induction h with
  | rel h => exact h
  | _ => constructor <;> assumption

theorem Wf.Cong.wk {P Q : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop} {Γ Δ L r r'}
  (toWk : ∀{Γ Δ V ρ r r'}, Γ.Wkn Δ ρ → P Δ V r r' → Q Γ V (r.wk ρ) (r'.wk ρ))
  (hρ : Γ.Wkn Δ ρ) (p : Wf.Cong P Δ L r r') : Wf.Cong Q Γ L (r.wk ρ) (r'.wk ρ)
  := by induction p with
  | rel h => exact rel $ toWk hρ h
  | _ => sorry

theorem Wf.Cong.wk_res {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop} {Γ V V' r r'}
  (toWk : ∀{Γ V V' r r'}, V ≤ V' → P Γ V r r' → P Γ V' r r')
  (hV : V ≤ V') (p : Cong P Γ V r r') : Cong P Γ V' r r'
  := by induction p with
  | rel h => exact rel $ toWk hV h
  | _ => sorry

theorem Wf.Cong.subst {P Q : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop} {Γ Δ L r r'}
  (toSubst : ∀{Γ Δ V σ r r'}, σ.Wf Γ Δ → P Δ V r r' → Q Γ V (r.subst σ) (r'.subst σ))
  (hσ : σ.Wf Γ Δ) (p : Wf.Cong P Δ L r r') : Wf.Cong Q Γ L (r.subst σ) (r'.subst σ)
  := by induction p with
  | rel h => exact rel $ toSubst hσ h
  | _ => sorry

theorem Wf.Cong.eqv_iff {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop} {Γ V r r'}
  (toLeft : ∀{Γ V r r'}, P Γ V r r' → r.Wf Γ V)
  (toRight : ∀{Γ V r r'}, P Γ V r r' → r'.Wf Γ V)
  (p : EqvGen (Wf.Cong P Γ V) r r') : r.Wf Γ V ↔ r'.Wf Γ V
  := by induction p with
  | rel _ _ h => exact ⟨λ_ => h.right toRight, λ_ => h.left toLeft⟩
  | refl => rfl
  | symm _ _ _ I => exact I.symm
  | trans _ _ _ _ _ Il Ir => exact Il.trans Ir

inductive Uniform (P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop)
  : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop
  | refl : r.Wf Γ V → Uniform P Γ V r r
  | cong : Wf.Cong P Γ V r r' → Uniform P Γ V r r'
  | symm : Uniform P Γ V x y → Uniform P Γ V y x
  | trans : Uniform P Γ V x y → Uniform P Γ V y z → Uniform P Γ V x z

theorem Uniform.cast_src {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ V} {r₀' r₀ r₁ : Term φ} (h : r₀' = r₀) (p : Uniform P Γ V r₀ r₁)
  : Uniform P Γ V r₀' r₁ := h ▸ p

theorem Uniform.cast_trg {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ V} {r₀ r₁' r₁ : Term φ} (p : Uniform P Γ V r₀ r₁) (h : r₁ = r₁')
  : Uniform P Γ V r₀ r₁' := h ▸ p

theorem Uniform.wf {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop} {Γ V r r'}
  (toWf : ∀{Γ V r r'}, P Γ V r r' → r.Wf Γ V ∧ r'.Wf Γ V)
  (p : Uniform P Γ V r r') : r.Wf Γ V ∧ r'.Wf Γ V
  := by induction p with
  | refl h => exact ⟨h, h⟩
  | cong h => exact h.wf toWf
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact ⟨Il.1, Ir.2⟩

theorem Uniform.op {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ f a a'} (hf : Φ.EFn f A B e) (h : Uniform P Γ ⟨A, e⟩ a a')
  : Uniform P Γ ⟨B, e⟩ (Term.op f a) (Term.op f a')
  := by induction h with
  | refl ha => exact refl (ha.op hf)
  | cong ha => exact cong (Wf.Cong.op hf ha)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.let1_bound {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ a a'} (h : Uniform P Γ ⟨A, e⟩ a a') (hb : b.Wf (⟨A, ⊥⟩::Γ) (B, e))
  : Uniform P Γ ⟨B, e⟩ (Term.let1 a b) (Term.let1 a' b)
  := by induction h with
  | refl ha => exact refl (ha.let1 hb)
  | cong ha => exact cong (Wf.Cong.let1_bound ha hb)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.let1_body {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ a} (ha : a.Wf Γ ⟨A, e⟩) (h : Uniform P (⟨A, ⊥⟩::Γ) ⟨B, e⟩ b b')
  : Uniform P Γ ⟨B, e⟩ (Term.let1 a b) (Term.let1 a b')
  := by induction h with
  | refl hb => exact refl (ha.let1 hb)
  | cong hb => exact cong (Wf.Cong.let1_body ha hb)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.pair_left {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ a a'} (h : Uniform P Γ ⟨A, e⟩ a a') (hb : b.Wf Γ ⟨B, e⟩)
  : Uniform P Γ ⟨A.prod B, e⟩ (Term.pair a b) (Term.pair a' b)
  := by induction h with
  | refl ha => exact refl (ha.pair hb)
  | cong ha => exact cong (Wf.Cong.pair_left ha hb)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.pair_right {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ b b'} (ha : a.Wf Γ ⟨A, e⟩) (h : Uniform P Γ ⟨B, e⟩ b b')
  : Uniform P Γ ⟨A.prod B, e⟩ (Term.pair a b) (Term.pair a b')
  := by induction h with
  | refl hb => exact refl (ha.pair hb)
  | cong hb => exact cong (Wf.Cong.pair_right ha hb)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.let2_bound {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ a a'} (h : Uniform P Γ ⟨A.prod B, e⟩ a a') (hb : b.Wf (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) (C, e))
  : Uniform P Γ ⟨C, e⟩ (Term.let2 a b) (Term.let2 a' b)
  := by induction h with
  | refl ha => exact refl (ha.let2 hb)
  | cong ha => exact cong (Wf.Cong.let2_bound ha hb)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.let2_body {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ a} (ha : a.Wf Γ ⟨A.prod B, e⟩) (h : Uniform P (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩ b b')
  : Uniform P Γ ⟨C, e⟩ (Term.let2 a b) (Term.let2 a b')
  := by induction h with
  | refl hb => exact refl (ha.let2 hb)
  | cong hb => exact cong (Wf.Cong.let2_body ha hb)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.inl {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ a a'} (h : Uniform P Γ ⟨A, e⟩ a a')
  : Uniform P Γ ⟨Ty.coprod A B, e⟩ (Term.inl a) (Term.inl a')
  := by induction h with
  | refl ha => exact refl (ha.inl)
  | cong ha => exact cong (Wf.Cong.inl ha)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.inr {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ b b'} (h : Uniform P Γ ⟨B, e⟩ b b')
  : Uniform P Γ ⟨Ty.coprod A B, e⟩ (Term.inr b) (Term.inr b')
  := by induction h with
  | refl hb => exact refl (hb.inr)
  | cong hb => exact cong (Wf.Cong.inr hb)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.case_disc {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ a a'} (h : Uniform P Γ ⟨Ty.coprod A B, e⟩ a a') (hb : b.Wf (⟨A, ⊥⟩::Γ) (C, e))
  (hc : c.Wf (⟨B, ⊥⟩::Γ) (C, e))
  : Uniform P Γ ⟨C, e⟩ (Term.case a b c) (Term.case a' b c)
  := by induction h with
  | refl ha => exact refl (ha.case hb hc)
  | cong ha => exact cong (Wf.Cong.case_disc ha hb hc)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.case_left {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ a} (ha : a.Wf Γ ⟨Ty.coprod A B, e⟩) (h : Uniform P (⟨A, ⊥⟩::Γ) ⟨C, e⟩ b b')
  (hc : c.Wf (⟨B, ⊥⟩::Γ) (C, e))
  : Uniform P Γ ⟨C, e⟩ (Term.case a b c) (Term.case a b' c)
  := by induction h with
  | refl hb => exact refl (ha.case hb hc)
  | cong hb => exact cong (Wf.Cong.case_left ha hb hc)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.case_right {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ a} (ha : a.Wf Γ ⟨Ty.coprod A B, e⟩) (hb : b.Wf (⟨A, ⊥⟩::Γ) (C, e))
  (h : Uniform P (⟨B, ⊥⟩::Γ) ⟨C, e⟩ c c')
  : Uniform P Γ ⟨C, e⟩ (Term.case a b c) (Term.case a b c')
  := by induction h with
  | refl hc => exact refl (ha.case hb hc)
  | cong hc => exact cong (Wf.Cong.case_right ha hb hc)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.abort {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ a a'} (h : Uniform P Γ ⟨Ty.empty, e⟩ a a')
  : Uniform P Γ ⟨A, e⟩ (Term.abort a) (Term.abort a')
  := by induction h with
  | refl ha => exact refl (ha.abort)
  | cong ha => exact cong (Wf.Cong.abort ha)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.rel {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ V r r'} (h : P Γ V r r')
  : Uniform P Γ V r r' := cong $ Wf.Cong.rel h

theorem Uniform.left {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ V r r'} (toWf : ∀{Γ V r r'}, P Γ V r r' → r.Wf Γ V ∧ r'.Wf Γ V) (h : Uniform P Γ V r r')
  : r.Wf Γ V := (h.wf toWf).1

theorem Uniform.right {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ V r r'} (toWf : ∀{Γ V r r'}, P Γ V r r' → r.Wf Γ V ∧ r'.Wf Γ V) (h : Uniform P Γ V r r')
  : r'.Wf Γ V := (h.wf toWf).2

theorem Uniform.map {P Q : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ V r r'} (f : ∀{Γ V r r'}, P Γ V r r' → Q Γ V r r') (h : Uniform P Γ V r r')
  : Uniform Q Γ V r r' := by induction h with
  | refl h => exact refl h
  | cong h => exact cong (h.map f)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Wf.Cong.flatten_uniform {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ V a a'} (h : Wf.Cong (Uniform P) Γ V a a')
  : Uniform P Γ V a a' := by induction h with
  | op => apply Uniform.op <;> assumption
  | let1_bound => apply Uniform.let1_bound <;> assumption
  | let1_body => apply Uniform.let1_body <;> assumption
  | pair_left => apply Uniform.pair_left <;> assumption
  | pair_right => apply Uniform.pair_right <;> assumption
  | let2_bound => apply Uniform.let2_bound <;> assumption
  | let2_body => apply Uniform.let2_body <;> assumption
  | inl => apply Uniform.inl ; assumption
  | inr => apply Uniform.inr ; assumption
  | case_disc => apply Uniform.case_disc <;> assumption
  | case_left => apply Uniform.case_left <;> assumption
  | case_right => apply Uniform.case_right <;> assumption
  | abort => apply Uniform.abort ; assumption
  | rel h => exact h

theorem Uniform.flatten {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop}
  {Γ V r r'} (h : Uniform (Uniform P) Γ V r r') : Uniform P Γ V r r' := by induction h with
  | refl h => exact refl h
  | cong h => exact h.flatten_uniform
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.wk {P Q : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop} {Γ Δ V ρ r r'}
  (toWk : ∀{Γ Δ V ρ r r'}, Γ.Wkn Δ ρ → P Δ V r r' → Q Γ V (r.wk ρ) (r'.wk ρ))
  (hρ : Γ.Wkn Δ ρ) (p : Uniform P Δ V r r') : Uniform Q Γ V (r.wk ρ) (r'.wk ρ)
  := by induction p with
  | refl h => exact refl (h.wk hρ)
  | cong h => exact cong (h.wk toWk hρ)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.wk_res {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop} {Γ V V' r r'}
  (toWk : ∀{Γ V V' r r'}, V ≤ V' → P Γ V r r' → P Γ V' r r')
  (hV : V ≤ V') (p : Uniform P Γ V r r') : Uniform P Γ V' r r'
  := by induction p with
  | refl h => exact refl (h.wk_res hV)
  | cong h => exact cong (h.wk_res toWk hV)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.subst {P Q : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop} {Γ Δ V σ r r'}
  (toSubst : ∀{Γ Δ V σ r r'}, σ.Wf Γ Δ → P Δ V r r' → Q Γ V (r.subst σ) (r'.subst σ))
  (hσ : σ.Wf Γ Δ) (p : Uniform P Δ V r r') : Uniform Q Γ V (r.subst σ) (r'.subst σ)
  := by induction p with
  | refl h => exact refl (h.subst hσ)
  | cong h => exact cong (h.subst toSubst hσ)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir

theorem Uniform.subst_flatten {P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop} {Γ Δ V σ r r'}
  (toSubst : ∀{Γ Δ V σ r r'}, σ.Wf Γ Δ → P Δ V r r' → Uniform P Γ V (r.subst σ) (r'.subst σ))
  (hσ : σ.Wf Γ Δ) (p : Uniform P Δ V r r') : Uniform P Γ V (r.subst σ) (r'.subst σ)
  := (p.subst (Q := Uniform P) toSubst hσ).flatten

def Uniform.Setoid (P : Ctx α ε → Ty α × ε → Term φ → Term φ → Prop)
  (Γ : Ctx α ε) (V : Ty α × ε) : Setoid (InS φ Γ V) where
  r x y := Uniform P Γ V x y
  iseqv := {
    refl := λx => refl x.prop
    symm := Uniform.symm
    trans := Uniform.trans
  }
