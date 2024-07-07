import DeBruijnSSA.BinSyntax.Rewrite.Term.Setoid

import Discretion.Utils.Quotient

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

section Basic

variable {Γ : Ctx α ε} {V : Ty α × ε} {A B A' B' : Ty α}

def Eqv (φ) [EffInstSet φ (Ty α) ε] (Γ : Ctx α ε) (V : Ty α × ε)
  := Quotient (α := InS φ Γ V) inferInstance

def InS.q (r : InS φ Γ V) : Eqv φ Γ V := ⟦r⟧

theorem Eqv.inductionOn {motive : Eqv φ Γ V → Prop}(r : Eqv φ Γ V) (h : ∀a, motive (InS.q a))
  : motive r := Quotient.inductionOn r h

theorem Eqv.sound {a a' : InS φ Γ V} (h : a ≈ a') : InS.q a = InS.q a' := Quotient.sound h

theorem Eqv.eq {a a' : InS φ Γ V} : a.q = a'.q ↔ a ≈ a' := Quotient.eq

def Eqv.var (n : ℕ) (hn : Γ.Var n V) : Eqv φ Γ V := ⟦InS.var n hn⟧

def Eqv.op (f : φ) (hf : Φ.EFn f A B e) (a : Eqv φ Γ ⟨A, e⟩) : Eqv φ Γ ⟨B, e⟩
  := Quotient.liftOn a (λa => ⟦InS.op f hf a⟧) (λ_ _ h => sound $ InS.op_congr hf h)

@[simp]
theorem Eqv.op_quot {f : φ} {hf : Φ.EFn f A B e} {a : InS φ Γ ⟨A, e⟩}
  : op f hf ⟦a⟧ = ⟦InS.op f hf a⟧ := rfl

def Eqv.let1 (a : Eqv φ Γ ⟨A, e⟩) (b : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩) : Eqv φ Γ ⟨B, e⟩
  := Quotient.liftOn₂ a b (λa b => ⟦InS.let1 a b⟧) (λ_ _ _ _ h h' => sound $ InS.let1_congr h h')

@[simp]
theorem Eqv.let1_quot {a : InS φ Γ ⟨A, e⟩} {b : InS φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  : let1 ⟦a⟧ ⟦b⟧ = ⟦InS.let1 a b⟧ := rfl

def Eqv.pair (a : Eqv φ Γ ⟨A, e⟩) (b : Eqv φ Γ ⟨B, e⟩) : Eqv φ Γ ⟨Ty.prod A B, e⟩
  := Quotient.liftOn₂ a b (λa b => ⟦InS.pair a b⟧) (λ_ _ _ _ h h' => sound $ InS.pair_congr h h')

@[simp]
theorem Eqv.pair_quot {a : InS φ Γ ⟨A, e⟩} {b : InS φ Γ ⟨B, e⟩} : pair ⟦a⟧ ⟦b⟧ = ⟦InS.pair a b⟧
  := rfl

def Eqv.let2 (a : Eqv φ Γ ⟨Ty.prod A B, e⟩) (b : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩) : Eqv φ Γ ⟨C, e⟩
  := Quotient.liftOn₂ a b (λa b => ⟦InS.let2 a b⟧) (λ_ _ _ _ h h' => sound $ InS.let2_congr h h')

@[simp]
theorem Eqv.let2_quot {a : InS φ Γ ⟨Ty.prod A B, e⟩} {b : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : Eqv.let2 ⟦a⟧ ⟦b⟧ = ⟦InS.let2 a b⟧ := rfl

def Eqv.inl (a : Eqv φ Γ ⟨A, e⟩) : Eqv φ Γ ⟨Ty.coprod A B, e⟩
  := Quotient.liftOn a (λa => ⟦InS.inl a⟧) (λ_ _ h => sound $ InS.inl_congr h)

@[simp]
theorem Eqv.inl_quot {a : InS φ Γ ⟨A, e⟩} : inl (B := B) ⟦a⟧ = ⟦InS.inl a⟧ := rfl

def Eqv.inr (a : Eqv φ Γ ⟨B, e⟩) : Eqv φ Γ ⟨Ty.coprod A B, e⟩
  := Quotient.liftOn a (λa => ⟦InS.inr a⟧) (λ_ _ h => sound $ InS.inr_congr h)

@[simp]
theorem Eqv.inr_quot {a : InS φ Γ ⟨B, e⟩} : inr (A := A) ⟦a⟧ = ⟦InS.inr a⟧ := rfl

def Eqv.case (a : Eqv φ Γ ⟨Ty.coprod A B, e⟩)
  (l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩)
  (r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩) : Eqv φ Γ ⟨C, e⟩
  := Quotient.liftOn a (λa =>
    Quotient.liftOn₂ l r (λl r => ⟦InS.case a l r⟧) (λ_ _ _ _ h h' => sound
      $ Setoid.trans (InS.case_left_congr _ h _) (InS.case_right_congr _ _ h')))
    (λa a' h => by
      induction l using Quotient.inductionOn
      induction r using Quotient.inductionOn
      exact sound $ InS.case_disc_congr h _ _
    )

@[simp]
theorem Eqv.case_quot {a : InS φ Γ ⟨Ty.coprod A B, e⟩}
  {l : InS φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : InS φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case ⟦a⟧ ⟦l⟧ ⟦r⟧ = ⟦InS.case a l r⟧ := rfl

def Eqv.abort (a : Eqv φ Γ ⟨Ty.empty, e⟩) (A) : Eqv φ Γ ⟨A, e⟩
  := Quotient.liftOn a (λa => ⟦InS.abort a A⟧) (λ_ _ h => sound $ InS.abort_congr h)

@[simp]
theorem Eqv.abort_quot {a : InS φ Γ ⟨Ty.empty, e⟩} {A} : abort ⟦a⟧ A = ⟦InS.abort a A⟧ := rfl

def Eqv.unit (e) : Eqv φ Γ ⟨Ty.unit, e⟩ := ⟦InS.unit e⟧

@[simp]
theorem Eqv.unit_quot {e} : Eqv.unit (φ := φ) (Γ := Γ) e = ⟦InS.unit e⟧ := rfl

def Eqv.wk (ρ : Γ.InS Δ) (a : Eqv φ Δ V) : Eqv φ Γ V
  := Quotient.liftOn a (λa => ⟦a.wk ρ⟧) (λ_ _ h => sound $ InS.wk_congr_right ρ h)

@[simp]
theorem Eqv.wk_var {ρ : Γ.InS Δ} {n : ℕ} {hn : Δ.Var n V}
  : wk ρ (var n hn) = var (φ := φ) (ρ.val n) (hn.wk ρ.prop) := rfl

@[simp]
theorem Eqv.wk_op {ρ : Γ.InS Δ} {f : φ} {hf : Φ.EFn f A B e} {a : Eqv φ Δ ⟨A, e⟩}
  : wk ρ (op f hf a) = op f hf (a.wk ρ) := by
  induction a using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_let1 {ρ : Γ.InS Δ} {a : Eqv φ Δ ⟨A, e⟩} {b : Eqv φ (⟨A, ⊥⟩::Δ) ⟨B, e⟩}
  : wk ρ (let1 a b) = let1 (a.wk ρ) (b.wk (ρ.lift (le_refl _))) := by
  induction a using Quotient.inductionOn;
  induction b using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_pair {ρ : Γ.InS Δ} {a : Eqv φ Δ ⟨A, e⟩} {b : Eqv φ Δ ⟨B, e⟩}
  : wk ρ (pair a b) = pair (a.wk ρ) (b.wk ρ) := by
  induction a using Quotient.inductionOn;
  induction b using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_let2 {ρ : Γ.InS Δ} {a : Eqv φ Δ ⟨Ty.prod A B, e⟩}
  {b : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Δ) ⟨C, e⟩}
  : wk ρ (let2 a b) = let2 (a.wk ρ) (b.wk (ρ.liftn₂ (le_refl _) (le_refl _))) := by
  induction a using Quotient.inductionOn;
  induction b using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_inl {ρ : Γ.InS Δ} {a : Eqv φ Δ ⟨A, e⟩}
  : wk ρ (inl (B := B) a) = inl (a.wk ρ) := by
  induction a using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_inr {ρ : Γ.InS Δ} {a : Eqv φ Δ ⟨B, e⟩}
  : wk ρ (inr (A := A) a) = inr (a.wk ρ) := by
  induction a using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_case {ρ : Γ.InS Δ} {a : Eqv φ Δ ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Δ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Δ) ⟨C, e⟩}
  : wk ρ (case a l r) = case (a.wk ρ) (l.wk (ρ.lift (le_refl _))) (r.wk (ρ.lift (le_refl _))) := by
  induction a using Quotient.inductionOn;
  induction l using Quotient.inductionOn;
  induction r using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_abort {ρ : Γ.InS Δ} {a : Eqv φ Δ ⟨Ty.empty, e⟩} {A}
  : wk ρ (abort a A) = abort (a.wk ρ) A := by
  induction a using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_unit {ρ : Γ.InS Δ} {e}
  : wk ρ (unit (φ := φ) e) = unit e := rfl

@[simp]
theorem Eqv.wk_quot {ρ : Γ.InS Δ} {a : InS φ Δ V} : wk ρ ⟦a⟧ = ⟦a.wk ρ⟧ := rfl

-- TODO: "inductive simps" for wk

def Subst.Eqv (φ) [EffInstSet φ (Ty α) ε] (Γ Δ : Ctx α ε)
  := Quotient (α := Subst.InS φ Γ Δ) inferInstance

def Subst.InS.q (σ : Subst.InS φ Γ Δ) : Subst.Eqv φ Γ Δ := ⟦σ⟧

def Subst.Eqv.sound {σ σ' : Subst.InS φ Γ Δ} (h : σ ≈ σ')
  : Subst.InS.q σ = Subst.InS.q σ' := Quotient.sound h

def Subst.Eqv.lift (h : lo ≤ hi) (σ : Eqv φ Γ Δ) : Eqv φ (lo::Γ) (hi::Δ)
  := Quotient.liftOn σ (λσ => ⟦σ.lift h⟧) (λ_ _ h' => sound $ Subst.InS.lift_congr h h')

def Subst.Eqv.liftn₂ (h₁ : lo₁ ≤ hi₁) (h₂ : lo₂ ≤ hi₂)
  (σ : Eqv φ Γ Δ) : Eqv φ (lo₁::lo₂::Γ) (hi₁::hi₂::Δ)
  := Quotient.liftOn σ (λσ => ⟦σ.liftn₂ h₁ h₂⟧) (λ_ _ h' => sound $ sorry)

def Eqv.subst (σ : Subst.Eqv φ Γ Δ) (a : Eqv φ Δ V) : Eqv φ Γ V
  := Quotient.liftOn₂ σ a (λσ a => ⟦a.subst σ⟧) (λ_ _ _ _ h h' => sound $ InS.subst_congr h h')

@[simp]
theorem Eqv.subst_quot {σ : Subst.InS φ Γ Δ} {a : InS φ Δ V} : subst ⟦σ⟧ ⟦a⟧ = ⟦a.subst σ⟧ := rfl

-- TODO: subst_var lore

@[simp]
theorem Eqv.subst_op {σ : Subst.Eqv φ Γ Δ} {a : Eqv φ Δ ⟨A, e⟩} {f : φ} {hf : Φ.EFn f A B e}
  : subst σ (op f hf a) = op f hf (subst σ a) := by
  induction a using Quotient.inductionOn;
  induction σ using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.subst_let1 {σ : Subst.Eqv φ Γ Δ} {a : Eqv φ Δ ⟨A, e⟩} {b : Eqv φ (⟨A, ⊥⟩::Δ) ⟨B, e⟩}
  : subst σ (let1 a b) = let1 (subst σ a) (subst (σ.lift (le_refl _)) b) := by
  induction a using Quotient.inductionOn;
  induction b using Quotient.inductionOn;
  induction σ using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.subst_pair {σ : Subst.Eqv φ Γ Δ} {a : Eqv φ Δ ⟨A, e⟩} {b : Eqv φ Δ ⟨B, e⟩}
  : subst σ (pair a b) = pair (subst σ a) (subst σ b) := by
  induction a using Quotient.inductionOn;
  induction b using Quotient.inductionOn;
  induction σ using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.subst_let2 {σ : Subst.Eqv φ Γ Δ} {a : Eqv φ Δ ⟨Ty.prod A B, e⟩}
  {b : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Δ) ⟨C, e⟩}
  : subst σ (let2 a b) = let2 (subst σ a) (subst (σ.liftn₂ (le_refl _) (le_refl _)) b) := by
  induction a using Quotient.inductionOn;
  induction b using Quotient.inductionOn;
  induction σ using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.subst_inl {σ : Subst.Eqv φ Γ Δ} {a : Eqv φ Δ ⟨A, e⟩}
  : subst σ (inl (B := B) a) = inl (subst σ a) := by
  induction a using Quotient.inductionOn;
  induction σ using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.subst_inr {σ : Subst.Eqv φ Γ Δ} {a : Eqv φ Δ ⟨B, e⟩}
  : subst σ (inr (A := A) a) = inr (subst σ a) := by
  induction a using Quotient.inductionOn;
  induction σ using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.subst_case {σ : Subst.Eqv φ Γ Δ} {a : Eqv φ Δ ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Δ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Δ) ⟨C, e⟩}
  : subst σ (case a l r) = case (subst σ a) (subst (σ.lift (le_refl _)) l) (subst (σ.lift (le_refl _)) r) := by
  induction a using Quotient.inductionOn;
  induction l using Quotient.inductionOn;
  induction r using Quotient.inductionOn;
  induction σ using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.subst_abort {σ : Subst.Eqv φ Γ Δ} {a : Eqv φ Δ ⟨Ty.empty, e⟩} {A}
  : subst σ (abort a A) = abort (subst σ a) A := by
  induction a using Quotient.inductionOn;
  induction σ using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.subst_unit {σ : Subst.Eqv φ Γ Δ} {e}
  : subst σ (unit (φ := φ) e) = unit e := by
  induction σ using Quotient.inductionOn;
  rfl

-- TODO: Define Eqv.termInduction or somesuch... should do the same for InS, too...

-- TODO: Ye Olde Rewrites

end Basic

end Term

end BinSyntax
