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

theorem Eqv.wk_wk {ρ : Γ.InS Δ} {σ : Δ.InS Ξ} {a : Eqv φ Ξ V}
  : (a.wk σ).wk ρ = a.wk (ρ.comp σ) := by
  induction a using Quotient.inductionOn
  simp [InS.wk_wk]

def Eqv.wk0 (a : Eqv φ Γ V) : Eqv φ (head::Γ) V := wk Ctx.InS.wk0 a

@[simp]
theorem Eqv.wk0_quot {a : InS φ Γ V} : wk0 (head := head) ⟦a⟧ = ⟦a.wk0⟧ := rfl

@[simp]
theorem Eqv.wk0_var {hn : Γ.Var n V}
  : wk0 (φ := φ) (head := head) (var n hn) = var (n + 1) hn.step := rfl

def Eqv.wk1 (a : Eqv φ (head::Γ) V) : Eqv φ (head::inserted::Γ) V := wk Ctx.InS.wk1 a

@[simp]
theorem Eqv.wk1_quot {a : InS φ (head::Γ) V} : wk1 (inserted := inserted) ⟦a⟧ = ⟦a.wk1⟧ := rfl

@[simp]
theorem Eqv.wk1_var0 {hn : Ctx.Var (head::Γ) 0 V}
  : wk1 (inserted := inserted) (var (φ := φ) 0 hn) = var 0 (Ctx.Var.head hn.get _) := rfl

def Eqv.wk2 (a : Eqv φ (left::right::Γ) V) : Eqv φ (left::right::inserted::Γ) V := wk Ctx.InS.wk2 a

@[simp]
theorem Eqv.wk2_quot {a : InS φ (left::right::Γ) V}
  : wk2 (inserted := inserted) ⟦a⟧ = ⟦a.wk2⟧ := rfl

theorem Eqv.wk1_wk2 {a : Eqv φ (head::Γ) V}
  : (a.wk1 (inserted := left)).wk2 (inserted := right) = a.wk1.wk1 := by
  induction a using Quotient.inductionOn
  simp [InS.wk1_wk2]

theorem Eqv.wk0_let1 {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  : wk0 (head := head) (a.let1 b) = a.wk0.let1 b.wk1 := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  simp [InS.wk0_let1]

theorem Eqv.wk1_let1 {a : Eqv φ (head::Γ) ⟨A, e⟩} {b : Eqv φ (⟨A, ⊥⟩::head::Γ) ⟨B, e⟩}
  : wk1 (inserted := inserted) (a.let1 b) = a.wk1.let1 b.wk2 := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  simp [InS.wk1_let1]

theorem Eqv.wk0_let2 {a : Eqv φ Γ ⟨Ty.prod A B, e⟩}
  {b : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : wk0 (head := head) (a.let2 b) = a.wk0.let2 b.wk2 := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  simp [InS.wk0_let2]

theorem Eqv.wk0_case {a : Eqv φ Γ ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : wk0 (head := head) (a.case l r) = a.wk0.case l.wk1 r.wk1 := by
  induction a using Quotient.inductionOn
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  simp [InS.wk0_case]

theorem Eqv.wk1_case {a : Eqv φ (head::Γ) ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::head::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::head::Γ) ⟨C, e⟩}
  : wk1 (inserted := inserted) (a.case l r) = a.wk1.case l.wk2 r.wk2 := by
  induction a using Quotient.inductionOn
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  simp [InS.wk1_case]

theorem Eqv.wk0_pair {Γ : Ctx α ε}
  {l : Eqv φ Γ (A, e)} {r : Eqv φ Γ (B, e)}
  : (pair l r).wk0 (head := head) = pair l.wk0 r.wk0 := by
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  rfl

theorem Eqv.wk0_inl {Γ : Ctx α ε} {l : Eqv φ Γ (A, e)}
  : (inl (B := right) l).wk0 (head := head) = inl l.wk0 := by
  induction l using Quotient.inductionOn
  rfl

theorem Eqv.wk0_inr {Γ : Ctx α ε} {r : Eqv φ Γ (B, e)}
  : (inr (A := left) r).wk0 (head := head) = inr r.wk0 := by
  induction r using Quotient.inductionOn
  rfl

theorem Eqv.wk0_abort {Γ : Ctx α ε} {a : Eqv φ Γ (Ty.empty, e)}
  : (abort (A := tyOut) a).wk0 (head := head) = abort a.wk0 tyOut := by
  induction a using Quotient.inductionOn
  rfl

theorem Eqv.wk0_unit {Γ : Ctx α ε} {e} : (unit (Γ := Γ) (φ := φ) e).wk0 (head := head) = unit e
  := rfl

theorem Eqv.wk1_pair {Γ : Ctx α ε}
  {l : Eqv φ (head::Γ) (A, e)} {r : Eqv φ (head::Γ) (B, e)}
  : (pair l r).wk1 (inserted := inserted) = pair l.wk1 r.wk1
  := by
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  rfl

theorem Eqv.wk1_inl {Γ : Ctx α ε} {l : Eqv φ (head::Γ) (A, e)}
  : (inl (B := right) l).wk1 (inserted := inserted) = inl l.wk1 := by
  induction l using Quotient.inductionOn
  rfl


theorem Eqv.wk1_inr {Γ : Ctx α ε} {r : Eqv φ (head::Γ) (B, e)}
  : (inr (A := left) r).wk1 (inserted := inserted) = inr r.wk1 := by
  induction r using Quotient.inductionOn
  rfl

theorem Eqv.wk1_abort {Γ : Ctx α ε} {a : Eqv φ (head::Γ) (Ty.empty, e)}
  : (abort (A := tyOut) a).wk1 (inserted := inserted) = abort a.wk1 tyOut := by
  induction a using Quotient.inductionOn
  rfl

theorem Eqv.wk1_unit {Γ : Ctx α ε} {e}
  : (unit (Γ := head::Γ) (φ := φ) e).wk1 (inserted := inserted) = unit e
  := rfl

theorem Eqv.wk2_pair {Γ : Ctx α ε}
  {l : Eqv φ (left::right::Γ) (A, e)} {r : Eqv φ (left::right::Γ) (B, e)}
  : (pair l r).wk2 (inserted := inserted) = pair l.wk2 r.wk2 := by
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  rfl

theorem Eqv.wk2_inl {Γ : Ctx α ε} {l : Eqv φ (left::right::Γ) (A, e)}
  : (inl (B := B) l).wk2 (inserted := inserted) = inl l.wk2 := by
  induction l using Quotient.inductionOn
  rfl

theorem Eqv.wk2_inr {Γ : Ctx α ε} {r : Eqv φ (left::right::Γ) (B, e)}
  : (inr (A := A) r).wk2 (inserted := inserted) = inr r.wk2 := by
  induction r using Quotient.inductionOn
  rfl

theorem Eqv.wk2_abort {Γ : Ctx α ε} {a : Eqv φ (left::right::Γ) (Ty.empty, e)}
  : (abort (A := tyOut) a).wk2 (inserted := inserted) = abort a.wk2 tyOut := by
  induction a using Quotient.inductionOn
  rfl

theorem Eqv.wk2_unit {Γ : Ctx α ε} {e}
  : (unit (Γ := left::right::Γ) (φ := φ) e).wk2 (inserted := inserted) = unit e := rfl

def Subst.Eqv (φ) [EffInstSet φ (Ty α) ε] (Γ Δ : Ctx α ε)
  := Quotient (α := Subst.InS φ Γ Δ) inferInstance

def Subst.InS.q (σ : Subst.InS φ Γ Δ) : Subst.Eqv φ Γ Δ := ⟦σ⟧

def Subst.Eqv.sound {σ σ' : Subst.InS φ Γ Δ} (h : σ ≈ σ')
  : Subst.InS.q σ = Subst.InS.q σ' := Quotient.sound h

def Subst.Eqv.lift (h : lo ≤ hi) (σ : Eqv φ Γ Δ) : Eqv φ (lo::Γ) (hi::Δ)
  := Quotient.liftOn σ (λσ => ⟦σ.lift h⟧) (λ_ _ h' => sound $ Subst.InS.lift_congr h h')

@[simp]
theorem Subst.Eqv.lift_quot {h : lo ≤ hi} {σ : InS φ Γ Δ} : lift h ⟦σ⟧ = ⟦σ.lift h⟧ := rfl

def Subst.Eqv.liftn₂ (h₁ : lo₁ ≤ hi₁) (h₂ : lo₂ ≤ hi₂)
  (σ : Eqv φ Γ Δ) : Eqv φ (lo₁::lo₂::Γ) (hi₁::hi₂::Δ)
  := Quotient.liftOn σ (λσ => ⟦σ.liftn₂ h₁ h₂⟧) (λ_ _ h' => sound $ sorry)

@[simp]
theorem Subst.Eqv.liftn₂_quot {h₁ : lo₁ ≤ hi₁} {h₂ : lo₂ ≤ hi₂} {σ : InS φ Γ Δ}
  : liftn₂ h₁ h₂ ⟦σ⟧ = ⟦σ.liftn₂ h₁ h₂⟧ := rfl

def Eqv.subst (σ : Subst.Eqv φ Γ Δ) (a : Eqv φ Δ V) : Eqv φ Γ V
  := Quotient.liftOn₂ σ a (λσ a => ⟦a.subst σ⟧) (λ_ _ _ _ h h' => sound $ InS.subst_congr h h')

@[simp]
theorem Eqv.subst_quot {σ : Subst.InS φ Γ Δ} {a : InS φ Δ V} : subst ⟦σ⟧ ⟦a⟧ = ⟦a.subst σ⟧ := rfl

def Subst.Eqv.comp (σ : Subst.Eqv φ Γ Δ) (τ : Subst.Eqv φ Δ Ξ)
  : Subst.Eqv φ Γ Ξ := Quotient.liftOn₂ σ τ (λσ τ => ⟦σ.comp τ⟧)
    (λ_ _ _ _ h h' => sound $ Term.Subst.InS.comp_congr h h')

@[simp]
theorem Subst.Eqv.comp_quot {σ : Subst.InS φ Γ Δ} {τ : Subst.InS φ Δ Ξ}
  : comp ⟦σ⟧ ⟦τ⟧ = ⟦σ.comp τ⟧ := rfl

theorem Subst.Eqv.lift_comp_lift {he : lo ≤ mid} {he' : mid ≤ hi} {σ : Eqv φ Γ Δ} {τ : Eqv φ Δ Ξ}
  : (σ.lift he).comp (τ.lift he') = (σ.comp τ).lift (le_trans he he') := by
  induction σ using Quotient.inductionOn
  induction τ using Quotient.inductionOn
  simp [Subst.InS.lift_comp_lift]

theorem Eqv.subst_subst {σ : Subst.Eqv φ Γ Δ} {τ : Subst.Eqv φ Δ Ξ} {a : Eqv φ Ξ V}
  : subst σ (subst τ a) = subst (σ.comp τ) a := by
  induction a using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  induction τ using Quotient.inductionOn
  simp [InS.subst_subst]

@[simp]
theorem Eqv.subst_lift_var_zero {σ : Subst.Eqv φ Γ Δ} {he : lo ≤ med} {he' : med ≤ hi}
  : subst (σ.lift he) (var 0 (Ctx.Var.head he' _)) = var 0 (Ctx.Var.head (le_trans he he') _) := by
  induction σ using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.subst_liftn₂_var_zero {σ : Subst.Eqv φ Γ Δ} {he₁ : lo₁ ≤ med₁} {he₂ : lo₂ ≤ med₂}
  {he'₁ : med₁ ≤ hi₁}
  : subst (σ.liftn₂ he₁ he₂) (var 0 (Ctx.Var.head he'₁ _))
  = var 0 (Ctx.Var.head (le_trans he₁ he₁') _) := by
  induction σ using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.subst_liftn₂_var_one {σ : Subst.Eqv φ Γ Δ} {he₁ : lo₁ ≤ med₁} {he₂ : lo₂ ≤ med₂}
  : subst (σ.liftn₂ he₁ he₂) (var 1 he₂')
  = var 1 (Ctx.Var.head (le_trans he₂ he₂'.get) _).step := by
  induction σ using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.subst_lift_var_succ {σ : Subst.Eqv φ Γ Δ} {n : ℕ}
  {hn : Ctx.Var (hi :: Δ) (n + 1) V} {h : lo ≤ hi}
  : subst (σ.lift h) (var (n + 1) hn) = (subst σ (var n hn.tail)).wk0 := by
  induction σ using Quotient.inductionOn
  rfl

theorem Eqv.subst_var_wk0 {σ : Subst.Eqv φ Γ Δ} {n : ℕ}
  {hn : Ctx.Var Δ n V} {h : lo ≤ hi}
  : (subst σ (var n hn)).wk0 = subst (σ.lift h) (var (n + 1) hn.step) := by
  induction σ using Quotient.inductionOn
  rfl

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

def Eqv.subst0 (a : Eqv φ Δ V) : Subst.Eqv φ Δ (V::Δ)
  := Quotient.liftOn a (λa => ⟦a.subst0⟧) (λ_ _ h => sorry)

@[simp]
theorem Eqv.subst0_quot {a : InS φ Δ V} : subst0 ⟦a⟧ = ⟦a.subst0⟧ := rfl

@[simp]
theorem Eqv.subst0_wk0 {a : Eqv φ Γ V} {b : Eqv φ Γ V'} : a.wk0.subst b.subst0 = a := by
  induction a using Quotient.inductionOn;
  induction b using Quotient.inductionOn;
  simp

@[simp]
theorem Eqv.subst0_var0_wk1 {Γ : Ctx α ε}
  (a : Eqv φ (⟨A, e⟩::Γ) V) : a.wk1.subst (var 0 (by simp)).subst0 = a
  := by induction a using Quotient.inductionOn; simp [var]

-- TODO: Define Eqv.termInduction or somesuch... should do the same for InS, too...

-- TODO: Ye Olde Rewrites

def Eqv.wk_res (hV : lo ≤ hi) (a : Eqv φ Γ lo) : Eqv φ Γ hi
  := Quotient.liftOn a (λa => ⟦a.wk_res hV⟧) (λ_ _ h => sound $ InS.wk_res_congr hV h)

@[simp]
theorem Eqv.wk_res_self {a : Eqv φ Γ e} : a.wk_res (by simp) = a := by
  induction a using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.var0_subst0 {Γ : Ctx α ε} {a : Eqv φ Γ lo} {h : Ctx.Var (lo::Γ) 0 hi}
  : (var 0 h).subst a.subst0 = a.wk_res h.get := by
  induction a using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.var_succ_subst0 {Γ : Ctx α ε} {n : ℕ}
  {hn : Ctx.Var (lo::Γ) (n + 1) hi} {a : Eqv φ Γ lo}
  : (var (n + 1) hn).subst a.subst0 = var n hn.tail := by
  induction a using Quotient.inductionOn;
  rfl

def Eqv.wk_eff (he : lo ≤ hi) (a : Eqv φ Γ ⟨A, lo⟩) : Eqv φ Γ ⟨A, hi⟩
  := Quotient.liftOn a (λa => ⟦a.wk_eff he⟧) (λ_ _ h => sound $ InS.wk_eff_congr he h)

@[simp]
theorem Eqv.wk_res_eff {a : Eqv φ Γ ⟨A, lo⟩} {h}
  : (a.wk_res (hi := ⟨A, hi⟩) h) = a.wk_eff h.2
  := by induction a using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.wk_eff_quot {a : InS φ Γ ⟨A, lo⟩} {he : lo ≤ hi} : wk_eff he ⟦a⟧ = ⟦a.wk_eff he⟧ := rfl

@[simp]
theorem Eqv.wk_eff_self {a : Eqv φ Γ ⟨A, e⟩} : a.wk_eff (by simp) = a := by
  induction a using Quotient.inductionOn;
  rfl

theorem Eqv.wk0_wk_eff {a : Eqv φ Γ ⟨A, lo⟩} {h : lo ≤ hi}
  : (a.wk_eff h).wk0 (head := head) = a.wk0.wk_eff h := by
  induction a using Quotient.inductionOn;
  rfl

theorem Eqv.subst_wk_eff {σ : Subst.Eqv φ Γ Δ} {a : Eqv φ Δ ⟨A, lo⟩} {he : lo ≤ hi}
  : subst σ (a.wk_eff he) = (subst σ a).wk_eff he := by
  induction a using Quotient.inductionOn;
  induction σ using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_eff_wk_eff {a : Eqv φ Γ ⟨A, lo⟩} {he : lo ≤ mid} {he' : mid ≤ hi}
  : (a.wk_eff he).wk_eff he' = a.wk_eff (le_trans he he')
  := by induction a using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.wk_eff_var {n : ℕ} {hn : Γ.Var n ⟨A, lo⟩} {he : lo ≤ hi}
  : wk_eff he (var n hn) = var (φ := φ) n (hn.wk_eff he) := rfl

@[simp]
theorem Eqv.wk_eff_op {a : Eqv φ Γ ⟨A, lo⟩} {f : φ} {hf : Φ.EFn f A B lo} {he : lo ≤ hi}
  : wk_eff he (op f hf a) = op f (hf.wk_eff he) (a.wk_eff he) := by
  induction a using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_eff_let1 {a : Eqv φ Γ ⟨A, lo⟩} {b : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, lo⟩} {he : lo ≤ hi}
  : wk_eff he (let1 a b) = let1 (a.wk_eff he) (b.wk_eff he) := by
  induction a using Quotient.inductionOn;
  induction b using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_eff_pair {a : Eqv φ Γ ⟨A, lo⟩} {b : Eqv φ Γ ⟨B, lo⟩} {he : lo ≤ hi}
  : wk_eff he (pair a b) = pair (a.wk_eff he) (b.wk_eff he) := by
  induction a using Quotient.inductionOn;
  induction b using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_eff_let2 {a : Eqv φ Γ ⟨Ty.prod A B, lo⟩}
  {b : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, lo⟩} {he : lo ≤ hi}
  : wk_eff he (let2 a b) = let2 (a.wk_eff he) (b.wk_eff he) := by
  induction a using Quotient.inductionOn;
  induction b using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_eff_inl {a : Eqv φ Γ ⟨A, lo⟩} {he : lo ≤ hi}
  : wk_eff he (inl (B := B) a) = inl (a.wk_eff he) := by
  induction a using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_eff_inr {a : Eqv φ Γ ⟨B, lo⟩} {he : lo ≤ hi}
  : wk_eff he (inr (A := A) a) = inr (a.wk_eff he) := by
  induction a using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_eff_case {a : Eqv φ Γ ⟨Ty.coprod A B, lo⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, lo⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, lo⟩} {he : lo ≤ hi}
  : wk_eff he (case a l r) = case (a.wk_eff he) (l.wk_eff he) (r.wk_eff he) := by
  induction a using Quotient.inductionOn;
  induction l using Quotient.inductionOn;
  induction r using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_eff_abort {a : Eqv φ Γ ⟨Ty.empty, lo⟩} {A} {he : lo ≤ hi}
  : wk_eff he (abort a A) = abort (a.wk_eff he) A := by
  induction a using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_eff_unit {he : lo ≤ hi}
  : wk_eff he (unit (φ := φ) (Γ := Γ) lo) = unit hi := rfl

theorem Eqv.let1_op {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  {hf : Φ.EFn f A B e} : let1 (op f hf a) b = (let1 a $ let1 (op f hf (var 0 (by simp))) $ b.wk1)
  := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  apply Eqv.sound; apply InS.let1_op

theorem Eqv.let1_let1 {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  {c : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : let1 (let1 a b) c = (let1 a $ let1 b $ c.wk1) := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  induction c using Quotient.inductionOn
  apply Eqv.sound; apply InS.let1_let1

theorem Eqv.let1_pair {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ (Γ) ⟨B, e⟩} {r : Eqv φ (⟨A.prod B, ⊥⟩::Γ) ⟨C, e⟩}
  : let1 (pair a b) r
  = (let1 a $ let1 b.wk0 $ let1 (pair (var 1 (by simp)) (var 0 (by simp))) $ r.wk1.wk1) := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.let1_pair

theorem Eqv.let1_let2 {Γ : Ctx α ε} {a : Eqv φ Γ ⟨Ty.prod A B, e⟩}
  {b : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨C, ⊥⟩::Γ) ⟨D, e⟩}
  : let1 (let2 a b) r = (let2 a $ let1 b $ r.wk1.wk1) := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.let1_let2

theorem Eqv.let1_inl {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, e⟩} {r : Eqv φ (⟨Ty.coprod A B, ⊥⟩::Γ) ⟨C, e⟩}
  : let1 (inl a) r = (let1 a $ let1 (inl (var 0 (by simp))) $ r.wk1) := by
  induction a using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.let1_inl

theorem Eqv.let1_inr {Γ : Ctx α ε} {a : Eqv φ Γ ⟨B, e⟩} {r : Eqv φ (⟨Ty.coprod A B, ⊥⟩::Γ) ⟨C, e⟩}
  : let1 (inr a) r = (let1 a $ let1 (inr (var 0 (by simp))) $ r.wk1) := by
  induction a using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.let1_inr

theorem Eqv.let1_case {Γ : Ctx α ε} {a : Eqv φ Γ ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  {s : Eqv φ (⟨C, ⊥⟩::Γ) ⟨D, e⟩}
  : let1 (case a l r) s = case a (let1 l s.wk1) (let1 r s.wk1) := by
  induction a using Quotient.inductionOn
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  induction s using Quotient.inductionOn
  apply Eqv.sound; apply InS.let1_case

theorem Eqv.let1_abort {Γ : Ctx α ε} {a : Eqv φ Γ ⟨Ty.empty, e⟩} {A : Ty α}
  {r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  : let1 (abort a A) r = (let1 a $ let1 (abort (var 0 (by simp)) A) $ r.wk1) := by
  induction a using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.let1_abort

theorem Eqv.let2_eta {Γ : Ctx α ε} {a : Eqv φ Γ ⟨Ty.prod A B, e⟩}
  : let2 a (pair (var 1 (by simp)) (var 0 (by simp))) = a := by
  induction a using Quotient.inductionOn
  apply Eqv.sound; apply InS.let2_eta

theorem Eqv.let1_eta {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, e⟩}
  : let1 a (var 0 (by simp)) = a := by
  induction a using Quotient.inductionOn
  apply Eqv.sound; apply InS.let1_eta

theorem Eqv.let2_pair {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ Γ ⟨B, e⟩}
  {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : let2 (pair a b) r = (let1 a $ let1 b.wk0 $ r) := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.let2_pair

theorem Eqv.let2_bind {Γ : Ctx α ε} {a : Eqv φ Γ ⟨Ty.prod A B, e⟩}
  {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : let2 a r = (let1 a $ let2 (var 0 (by simp)) $ r.wk2) := by
  induction a using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.let2_bind

theorem Eqv.case_bind {Γ : Ctx α ε} {a : Eqv φ Γ ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case a l r = (let1 a $ case (var 0 (by simp)) (l.wk1) (r.wk1)) := by
  induction a using Quotient.inductionOn
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.case_bind

def Eqv.Pure (a : Eqv φ Γ ⟨A, e⟩) : Prop := ∃p : Eqv φ Γ ⟨A, ⊥⟩, a = p.wk_eff (by simp)

@[simp]
theorem Eqv.pure_is_pure {a : Eqv φ Γ ⟨A, ⊥⟩} : a.Pure := ⟨a, by simp⟩

@[simp]
theorem Eqv.wk_eff_is_pure {a : Eqv φ Γ ⟨A, ⊥⟩} : (a.wk_eff (hi := e) (by simp)).Pure := ⟨a, rfl⟩

@[simp]
theorem Eqv.unit_is_pure {e} : (unit (Γ := Γ) (φ := φ) e).Pure := ⟨unit ⊥, rfl⟩

theorem Eqv.let1_beta {a : Eqv φ Γ ⟨A, ⊥⟩} {b : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  : let1 (a.wk_eff (by simp)) b = b.subst a.subst0 := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  apply sound $ InS.let1_beta

theorem Eqv.let1_beta_pure {a : Eqv φ Γ ⟨A, ⊥⟩} {b : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩}
  : let1 a b = b.subst a.subst0 := by rw [<-a.wk_eff_self, let1_beta, wk_eff_self]

theorem Eqv.let1_beta_var0 {Γ : Ctx α ε} {b : Eqv φ (⟨A, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  : let1 (var 0 (by simp)) b = b.subst (var 0 (by simp)).subst0 := by rw [<-wk_eff_var, let1_beta]

theorem Eqv.let1_beta_let2_eta {Γ : Ctx α ε}
  {b : Eqv φ (⟨A.prod B, ⊥⟩::⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : let1 ((var 1 (by simp)).pair (var 0 (by simp))) b
  = b.subst ((var 1 (by simp)).pair (var 0 (by simp))).subst0
  := by rw [<-wk_eff_var (n := 1), <-wk_eff_var (n := 0), <-wk_eff_pair, let1_beta]

theorem Eqv.terminal {a : Eqv φ Γ ⟨Ty.unit, ⊥⟩} {b : Eqv φ Γ ⟨Ty.unit, ⊥⟩} : a = b := by
  induction a using Quotient.inductionOn; induction b using Quotient.inductionOn; apply sound;
  apply InS.terminal

theorem Eqv.pure_eq_unit {a : Eqv φ Γ ⟨Ty.unit, ⊥⟩} : a = Eqv.unit ⊥ := Eqv.terminal

-- TODO: simp?
theorem Eqv.eq_unit {a : Eqv φ Γ ⟨Ty.unit, e⟩} : a.Pure → a = Eqv.unit e
  | ⟨p, hp⟩ => by cases hp; rw [<-wk_eff_unit (lo := ⊥) (he := bot_le)];
                  apply congrArg; apply pure_eq_unit

theorem Eqv.initial (hΓ : Γ.IsInitial) {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ Γ ⟨A, e⟩} : a = b := by
  induction a using Quotient.inductionOn; induction b using Quotient.inductionOn; apply sound;
  apply InS.initial hΓ

end Basic

end Term

end BinSyntax
