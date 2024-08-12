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

def Eqv.cast
  (a : Eqv φ Γ V) (hΓ : Γ = Γ') (hV : V = V') : Eqv φ Γ' V'
  := Quotient.liftOn a
    (λa => ⟦a.cast hΓ hV⟧)
    (λa a' h => Quotient.sound (by cases hΓ; cases hV; exact h))

theorem Eqv.eq_of_term_eq {a a' : InS φ Γ V} (h : (a : Term φ) = (a' : Term φ))
  : a.q = a'.q := congrArg _ (InS.ext h)

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

@[simp]
theorem Eqv.wk1_var_succ {n : ℕ} {hn : Ctx.Var (head::Γ) (n + 1) V}
  : wk1 (inserted := inserted) (var (φ := φ) (n + 1) hn)
  = var (n + 2) (have hn := hn.wk (Ctx.Wkn.wk1 (inserted := inserted)); hn) := rfl

def Eqv.wk2 (a : Eqv φ (left::right::Γ) V) : Eqv φ (left::right::inserted::Γ) V := wk Ctx.InS.wk2 a

@[simp]
theorem Eqv.wk2_quot {a : InS φ (left::right::Γ) V}
  : wk2 (inserted := inserted) ⟦a⟧ = ⟦a.wk2⟧ := rfl

@[simp]
theorem Eqv.wk2_var0 {hn : Ctx.Var (left::right::Γ) 0 V}
  : wk2 (inserted := inserted) (var (φ := φ) 0 hn) = var 0 (Ctx.Var.head hn.get _) := rfl

@[simp]
theorem Eqv.wk2_var1 {hn : Ctx.Var (left::right::Γ) 1 V}
  : wk2 (inserted := inserted) (var (φ := φ) 1 hn) = var 1 (Ctx.Var.head hn.get _).step := rfl

def Eqv.wk_id {Γ Δ : Ctx α ε} (hΓ : Γ.Wkn Δ id) (a : Eqv φ Δ V) : Eqv φ Γ V
  := Quotient.liftOn a (λa => ⟦a.wk_id hΓ⟧) (λ_ _ h => sorry)

@[simp]
theorem Eqv.wk_id_var {Γ Δ : Ctx α ε} {hΓ : Γ.Wkn Δ id} {n : ℕ} {hn : Δ.Var n V}
  : wk_id hΓ (var n hn) = var (φ := φ) n (hn.wk hΓ) := rfl

@[simp]
theorem Eqv.wk_id_let1 {Γ Δ : Ctx α ε} {hΓ : Γ.Wkn Δ id} {a : Eqv φ Δ ⟨A, e⟩}
  {b : Eqv φ (⟨A, ⊥⟩::Δ) ⟨B, e⟩}
  : wk_id hΓ (let1 a b) = let1 (a.wk_id hΓ) (b.wk_id hΓ.slift_id) := by
  induction a using Quotient.inductionOn;
  induction b using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_id_pair {Γ Δ : Ctx α ε} {hΓ : Γ.Wkn Δ id} {a : Eqv φ Δ ⟨A, e⟩}
  {b : Eqv φ Δ ⟨B, e⟩}
  : wk_id hΓ (pair a b) = pair (a.wk_id hΓ) (b.wk_id hΓ) := by
  induction a using Quotient.inductionOn;
  induction b using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_id_let2 {Γ Δ : Ctx α ε} {hΓ : Γ.Wkn Δ id} {a : Eqv φ Δ ⟨Ty.prod A B, e⟩}
  {b : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Δ) ⟨C, e⟩}
  : wk_id hΓ (let2 a b) = let2 (a.wk_id hΓ) (b.wk_id hΓ.slift_id₂) := by
  induction a using Quotient.inductionOn;
  induction b using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_id_inl {Γ Δ : Ctx α ε} {hΓ : Γ.Wkn Δ id} {a : Eqv φ Δ ⟨A, e⟩}
  : wk_id hΓ (inl (B := B) a) = inl (a.wk_id hΓ) := by
  induction a using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_id_inr {Γ Δ : Ctx α ε} {hΓ : Γ.Wkn Δ id} {a : Eqv φ Δ ⟨B, e⟩}
  : wk_id hΓ (inr (A := A) a) = inr (a.wk_id hΓ) := by
  induction a using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_id_case {Γ Δ : Ctx α ε} {hΓ : Γ.Wkn Δ id} {a : Eqv φ Δ ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Δ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Δ) ⟨C, e⟩}
  : wk_id hΓ (case a l r) = case (a.wk_id hΓ) (l.wk_id hΓ.slift_id) (r.wk_id hΓ.slift_id) := by
  induction a using Quotient.inductionOn;
  induction l using Quotient.inductionOn;
  induction r using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_id_unit {Γ Δ : Ctx α ε} {hΓ : Γ.Wkn Δ id} {e}
  : wk_id hΓ (unit (φ := φ) e) = unit e := rfl

@[simp]
theorem Eqv.wk_id_abort {Γ Δ : Ctx α ε} {hΓ : Γ.Wkn Δ id} {a : Eqv φ Δ ⟨Ty.empty, e⟩} {A}
  : wk_id hΓ (abort a A) = abort (a.wk_id hΓ) A := by
  induction a using Quotient.inductionOn;
  rfl

@[simp]
theorem Eqv.wk_id_quot {Γ Δ : Ctx α ε} {hΓ : Γ.Wkn Δ id} {a : InS φ Δ V}
  : wk_id hΓ ⟦a⟧ = ⟦a.wk_id hΓ⟧ := rfl

theorem Eqv.wk_eq_wk_id  {Γ Δ : Ctx α ε} {h : Γ.Wkn Δ id} {a : Term.Eqv φ Δ V}
  : a.wk ⟨_root_.id, h⟩ = a.wk_id h
  := by induction a using Quotient.inductionOn; simp [Term.InS.wk_eq_wk_id]

def Eqv.swap01 (a : Eqv φ (left::right::Γ) V) : Eqv φ (right::left::Γ) V := wk Ctx.InS.swap01 a

@[simp]
theorem Eqv.swap01_quot {a : InS φ (left::right::Γ) V}
  : swap01 ⟦a⟧ = ⟦a.swap01⟧ := rfl

def Eqv.swap02 (a : Eqv φ (left::mid::right::Γ) V) : Eqv φ (mid::right::left::Γ) V
  := wk Ctx.InS.swap02 a

@[simp]
theorem Eqv.swap02_quot {a : InS φ (left::mid::right::Γ) V}
  : swap02 ⟦a⟧ = ⟦a.swap02⟧ := rfl

theorem Eqv.var0_eq_wk1_var0 {hn : Ctx.Var (head::inserted::Γ) 0 V}
  : var 0 hn = wk1 (var (φ := φ) 0 (Ctx.Var.head hn.get _)) := rfl

theorem Eqv.var0_eq_wk2_var0 {hn : Ctx.Var (left::right::inserted::Γ) 0 V}
  : var 0 hn = wk2 (inserted := inserted) (var (φ := φ) 0 (Ctx.Var.head hn.get _)) := rfl

theorem Eqv.var1_eq_wk0_var0 {hn : Ctx.Var (head::Γ) 1 V}
  : var 1 hn = wk0 (var (φ := φ) 0 hn.tail) := rfl

theorem Eqv.var1_eq_wk2_var1 {hn : Ctx.Var (left::right::inserted::Γ) 1 V}
  : var 1 hn = wk2 (inserted := inserted) (var (φ := φ) 1 (Ctx.Var.head hn.get _).step) := rfl

theorem Eqv.var2_eq_wk0_var1 {hn : Ctx.Var (head::Γ) 2 V}
  : var 2 hn = wk0 (var (φ := φ) 1 hn.tail) := rfl

theorem Eqv.var4_eq_wk0_var3 {hn : Ctx.Var (head::Γ) 4 V}
  : var 4 hn = wk0 (var (φ := φ) 3 hn.tail) := rfl

theorem Eqv.var4_eq_wk1_var3 {hn : Ctx.Var (head::inserted::Γ) 4 V}
  : var 4 hn = wk1 (var (φ := φ) 3 hn.tail.tail.step) := rfl

theorem Eqv.wk1_wk2 {a : Eqv φ (head::Γ) V}
  : (a.wk1 (inserted := left)).wk2 (inserted := right) = a.wk1.wk1 := by
  induction a using Quotient.inductionOn
  simp [InS.wk1_wk2]

theorem Eqv.wk0_wk1 {Γ : Ctx α ε} {L} (d : Eqv φ Γ L)
  : d.wk0.wk1 = (d.wk0 (head := right)).wk0 (head := left)
  := by induction d using Quotient.inductionOn; simp [InS.wk0_wk1]

theorem Eqv.wk1_wk0 {Γ : Ctx α ε} {L} (d : Eqv φ (mid::Γ) L)
  : (d.wk1 (inserted := right)).wk0 (head := left) = d.wk0.wk2
  := by induction d using Quotient.inductionOn; simp [InS.wk1_wk0]

theorem Eqv.wk0_wk2 {Γ : Ctx α ε} {L} (d : Eqv φ (mid::Γ) L)
  : d.wk0.wk2 = (d.wk1 (inserted := right)).wk0 (head := left)
  := d.wk1_wk0.symm

theorem Eqv.wk2_liftn₂_wk1 {Γ : Ctx α ε} {L} (d : Eqv φ (left::right::Γ) L)
  : d.wk2.wk (Ctx.InS.wk1.liftn₂ (le_refl _) (le_refl _))
  = (d.wk2 (inserted := inserted)).wk2 (inserted := inserted') := by
  rw [wk2, wk2, wk_wk, wk2, wk_wk]
  congr 1
  ext k
  -- Need an "engineering induction" tactic here...
  cases k with
  | zero => rfl
  | succ k => cases k <;> rfl

@[simp]
theorem Eqv.wk0_let1 {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  : wk0 (head := head) (a.let1 b) = a.wk0.let1 b.wk1 := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  simp [InS.wk0_let1]

@[simp]
theorem Eqv.wk0_let2 {a : Eqv φ Γ ⟨Ty.prod A B, e⟩}
  {b : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : wk0 (head := head) (a.let2 b) = a.wk0.let2 b.wk2 := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  simp [InS.wk0_let2]

@[simp]
theorem Eqv.wk1_let1 {a : Eqv φ (head::Γ) ⟨A, e⟩} {b : Eqv φ (⟨A, ⊥⟩::head::Γ) ⟨B, e⟩}
  : wk1 (inserted := inserted) (a.let1 b) = a.wk1.let1 b.wk2 := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  simp [InS.wk1_let1]

theorem Eqv.wk1_let2 {a : Eqv φ (head::Γ) ⟨Ty.prod A B, e⟩}
  {b : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::head::Γ) ⟨C, e⟩}
  : wk1 (inserted := inserted) (a.let2 b)
  = a.wk1.let2 (b.wk ((Ctx.InS.wk1).liftn₂ (le_refl _) (le_refl _))) := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  simp only [wk1, wk_let2]

@[simp]
theorem Eqv.wk0_case {a : Eqv φ Γ ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : wk0 (head := head) (a.case l r) = a.wk0.case l.wk1 r.wk1 := by
  induction a using Quotient.inductionOn
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  simp [InS.wk0_case]

@[simp]
theorem Eqv.wk1_case {a : Eqv φ (head::Γ) ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::head::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::head::Γ) ⟨C, e⟩}
  : wk1 (inserted := inserted) (a.case l r) = a.wk1.case l.wk2 r.wk2 := by
  induction a using Quotient.inductionOn
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  simp [InS.wk1_case]

@[simp]
theorem Eqv.wk0_pair {Γ : Ctx α ε}
  {l : Eqv φ Γ (A, e)} {r : Eqv φ Γ (B, e)}
  : (pair l r).wk0 (head := head) = pair l.wk0 r.wk0 := by
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.wk0_inl {Γ : Ctx α ε} {l : Eqv φ Γ (A, e)}
  : (inl (B := right) l).wk0 (head := head) = inl l.wk0 := by
  induction l using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.wk0_inr {Γ : Ctx α ε} {r : Eqv φ Γ (B, e)}
  : (inr (A := left) r).wk0 (head := head) = inr r.wk0 := by
  induction r using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.wk0_abort {Γ : Ctx α ε} {a : Eqv φ Γ (Ty.empty, e)}
  : (abort (A := tyOut) a).wk0 (head := head) = abort a.wk0 tyOut := by
  induction a using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.wk0_unit {Γ : Ctx α ε} {e} : (unit (Γ := Γ) (φ := φ) e).wk0 (head := head) = unit e
  := rfl

@[simp]
theorem Eqv.wk1_pair {Γ : Ctx α ε}
  {l : Eqv φ (head::Γ) (A, e)} {r : Eqv φ (head::Γ) (B, e)}
  : (pair l r).wk1 (inserted := inserted) = pair l.wk1 r.wk1
  := by
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.wk1_inl {Γ : Ctx α ε} {l : Eqv φ (head::Γ) (A, e)}
  : (inl (B := right) l).wk1 (inserted := inserted) = inl l.wk1 := by
  induction l using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.wk1_inr {Γ : Ctx α ε} {r : Eqv φ (head::Γ) (B, e)}
  : (inr (A := left) r).wk1 (inserted := inserted) = inr r.wk1 := by
  induction r using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.wk1_abort {Γ : Ctx α ε} {a : Eqv φ (head::Γ) (Ty.empty, e)}
  : (abort (A := tyOut) a).wk1 (inserted := inserted) = abort a.wk1 tyOut := by
  induction a using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.wk1_unit {Γ : Ctx α ε} {e}
  : (unit (Γ := head::Γ) (φ := φ) e).wk1 (inserted := inserted) = unit e
  := rfl

theorem Eqv.wk2_let1 {a : Eqv φ (left::right::Γ) ⟨A, e⟩} {b : Eqv φ (⟨A, ⊥⟩::left::right::Γ) ⟨B, e⟩}
  : wk2 (inserted := inserted) (a.let1 b) = a.wk2.let1 (b.wk (Ctx.InS.wk2.lift (le_refl _))) := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  rfl

theorem Eqv.wk2_let2 {a : Eqv φ (left::right::Γ) ⟨Ty.prod A B, e⟩}
  {b : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::left::right::Γ) ⟨C, e⟩}
  : wk2 (inserted := inserted) (a.let2 b)
  = a.wk2.let2 (b.wk ((Ctx.InS.wk2).liftn₂ (le_refl _) (le_refl _))) := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  simp only [wk2, wk_let2]

@[simp]
theorem Eqv.wk2_pair {Γ : Ctx α ε}
  {l : Eqv φ (left::right::Γ) (A, e)} {r : Eqv φ (left::right::Γ) (B, e)}
  : (pair l r).wk2 (inserted := inserted) = pair l.wk2 r.wk2 := by
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.wk2_inl {Γ : Ctx α ε} {l : Eqv φ (left::right::Γ) (A, e)}
  : (inl (B := B) l).wk2 (inserted := inserted) = inl l.wk2 := by
  induction l using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.wk2_inr {Γ : Ctx α ε} {r : Eqv φ (left::right::Γ) (B, e)}
  : (inr (A := A) r).wk2 (inserted := inserted) = inr r.wk2 := by
  induction r using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.wk2_abort {Γ : Ctx α ε} {a : Eqv φ (left::right::Γ) (Ty.empty, e)}
  : (abort (A := tyOut) a).wk2 (inserted := inserted) = abort a.wk2 tyOut := by
  induction a using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.wk2_unit {Γ : Ctx α ε} {e}
  : (unit (Γ := left::right::Γ) (φ := φ) e).wk2 (inserted := inserted) = unit e := rfl

theorem Eqv.wk0_wk_lift {Γ : Ctx α ε} {ρ : Γ.InS Δ} {a : Eqv φ Δ V} {h : lo ≤ hi}
  : (a.wk0 (head := hi)).wk (ρ.lift h) = (a.wk ρ).wk0 (head := lo) := by
  simp only [wk0, wk_wk]
  rfl

theorem Eqv.wk0_wk_liftn₂ {Γ : Ctx α ε} {ρ : Γ.InS Δ} {a : Eqv φ (head::Δ) V'}
  {h : lo ≤ hi} {h' : head' ≤ head}
  : wk (ρ.liftn₂ h h') (a.wk0 (head := hi))
  = (a.wk (ρ.lift h')).wk0 (head := lo) := by
  rw [<-Ctx.InS.lift_lift, wk0_wk_lift]

theorem Eqv.wk1_wk_liftn₂ {Γ : Ctx α ε} {ρ : Γ.InS Δ} {a : Eqv φ (hi::Δ) V'}
  {h : lo ≤ hi} {h' : head' ≤ head}
  : a.wk1.wk (ρ.liftn₂ h h') = (a.wk (ρ.lift h)).wk1 := by
  simp only [wk1, wk_wk, <-Ctx.InS.lift_lift]
  congr 1
  ext k
  cases k <;> rfl

theorem Eqv.wk_lift_wk1 {a : Eqv φ (left::right::Γ) V}
  : a.wk (Ctx.InS.wk1.lift h) = a.wk2 (inserted := inserted) := by simp [wk2]

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
  := Quotient.liftOn σ (λσ => ⟦σ.liftn₂ h₁ h₂⟧) (λ_ _ h' => sound $ by
    simp only [<-Subst.InS.lift_lift]
    exact Subst.InS.lift_congr _ $ Subst.InS.lift_congr _ h')

@[simp]
theorem Subst.Eqv.liftn₂_quot {h₁ : lo₁ ≤ hi₁} {h₂ : lo₂ ≤ hi₂} {σ : InS φ Γ Δ}
  : liftn₂ h₁ h₂ ⟦σ⟧ = ⟦σ.liftn₂ h₁ h₂⟧ := rfl

def Eqv.subst (σ : Subst.Eqv φ Γ Δ) (a : Eqv φ Δ V) : Eqv φ Γ V
  := Quotient.liftOn₂ σ a (λσ a => ⟦a.subst σ⟧) (λ_ _ _ _ h h' => sound $ InS.subst_congr h h')

theorem Subst.Eqv.lift_lift (h₁ : lo₁ ≤ hi₁) (h₂ : lo₂ ≤ hi₂)
  {σ : Eqv φ Γ Δ} : (σ.lift h₁).lift h₂ = (σ.liftn₂ h₂ h₁) := by
  induction σ using Quotient.inductionOn
  simp [Subst.InS.lift_lift]

@[simp]
theorem Eqv.subst_quot {σ : Subst.InS φ Γ Δ} {a : InS φ Δ V} : subst ⟦σ⟧ ⟦a⟧ = ⟦a.subst σ⟧ := rfl

@[simp]
theorem Eqv.subst_lift_var_zero {σ : Subst.Eqv φ Γ Δ} {he : lo ≤ med} {hn : Ctx.Var (med::Δ) 0 hi}
  : subst (σ.lift he) (var 0 hn) = var 0 ⟨by simp, by simp [le_trans he hn.get]⟩ := by
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

@[simp]
theorem Eqv.subst_liftn₂_var_add_2 {σ : Subst.Eqv φ Γ Δ} {he₁ : lo₁ ≤ med₁} {he₂ : lo₂ ≤ med₂}
  : subst (σ.liftn₂ he₁ he₂) (var (n + 2) hn) = (subst σ (var n hn.tail.tail)).wk0.wk0
  := by rw [<-Subst.Eqv.lift_lift, subst_lift_var_succ, subst_lift_var_succ]

theorem Eqv.subst_var_wk0 {σ : Subst.Eqv φ Γ Δ} {n : ℕ}
  {hn : Ctx.Var Δ n V} {h : lo ≤ hi}
  : (subst σ (var n hn)).wk0 = subst (σ.lift h) (var (n + 1) hn.step) := by
  induction σ using Quotient.inductionOn
  rfl

-- def Subst.Eqv.id (Γ : Ctx α ε) : Subst.Eqv φ Γ Γ := ⟦Subst.InS.id⟧

-- theorem Eqv.subst_id {a : Eqv φ Γ V} : subst Subst.Eqv.id a = a := by
--   induction a using Quotient.inductionOn
--   simp [Subst.InS.subst_id]

def Subst.Eqv.fromWk (ρ : Γ.InS Δ) : Eqv φ Γ Δ := ⟦ρ.toSubst⟧

theorem Eqv.subst_fromWk {ρ : Γ.InS Δ} {a : Eqv φ Δ V}
  : a.subst (Subst.Eqv.fromWk ρ) = a.wk ρ := by
  induction a using Quotient.inductionOn
  simp [Subst.Eqv.fromWk, InS.subst_toSubst]

def Subst.Eqv.id {Γ : Ctx α ε} : Subst.Eqv φ Γ Γ := ⟦Subst.InS.id⟧

@[simp]
theorem Eqv.subst_id {a : Eqv φ Γ V} : a.subst Subst.Eqv.id = a := by
  induction a using Quotient.inductionOn
  simp [Subst.Eqv.id]

theorem Eqv.subst_id' {a : Eqv φ Γ V} {σ : Subst.Eqv φ Γ Γ}
  (h : σ = Subst.Eqv.id) : a.subst σ = a := by cases h; simp

theorem Eqv.get_of_quot_eq {σ τ : Subst.InS φ Γ Δ}
  (h : (⟦σ⟧ : Subst.Eqv φ Γ Δ) = ⟦τ⟧) (i : Fin Δ.length)
  : (⟦σ.get i⟧ : Term.Eqv φ _ _) = ⟦τ.get i⟧ := Quotient.sound $ Quotient.exact h i

def Subst.Eqv.get (σ : Subst.Eqv φ Γ Δ) (i : Fin Δ.length) : Term.Eqv φ Γ (Δ.get i) :=
  Quotient.liftOn σ (λσ => ⟦σ.get i⟧) (λ_ _ h => Quotient.sound $ h i)

@[simp]
theorem Subst.Eqv.get_quot {σ : Subst.InS φ Γ Δ} {i : Fin Δ.length}
  : get ⟦σ⟧ i = ⟦σ.get i⟧ := rfl

theorem Subst.Eqv.ext_quot {σ τ : Subst.InS φ Γ Δ}
  (h : ∀i, (⟦σ.get i⟧ : Term.Eqv φ _ _) = ⟦τ.get i⟧) : (⟦σ⟧ : Subst.Eqv φ Γ Δ) = ⟦τ⟧
  := Quotient.sound (λi => Quotient.exact $ h i)

@[ext]
theorem Subst.Eqv.ext {σ τ : Subst.Eqv φ Γ Δ} (h : ∀i, get σ i = get τ i)
  : σ = τ := by
  induction σ using Quotient.inductionOn
  induction τ using Quotient.inductionOn
  exact ext_quot h

theorem Subst.Eqv.eq_of_subst_eq {σ τ : Subst.InS φ Γ Δ}
  (h : ∀i, σ.get i = τ.get i) : σ.q = τ.q := by ext k; simp [Subst.InS.q, h]

theorem Subst.Eqv.ext_iff' {σ τ : Subst.Eqv φ Γ Δ}
  : σ = τ ↔ ∀i, get σ i = get τ i := ⟨λh => by simp [h], ext⟩

-- TODO: rewrite to use get, eliminating a sorry implicitly?
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

theorem Subst.Eqv.get_comp {σ : Subst.Eqv φ Γ Δ} {τ : Subst.Eqv φ Δ Ξ} {i : Fin Ξ.length}
  : (σ.comp τ).get i = (τ.get i).subst σ := by
  induction σ using Quotient.inductionOn
  induction τ using Quotient.inductionOn
  rfl

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
  := Quotient.liftOn a (λa => ⟦a.subst0⟧) (λ_ _ h => by
    simp only
    apply Quotient.sound
    intro i
    cases i using Fin.cases with
    | zero => exact h
    | succ => exact Setoid.refl _)

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
theorem Eqv.wk_res_quot {a : InS φ Γ lo} {hV : lo ≤ hi} : wk_res hV ⟦a⟧ = ⟦a.wk_res hV⟧ := rfl

theorem Eqv.subst_var {σ : Subst.Eqv φ Γ Δ} {i : ℕ}
  {hn : Ctx.Var Δ i V} : subst σ (var i hn) = (σ.get ⟨i, hn.length⟩).wk_res hn.getElem := by
  induction σ using Quotient.inductionOn
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
theorem Eqv.wk_res_var {n : ℕ} {hn : Γ.Var n lo} {he : lo ≤ hi}
  : wk_res he (var n hn) = var (φ := φ) n (hn.wk_res he) := rfl

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

theorem Eqv.let2_bind' {Γ : Ctx α ε} {a : Eqv φ Γ ⟨Ty.prod A B, e⟩}
  {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩} {s : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::_::Γ) ⟨C, e⟩}
  (h : s = r.wk2)
  : (let1 a $ let2 (var 0 (by simp)) $ s) = let2 a r := by cases h; rw [<-let2_bind]

theorem Eqv.let2_let1 {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨X, e⟩} {b : Eqv φ (⟨X, ⊥⟩::Γ) ⟨Ty.prod A B, e⟩}
  {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : let2 (let1 a b) r = (let1 a $ let2 b $ r.wk2) := by
  rw [let2_bind, let1_let1]
  congr
  apply Eq.symm
  rw [let2_bind]
  congr
  rw [wk1_let2, wk1_var0, wk2_liftn₂_wk1]

theorem Eqv.let2_let2
  {a : Eqv φ Γ ⟨X.prod Y, e⟩} {b : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨Ty.prod A B, e⟩}
  {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : let2 (let2 a b) r = (let2 a $ let2 b $ r.wk2.wk2) := by
  rw [let2_bind, let1_let2]
  congr
  apply Eq.symm
  rw [let2_bind]
  congr
  simp only [wk1_let2, wk1_var0, wk2_liftn₂_wk1]

theorem Eqv.let2_case
  {a : Eqv φ Γ ⟨X.coprod Y, e⟩}
  {l : Eqv φ (⟨X, ⊥⟩::Γ) ⟨Ty.prod A B, e⟩} {r : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨Ty.prod A B, e⟩}
  {s : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : let2 (case a l r) s = case a (let2 l s.wk2) (let2 r s.wk2) := by
  rw [let2_bind, let1_case]
  congr <;> {
    apply Eq.symm
    rw [let2_bind]
    congr
    simp only [wk1_let2, wk1_var0, wk2_liftn₂_wk1]
  }

theorem Eqv.case_bind {Γ : Ctx α ε} {a : Eqv φ Γ ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case a l r = (let1 a $ case (var 0 (by simp)) (l.wk1) (r.wk1)) := by
  induction a using Quotient.inductionOn
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.case_bind

theorem Eqv.case_let1
  {x : Eqv φ Γ ⟨X, e⟩} {d : Eqv φ (⟨X, ⊥⟩::Γ) ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case (let1 x d) l r = let1 x (case d l.wk1 r.wk1) := by
  rw [case_bind, let1_let1]
  apply Eq.symm
  rw [case_bind]
  simp [wk1_wk2]

theorem Eqv.case_let2
  {x : Eqv φ Γ ⟨X.prod Y, e⟩} {d : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case (let2 x d) l r = let2 x (case d l.wk1.wk1 r.wk1.wk1) := by
  rw [case_bind, let1_let2]
  apply Eq.symm
  rw [case_bind]
  simp [wk1_wk2]

theorem Eqv.case_case
  {dd : Eqv φ Γ ⟨X.coprod Y, e⟩}
  {dl : Eqv φ (⟨X, ⊥⟩::Γ) ⟨Ty.coprod A B, e⟩}
  {dr : Eqv φ (⟨Y, ⊥⟩::Γ) ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case (case dd dl dr) l r = case dd (case dl l.wk1 r.wk1) (case dr l.wk1 r.wk1) := by
  rw [case_bind, let1_case]
  congr <;> {
    apply Eq.symm
    rw [case_bind]
    simp [wk1_wk2]
  }

theorem Eqv.case_eta {A B : Ty α}
  {a : Eqv φ Γ ⟨A.coprod B, e⟩}
  : case a (var 0 Ctx.Var.bhead).inl (var 0 Ctx.Var.bhead).inr = a := by
  induction a using Quotient.inductionOn
  apply Eqv.sound; apply InS.case_eta

theorem Eqv.let1_let1_case {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨Ty.coprod A B, e⟩}
  {b : Eqv φ (⟨Ty.coprod A B, ⊥⟩::Γ) ⟨X, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::⟨X, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨C, e⟩}
  {r : Eqv φ (⟨B, ⊥⟩::⟨X, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨C, e⟩}
  : (let1 a $ let1 b $ case (var 1 Ctx.Var.bhead.step) l r)
  = (let1 a $ case (var 0 Ctx.Var.bhead) (let1 b.wk0 $ l.swap01) (let1 b.wk0 $ r.swap01)) := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.let1_let1_case

theorem Eqv.let1_let2_case {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨Ty.coprod A B, e⟩}
  {b : Eqv φ (⟨Ty.coprod A B, ⊥⟩::Γ) ⟨X.prod Y, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::⟨Y, ⊥⟩::⟨X, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨C, e⟩}
  {r : Eqv φ (⟨B, ⊥⟩::⟨Y, ⊥⟩::⟨X, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨C, e⟩}
  : (let1 a $ let2 b $ case (var 2 Ctx.Var.bhead.step.step) l r)
  = (let1 a $ case (var 0 Ctx.Var.bhead) (let2 b.wk0 $ l.swap02) (let2 b.wk0 $ r.swap02)) := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.let1_let2_case

theorem Eqv.let1_case_case {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨Ty.coprod A B, e⟩}
  {d : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) ⟨Ty.coprod X Y, e⟩}
  {ll : Eqv φ (⟨A, ⊥⟩::⟨X, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨X, e⟩}
  {lr : Eqv φ (⟨B, ⊥⟩::⟨X, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨X, e⟩}
  {rl : Eqv φ (⟨A, ⊥⟩::⟨Y, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨X, e⟩}
  {rr : Eqv φ (⟨B, ⊥⟩::⟨Y, ⊥⟩::⟨A.coprod B, ⊥⟩::Γ) ⟨X, e⟩}
  : (let1 a $ case d
      (case (var 1 Ctx.Var.bhead.step) ll lr)
      (case (var 1 Ctx.Var.bhead.step) rl rr))
  = (let1 a $ case (var 0 Ctx.Var.bhead)
    (case d.wk0 ll.swap01 rl.swap01)
    (case d.wk0 lr.swap01 rr.swap01)) := by
  induction a using Quotient.inductionOn
  induction d using Quotient.inductionOn
  induction ll using Quotient.inductionOn
  induction lr using Quotient.inductionOn
  induction rl using Quotient.inductionOn
  induction rr using Quotient.inductionOn
  apply Eqv.sound; apply InS.let1_case_case

theorem Eqv.case_op_op {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨Ty.coprod A B, e⟩}
  {f} {hf : Φ.EFn f C D e}
  {r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  {s : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case a (op f hf r) (op f hf s) = op f hf (case a r s) := by
  induction a using Quotient.inductionOn
  induction r using Quotient.inductionOn
  induction s using Quotient.inductionOn
  apply Eqv.sound; apply InS.case_op_op

theorem Eqv.case_inl_inl {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A.coprod B, e⟩}
  {r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  {s : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case a (inl (B := D) r) (inl s) = inl (case a r s) := by
  induction a using Quotient.inductionOn
  induction r using Quotient.inductionOn
  induction s using Quotient.inductionOn
  apply Eqv.sound; apply InS.case_inl_inl

theorem Eqv.case_inr_inr {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A.coprod B, e⟩}
  {r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨D, e⟩}
  {s : Eqv φ (⟨B, ⊥⟩::Γ) ⟨D, e⟩}
  : case a (inr (A := C) r) (inr s) = inr (case a r s) := by
  induction a using Quotient.inductionOn
  induction r using Quotient.inductionOn
  induction s using Quotient.inductionOn
  apply Eqv.sound; apply InS.case_inr_inr

theorem Eqv.case_abort_abort {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A.coprod B, e⟩}
  {r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨Ty.empty, e⟩}
  {s : Eqv φ (⟨B, ⊥⟩::Γ) ⟨Ty.empty, e⟩}
  : case a (abort r A) (abort s A) = abort (case a r s) A := by
  induction a using Quotient.inductionOn
  induction r using Quotient.inductionOn
  induction s using Quotient.inductionOn
  apply Eqv.sound; apply InS.case_abort_abort

theorem Eqv.case_pair_pair {Γ : Ctx α ε}
  {d : Eqv φ Γ ⟨A.coprod B, e⟩}
  {al : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  {bl : Eqv φ (⟨A, ⊥⟩::Γ) ⟨D, e⟩}
  {ar : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  {br : Eqv φ (⟨B, ⊥⟩::Γ) ⟨D, e⟩}
  : case d (pair al bl) (pair ar br)
  = (let1 d $ pair
      (case (var 0 Ctx.Var.bhead) al.wk1 ar.wk1)
      (case (var 0 Ctx.Var.bhead) bl.wk1 br.wk1)) := by
  induction d using Quotient.inductionOn
  induction al using Quotient.inductionOn
  induction bl using Quotient.inductionOn
  induction ar using Quotient.inductionOn
  induction br using Quotient.inductionOn
  apply Eqv.sound; apply InS.case_pair_pair

theorem Eqv.case_wk0_wk0 {A B : Ty α} {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A.coprod B, e⟩}
  {r : Eqv φ Γ ⟨C, e⟩}
  : case a r.wk0 r.wk0 = let1 a r.wk0 := by
  induction a using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.case_wk0_wk0

theorem Eqv.case_inl {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case (inl a) l r = (let1 a l) := by
  induction a using Quotient.inductionOn
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.case_inl

theorem Eqv.case_inr {Γ : Ctx α ε} {a : Eqv φ Γ ⟨B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} {r : Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩}
  : case (inr a) l r = (let1 a r) := by
  induction a using Quotient.inductionOn
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.sound; apply InS.case_inr

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

theorem Eqv.let1_beta_var1 {Γ : Ctx α ε} {b : Eqv φ (⟨A, ⊥⟩::⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : let1 (var 1 (by simp)) b = b.subst (var 1 (by simp)).subst0 := by rw [<-wk_eff_var, let1_beta]

theorem Eqv.let1_beta_var2 {Γ : Ctx α ε} {b : Eqv φ (⟨A, ⊥⟩::⟨B, ⊥⟩::⟨C, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨D, e⟩}
  : let1 (var 2 (by simp)) b = b.subst (var 2 (by simp)).subst0 := by rw [<-wk_eff_var, let1_beta]

theorem Eqv.let1_beta_var3
  {Γ : Ctx α ε} {b : Eqv φ (⟨A, ⊥⟩::⟨B, ⊥⟩::⟨C, ⊥⟩::⟨D, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨E, e⟩}
  : let1 (var 3 (by simp)) b = b.subst (var 3 (by simp)).subst0 := by rw [<-wk_eff_var, let1_beta]

theorem Eqv.let1_beta_var
  {Γ : Ctx α ε} {n : ℕ} {hn : Ctx.Var Γ n ⟨A, ⊥⟩}
  {b : Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  : let1 (var n (hn.wk_eff bot_le)) b = b.subst (var n hn).subst0 := by rw [<-wk_eff_var, let1_beta]

theorem Eqv.let1_beta_let2_eta {Γ : Ctx α ε}
  {b : Eqv φ (⟨A.prod B, ⊥⟩::⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : let1 ((var 1 (by simp)).pair (var 0 (by simp))) b
  = b.subst ((var 1 (by simp)).pair (var 0 (by simp))).subst0
  := by rw [<-wk_eff_var (n := 1), <-wk_eff_var (n := 0), <-wk_eff_pair, let1_beta]

theorem Eqv.pair_bind
  {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ Γ ⟨B, e⟩}
  : pair a b = (let1 a $ let1 b.wk0 $ pair (var 1 (by simp)) (var 0 (by simp))) := by
  rw [<-let2_eta (a := pair _ _), let2_pair]

theorem Eqv.let1_pair_var_1_left
  {Γ : Ctx α ε} {r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨X, e⟩} {b : Eqv φ (⟨X, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  : let1 r (pair (var 1 ⟨by simp, le_refl _, by simp⟩) b) = pair (var 0 (by simp)) (let1 r b) := by
  rw [
    pair_bind, let1_beta_var1, subst_let1, subst0_wk0, subst_pair, subst_lift_var_succ,
    var0_subst0, wk_res_var, subst_lift_var_zero,
    pair_bind (a := var 0 _), let1_beta_var0, subst_let1, subst0_wk0, let1_let1
  ]
  rfl

theorem Eqv.let1_pair_var_succ
  {Γ : Ctx α ε} {r : Eqv φ Γ ⟨X, e⟩} {b : Eqv φ (⟨X, ⊥⟩::Γ) ⟨B, e⟩}
  {hn : Ctx.Var _ n ⟨C, ⊥⟩}
  : let1 r (pair (var (n + 1) (hn.step.wk_eff bot_le)) b)
  = pair (var n (hn.wk_eff bot_le)) (let1 r b) := by
  rw [
    pair_bind, let1_beta_var, subst_let1, subst0_wk0, subst_pair, subst_lift_var_succ,
    var0_subst0, wk_res_var, subst_lift_var_zero,
    pair_bind (a := var n _), let1_beta_var, subst_let1, subst0_wk0, let1_let1
  ]
  rfl
  exact hn
  simp [hn]

theorem Eqv.pair_bind_left
  {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ Γ ⟨B, e⟩}
  : pair a b = let1 a (pair (var 0 (by simp)) b.wk0)
  := by rw [pair_bind, pair_bind (a := (var 0 _)), let1_beta_var0, subst_let1, subst0_wk0]; rfl

theorem Eqv.let1_pair_right
  {Γ : Ctx α ε} {r : Eqv φ Γ ⟨X, e⟩} {a : Eqv φ (⟨X, ⊥⟩::Γ) ⟨A, e⟩} {b : Eqv φ Γ ⟨B, e⟩}
  : let1 r (pair a b.wk0) = pair (let1 r a) b := by rw [
    pair_bind (b := b), let1_let1, let1_pair_var_1_left, let1_eta, wk1_pair, wk1_var0, wk0_wk1,
    <-pair_bind_left
  ]

theorem Eqv.let2_pair_right
  {Γ : Ctx α ε} {r : Eqv φ Γ ⟨X.prod Y, e⟩}
  {a : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨A, e⟩} {b : Eqv φ Γ ⟨B, e⟩}
  : let2 r (pair a b.wk0.wk0) = pair (let2 r a) b := by rw [
    pair_bind (b := b), let1_let2, let1_pair_var_1_left, let1_eta, wk1_pair, wk1_var0, wk0_wk1,
    wk1_pair, wk0_wk1, wk1_var0, <-pair_bind_left
  ]

theorem Eqv.let1_pair_wk_eff_left
  {Γ : Ctx α ε} {r : Eqv φ Γ ⟨X, e⟩} {a : Eqv φ Γ ⟨A, ⊥⟩} {b : Eqv φ (⟨X, ⊥⟩::Γ) ⟨B, e⟩}
  : let1 r (pair (a.wk0.wk_eff (by simp)) b) = pair (a.wk_eff (by simp)) (let1 r b) := by
  rw [
    pair_bind (b := r.let1 _), let1_beta, subst_let1, subst0_wk0, let1_let1, pair_bind, let1_beta,
    subst_let1, subst0_wk0, subst_pair, subst_lift_var_succ, subst_lift_var_zero, var0_subst0,
    wk_res_eff, subst_pair, subst_lift_var_succ, subst_lift_var_zero, var0_subst0, wk_res_eff,
    <-wk0_wk_eff, wk1_pair, wk1_var0, wk0_wk1
  ]

theorem Eqv.let2_eta_wk2 {Γ : Ctx α ε}
  : ((var 1 (by simp)).pair (var 0 (by simp)) : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) (A.prod B, e)
    ).wk2 (inserted := inserted) = (var 1 (by simp)).pair (var 0 (by simp))
  := rfl

theorem Eqv.swap_eta_wk2 {Γ : Ctx α ε}
  : ((var 0 (by simp)).pair (var 1 (by simp)) : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) (B.prod A, e)
    ).wk2 (inserted := inserted) = (var 0 (by simp)).pair (var 1 (by simp))
  := rfl

-- TODO: generalize appropriately...

theorem Eqv.let2_pair_var_2_left
  {Γ : Ctx α ε} {r : Eqv φ (⟨A, ⊥⟩::Γ) ⟨X.prod Y, e⟩} {b : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  : let2 r (pair (e := e) (A := A) (var 2 (by simp)) b)
  = pair (var 0 (by simp)) (let2 r b) := by
  rw [
    pair_bind, let1_beta_var2, subst_let1, subst0_wk0, subst_pair, subst_lift_var_succ,
    var0_subst0, wk_res_var, subst_lift_var_zero,
    pair_bind (a := var 0 _), let1_beta_var0, subst_let1, subst0_wk0, let1_let2
  ]
  rfl

theorem Eqv.let2_pair_var_3_left
  {Γ : Ctx α ε} {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨X.prod Y, e⟩}
  {b : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : let2 r (pair (e := e) (A := A) (var 3 (by simp)) b)
  = pair (var 1 (by simp)) (let2 r b) := by
  rw [
    pair_bind, let1_beta_var3, subst_let1, subst0_wk0, subst_pair, subst_lift_var_succ,
    var0_subst0, wk_res_var, subst_lift_var_zero,
    pair_bind (a := var 1 _), let1_beta_var1, subst_let1, subst0_wk0, let1_let2
  ]
  rfl

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

-- TODO: eqv induction...

theorem Eqv.let1_wk_eff_let1 {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A, ⊥⟩} {b : Eqv φ Γ ⟨B, e⟩} {c : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : let1 (a.wk_eff bot_le) (let1 b.wk0 c)
  = let1 b (let1 (a.wk_eff bot_le).wk0 (c.wk Ctx.InS.swap01)) := by
  rw [let1_beta, wk0_wk_eff, let1_beta, subst_let1, subst0_wk0]
  apply congrArg
  induction c using Quotient.inductionOn
  induction a using Quotient.inductionOn
  apply Eqv.eq_of_term_eq
  simp only [Set.mem_setOf_eq, InS.coe_subst, Subst.InS.coe_lift, InS.coe_subst0, InS.coe_wk0,
    InS.coe_wk, Ctx.InS.coe_swap01, ← Term.subst_fromWk, Term.subst_subst]
  congr
  funext k
  cases k with
  | zero => rfl
  | succ k => cases k with
  | zero => simp [Term.Subst.comp, Term.subst_fromWk]
  | succ k => rfl

theorem Eqv.Pure.let1_let1 {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ Γ ⟨B, e⟩} {c : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : a.Pure → let1 a (let1 b.wk0 c) = let1 b (let1 a.wk0 (c.wk Ctx.InS.swap01))
  | ⟨a, ha⟩ => by cases ha; rw [let1_wk_eff_let1]

theorem Eqv.let1_let1_comm {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A, ⊥⟩} {b : Eqv φ Γ ⟨B, ⊥⟩} {c : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, ⊥⟩}
  : let1 a (let1 b.wk0 c) = let1 b (let1 a.wk0 (c.wk Ctx.InS.swap01))
  := Eqv.Pure.let1_let1 ⟨a, by simp⟩

theorem Eqv.swap01_let2_eta {Γ : Ctx α ε} {A B : Ty α} {e}
  : (pair (var 1 (by simp)) (var 0 (by simp)) : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) (A.prod B, e)
    ).wk Ctx.InS.swap01 = pair (var 0 (by simp)) (var 1 (by simp)) := rfl

theorem Eqv.pair_bind_swap_left
  {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ Γ ⟨B, e⟩}
  (ha : a.Pure)
  : pair a b = (let1 b $ let1 a.wk0 $ pair (var 0 (by simp)) (var 1 (by simp))) := by
  rw [pair_bind, ha.let1_let1, swap01_let2_eta]

theorem Eqv.pair_bind_swap_right
  {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ Γ ⟨B, e⟩}
  (hb : b.Pure)
  : pair a b = (let1 b $ let1 a.wk0 $ pair (var 0 (by simp)) (var 1 (by simp))) := by
  rw [pair_bind, hb.let1_let1]; rfl

theorem Eqv.pair_bind_swap_wk_eff_left {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A, ⊥⟩} {b : Eqv φ Γ ⟨B, e⟩}
  : pair (a.wk_eff bot_le) b
  = (let1 b $ let1 (a.wk_eff bot_le).wk0 $ pair (var 0 (by simp)) (var 1 (by simp)))
  := pair_bind_swap_left ⟨a, rfl⟩

theorem Eqv.pair_bind_swap_wk_eff_right {Γ : Ctx α ε}
  {a : Eqv φ Γ ⟨A, e⟩} {b : Eqv φ Γ ⟨B, ⊥⟩}
  : pair a (b.wk_eff bot_le)
  = (let1 (b.wk_eff bot_le) $ let1 a.wk0 $ pair (var 0 (by simp)) (var 1 (by simp)))
  := pair_bind_swap_right ⟨b, rfl⟩

theorem Eqv.pair_bind_swap
  {Γ : Ctx α ε} {a : Eqv φ Γ ⟨A, ⊥⟩} {b : Eqv φ Γ ⟨B, ⊥⟩}
  : pair a b = (let1 b $ let1 a.wk0 $ pair (var 0 (by simp)) (var 1 (by simp)))
  := pair_bind_swap_left ⟨a, by simp⟩

end Basic

end Term

end BinSyntax
