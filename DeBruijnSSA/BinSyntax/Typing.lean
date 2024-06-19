import Discretion.Wk.List
import Discretion.Basic
import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Effect.Definitions

namespace BinSyntax

section Basic

-- TODO: assert effect for e.g. terminators is pure rather than use 0?

-- Can we even do centrality? Propositional parametrization?

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]

inductive Ty (α : Type u) where
  | base : α → Ty α
  | prod : Ty α → Ty α → Ty α
  | coprod : Ty α → Ty α → Ty α
  | unit : Ty α
  | empty : Ty α
  deriving Repr, DecidableEq

inductive Ty.IsInitial : Ty α → Prop
  | prod_left : ∀{A}, IsInitial A → IsInitial (prod A B)
  | prod_right : ∀{B}, IsInitial B → IsInitial (prod A B)
  | coprod : ∀{A B}, IsInitial A → IsInitial B → IsInitial (coprod A B)
  | empty : IsInitial empty

inductive Ty.LE : Ty α → Ty α → Prop where
  | base {x y} : x ≤ y → LE (base x) (base y)
  | prod {x₁ x₂ y₁ y₂} : LE x₁ y₁ → LE x₂ y₂ → LE (prod x₁ x₂) (prod y₁ y₂)
  | coprod {x₁ x₂ y₁ y₂} : LE x₁ y₁ → LE x₂ y₂ → LE (coprod x₁ x₂) (coprod y₁ y₂)
  | unit : LE unit unit
  | empty : LE empty empty

theorem Ty.LE.prod_left {A A' B B' : Ty α} (h : LE (Ty.prod A B) (Ty.prod A' B')) : LE A A'
  := by cases h; assumption

theorem Ty.LE.prod_right {A A' B B' : Ty α} (h : LE (Ty.prod A B) (Ty.prod A' B')) : LE B B'
  := by cases h; assumption

theorem Ty.LE.coprod_left {A A' B B' : Ty α} (h : LE (Ty.coprod A B) (Ty.coprod A' B')) : LE A A'
  := by cases h; assumption

theorem Ty.LE.coprod_right {A A' B B' : Ty α} (h : LE (Ty.coprod A B) (Ty.coprod A' B')) : LE B B'
  := by cases h; assumption

theorem Ty.LE.refl : ∀{A : Ty α}, LE A A
  | Ty.base x => base (le_refl x)
  | Ty.prod _ _ => prod refl refl
  | Ty.coprod _ _ => coprod refl refl
  | Ty.unit => unit
  | Ty.empty => empty

theorem Ty.LE.trans : ∀{A B C : Ty α}, LE A B → LE B C → LE A C
  | _, _, _, base h, base h' => base (le_trans h h')
  | _, _, _, prod h₁ h₂, prod h₁' h₂' => prod (h₁.trans h₁') (h₂.trans h₂')
  | _, _, _, coprod h₁ h₂, coprod h₁' h₂' => coprod (h₁.trans h₁') (h₂.trans h₂')
  | _, _, _, unit, unit => unit
  | _, _, _, empty, empty => empty

theorem Ty.LE.antisymm : ∀{A B : Ty α}, LE A B → LE B A → A = B
  | _, _, base h, base h' => by rw [le_antisymm h h']
  | _, _, prod h₁ h₂, prod h₁' h₂' => by rw [Ty.LE.antisymm h₁ h₁', Ty.LE.antisymm h₂ h₂']
  | _, _, coprod h₁ h₂, coprod h₁' h₂' => by rw [Ty.LE.antisymm h₁ h₁', Ty.LE.antisymm h₂ h₂']
  | _, _, unit, unit => rfl
  | _, _, empty, empty => rfl

instance : PartialOrder (Ty α) where
  le := Ty.LE
  le_refl _ := Ty.LE.refl
  le_trans _ _ _ := Ty.LE.trans
  le_antisymm _ _ := Ty.LE.antisymm

theorem Ty.LE.eq [d : DiscreteOrder α] {A B : Ty α} : LE A B → A = B
  | base h => by rw [d.le_eq _ _ h]
  | prod h₁ h₂ => by rw [eq h₁, eq h₂]
  | coprod h₁ h₂ => by rw [eq h₁, eq h₂]
  | unit => rfl
  | empty => rfl

instance [DiscreteOrder α] : DiscreteOrder (Ty α) where
  le_eq _ _ := Ty.LE.eq

-- TODO: Ty.LE is decidable if ≤ on α is

def Ctx (α ε) := List (Ty α × ε)

def Ctx.reverse (Γ : Ctx α ε) : Ctx α ε := List.reverse Γ

structure Ctx.Var (Γ : Ctx α ε) (n : ℕ) (V : Ty α × ε) : Prop where
  length : n < Γ.length
  get : Γ.get ⟨n, length⟩ ≤ V

theorem Ctx.Var.head (h : V ≤ V') (Γ : Ctx α ε) : Var (V::Γ) 0 V' where
  length := by simp
  get := h

@[simp]
theorem Ctx.Var.head_iff {V V' : Ty α × ε} {Γ : Ctx α ε} : Var (V::Γ) 0 V' ↔ V ≤ V'
  := ⟨λh => h.get, λh => Ctx.Var.head h Γ⟩

theorem Ctx.Var.shead {head : Ty α × ε} {Γ : Ctx α ε}
  : Var (head::Γ) 0 head := Var.head (le_refl _) Γ

theorem Ctx.Var.step {Γ : Ctx α ε} (h : Var Γ n V) : Var (V'::Γ) (n+1) V
  := ⟨by simp [h.length], by simp [h.get]⟩

theorem Ctx.Var.of_step {Γ : Ctx α ε} {n} (h : Var (V'::Γ) (n+1) V) : Var Γ n V
  := ⟨Nat.lt_of_succ_lt_succ h.length, h.get⟩

@[simp]
theorem Ctx.Var.step_iff {V V' : Ty α × ε} {Γ : Ctx α ε} {n} : Var (V'::Γ) (n+1) V ↔ Var Γ n V
  := ⟨Ctx.Var.of_step, Ctx.Var.step⟩

def Ctx.effect (Γ : Ctx α ε) : ℕ → ε := λn => if h : n < Γ.length then (Γ.get ⟨n, h⟩).2 else ⊥

instance : Append (Ctx α ε) := (inferInstance : Append (List (Ty α × ε)))

instance : Membership (Ty α × ε) (Ctx α ε)
  := (inferInstance : Membership (Ty α × ε) (List (Ty α × ε)))

def Ctx.IsInitial (Γ : Ctx α ε) : Prop := ∃V ∈ Γ, Ty.IsInitial V.1

theorem Ctx.IsInitial.append_left {Γ : Ctx α ε} (h : Γ.IsInitial) (Δ) : (Γ ++ Δ).IsInitial
  := let ⟨V, hV, hV0⟩ := h; ⟨V, List.mem_append_left _ hV, hV0⟩

theorem Ctx.IsInitial.append_right (Γ) {Δ : Ctx α ε} (h : Δ.IsInitial) : (Γ ++ Δ).IsInitial
  := let ⟨V, hV, hV0⟩ := h; ⟨V, List.mem_append_right _ hV, hV0⟩

@[simp]
theorem Ctx.IsInitial.append {Γ Δ : Ctx α ε} : (Γ ++ Δ).IsInitial ↔ Γ.IsInitial ∨ Δ.IsInitial
  := ⟨
    λ⟨V, hV, hV0⟩ => (List.mem_append.mp hV).elim (Or.inl ⟨V, ·, hV0⟩) (Or.inr ⟨V, ·, hV0⟩),
    λh => h.elim (append_left · _) (append_right _)⟩

-- def Ctx.IsInitial.cons {A ε} (h : Ty.IsInitial A) (Γ : Ctx α ε)
--   : IsInitial (⟨A, ε⟩::Γ)
--   := ⟨V, List.mem_cons_self _ _, h⟩

-- TODO: HAppend of Ctx and List?

theorem Ctx.append_assoc : (Γ Δ Ξ : Ctx α ε) → Γ ++ Δ ++ Ξ = Γ ++ (Δ ++ Ξ)
  := List.append_assoc

theorem Ctx.reverse_append : (Γ Δ : Ctx α ε) → (Γ ++ Δ).reverse = Δ.reverse ++ Γ.reverse
  := List.reverse_append

theorem Ctx.length_reverse : (Γ : Ctx α ε) → Γ.reverse.length = Γ.length
  := List.length_reverse

def FCtx (α ε) := Σn, Fin n → Ty α × ε

-- TODO: FCtx append

/-- A well-formed term -/
inductive Term.Wf : Ctx α ε → Term φ → Ty α × ε → Prop
  | var : Γ.Var n V → Wf Γ (var n) V
  | op : Φ.EFn f A B e → Wf Γ a ⟨A, e⟩ → Wf Γ (op f a) ⟨B, e⟩
  | pair : Wf Γ a ⟨A, e⟩ → Wf Γ b ⟨B, e⟩ → Wf Γ (pair a b) ⟨(Ty.prod A B), e⟩
  | inl : Wf Γ a ⟨A, e⟩ → Wf Γ (inl a) ⟨(Ty.coprod A B), e⟩
  | inr : Wf Γ b ⟨B, e⟩ → Wf Γ (inr b) ⟨(Ty.coprod A B), e⟩
  | abort : Wf Γ a ⟨Ty.empty, e⟩ → Wf Γ (abort a) ⟨A, e⟩
  | unit (e) : Wf Γ unit ⟨Ty.unit, e⟩

theorem Term.Wf.to_var {Γ : Ctx α ε} {n V} (h : Wf Γ (@Term.var φ n) V)
  : Γ.Var n V := by cases h; assumption

theorem Term.Wf.to_fn' {Γ : Ctx α ε} {a : Term φ}
  (h : Wf Γ (Term.op f a) V)
  (hA : A ≤ Φ.src f)
  (hB : V.1 ≤ B)
  (he : V.2 ≤ e)
  : Φ.EFn f A B e := by cases h with | op hf => exact ⟨⟨hA, hf.trg.trans hB⟩, hf.effect.trans he⟩

theorem Term.Wf.to_fn {Γ : Ctx α ε} {a : Term φ} (h : Wf Γ (Term.op f a) V)
  : Φ.EFn f (Φ.src f) V.1 V.2 := h.to_fn' (le_refl _) (le_refl _) (le_refl _)

theorem Term.Wf.wk_res {Γ : Ctx α ε} {a : Term φ} {V V'} (h : Wf Γ a V) (hV : V ≤ V') : Wf Γ a V'
  := by induction h generalizing V' with
  | var dv =>
    constructor
    exact ⟨dv.length, dv.get.trans hV⟩
  | op hf _ I =>
    cases V'
    constructor
    exact ⟨⟨hf.src, hf.trg.trans hV.left⟩, hf.effect.trans hV.right⟩
    exact I ⟨le_refl _, hV.right⟩
  | pair _ _ Il Ir =>
    cases V'
    cases hV.left
    constructor
    exact Il ⟨by assumption, hV.right⟩
    exact Ir ⟨by assumption, hV.right⟩
  | inl _ I =>
    cases V'
    cases hV.left
    constructor
    exact I ⟨by assumption, hV.right⟩
  | inr _ I =>
    cases V'
    cases hV.left
    constructor
    exact I ⟨by assumption, hV.right⟩
  | abort _ I =>
    cases V'
    constructor
    exact I ⟨le_refl _, hV.right⟩
  | unit =>
    cases V'
    cases hV.left
    constructor

theorem Term.Wf.to_op' {Γ : Ctx α ε} {a : Term φ}
  (h : Wf Γ (Term.op f a) V)
  (hV : ⟨Φ.src f, V.2⟩ ≤ V')
  : Wf Γ a V' := by cases h with | op hf ha => exact ha.wk_res ⟨hf.src.trans hV.left, hV.right⟩

theorem Term.Wf.to_op {Γ : Ctx α ε} {a : Term φ} {V} (h : Wf Γ (Term.op f a) V)
  : Wf Γ a ⟨Φ.src f, V.2⟩ := h.to_op' (le_refl _)

theorem Term.Wf.to_left {Γ : Ctx α ε} {a b : Term φ}
  (h : Wf Γ (Term.pair a b) ⟨Ty.prod A B, e⟩)
  : Wf Γ a ⟨A, e⟩ := by cases h with | pair ha _ => exact ha

theorem Term.Wf.to_right {Γ : Ctx α ε} {a b : Term φ}
  (h : Wf Γ (Term.pair a b) ⟨Ty.prod A B, e⟩)
  : Wf Γ b ⟨B, e⟩ := by cases h with | pair _ hb => exact hb

/-- A derivation that a term is well-formed -/
inductive Term.WfD : Ctx α ε → Term φ → Ty α × ε → Type _
  | var : Γ.Var n V → WfD Γ (var n) V
  | op : Φ.EFn f A B e → WfD Γ a ⟨A, e⟩ → WfD Γ (op f a) ⟨B, e⟩
  | pair : WfD Γ a ⟨A, e⟩ → WfD Γ b ⟨B, e⟩ → WfD Γ (pair a b) ⟨(Ty.prod A B), e⟩
  | inl : WfD Γ a ⟨A, e⟩ → WfD Γ (inl a) ⟨(Ty.coprod A B), e⟩
  | inr : WfD Γ b ⟨B, e⟩ → WfD Γ (inr b) ⟨(Ty.coprod A B), e⟩
  | abort : WfD Γ a ⟨Ty.empty, e⟩ → WfD Γ (abort a) ⟨A, e⟩
  | unit (e) : WfD Γ unit ⟨Ty.unit, e⟩

def Term.WfD.var0 {head} {Γ : Ctx α ε} : WfD (head::Γ) (@Term.var φ 0) head := var (by simp)

def Term.WfD.var1 {left right} {Γ : Ctx α ε} : WfD (left::right::Γ) (@Term.var φ 1) right
  := var (by simp)

def Term.WfD.cast_term {Γ : Ctx α ε} {a a' : Term φ} {V} (h : WfD Γ a V) (ha : a = a') : WfD Γ a' V
  := ha ▸ h

def Term.WfD.cast_src {Γ Γ' : Ctx α ε} {a : Term φ} {V} (h : Γ = Γ') (d : WfD Γ a V)
  : WfD Γ' a V := h ▸ d

def Term.WfD.cast_trg {Γ : Ctx α ε} {a : Term φ} {V V'} (d : WfD Γ a V) (h : V = V')
  : WfD Γ a V' := h ▸ d

theorem Term.WfD.cast_term_cast_src {Γ Γ' : Ctx α ε} {a a' : Term φ} {V}
  (h : Γ = Γ') (d : WfD Γ a V) (ha : a = a')
  : (d.cast_src h).cast_term ha = (d.cast_term ha).cast_src h
  := by cases h; cases ha; rfl

theorem Term.WfD.cast_term_cast_trg {Γ : Ctx α ε} {a a' : Term φ} {V V'}
  (d : WfD Γ a V) (ha : a = a') (h : V = V')
  : (d.cast_trg h).cast_term ha = (d.cast_term ha).cast_trg h
  := by cases ha; cases h; rfl

theorem Term.WfD.cast_src_cast_trg {Γ Γ' : Ctx α ε} {a : Term φ} {V V'}
  (h : Γ = Γ') (d : WfD Γ a V) (h' : V = V')
  : (d.cast_trg h').cast_src h = (d.cast_src h).cast_trg h'
  := by cases h; cases h'; rfl

-- TODO: weakenings should commute, too...

theorem Term.WfD.toWf {Γ : Ctx α ε} {a : Term φ} {V} (h : WfD Γ a V) : Wf Γ a V
  := match h with
  | var dv => Wf.var dv
  | op df de => Wf.op df de.toWf
  | pair dl dr => Wf.pair dl.toWf dr.toWf
  | inl dl => Wf.inl dl.toWf
  | inr dr => Wf.inr dr.toWf
  | abort da => Wf.abort da.toWf
  | unit e => Wf.unit e

-- /-- Infer the type of a term; pun with infimum -/
-- def Term.infTy (Γ : Ctx α ε) : Term φ → Ty α
--   | var n => if h : n < Γ.length then (Γ.get ⟨n, h⟩).1 else Ty.unit
--   | op f _ => Φ.trg f
--   | pair a b => Ty.prod (a.infTy Γ) (b.infTy Γ)
--   | inl a => Ty.coprod (a.infTy Γ) Ty.unit
--   | inr b => Ty.coprod Ty.unit (b.infTy Γ)
--   | unit => Ty.unit

-- theorem Term.WfD.infTy_le {Γ : Ctx α ε} {a : Term φ} {A e} (h : WfD Γ a ⟨A, e⟩) : a.infTy Γ ≤ A
--   := match h with
--   | var dv => by simp [infTy, dv.length, dv.get.left]
--   | op df de => df.trg
--   | prod dl dr => Ty.LE.prod dl.infTy_le dr.infTy_le
--   | unit _ | bool _ _ => le_refl _

-- def Term.WfD.toInfTy {Γ : Ctx α ε} {a : Term φ} {A e} (h : WfD Γ a ⟨A, e⟩) : WfD Γ a ⟨a.infTy Γ, e⟩
--   := match h with
--   | var dv => var (by
--     constructor <;> simp only [infTy, dv.length, ↓reduceDite]
--     exact ⟨le_refl _, dv.get.2⟩
--     )
--   | op df de => op ⟨df.src, le_refl _, df.effect⟩ de
--   | prod dl dr => prod (dl.toInfTy) (dr.toInfTy)
--   | unit e => unit e
--   | bool b e => bool b e

-- TODO: WfD ==> Wf

-- TODO: Wf ==> ∃WfD

-- def Term.Wf.toWfD
--   {Γ : Ctx α ε} {a : Term φ} {V} (h : Wf Γ a V) : WfD Γ a V
--   := match a, V, h with
--   | Term.var _, _, h => WfD.var h.to_var
--   | Term.op _ _, _, h => WfD.op h.to_fn h.to_op.toWfD
--   | Term.pair _ _, ⟨Ty.prod _ _, _⟩, h => WfD.pair h.to_left.toWfD h.to_right.toWfD
--   | Term.inl _, _, h => WfD.inl h.to_left.toWfD
--   | Term.inr _, _, h => WfD.inr h.to_right.toWfD
--   | Term.unit, ⟨Ty.unit, _⟩, _ => WfD.unit _

-- theorem Term.wf_iff_wfD
--   {Γ : Ctx α ε} {a : Term φ} {V} : Wf Γ a V ↔ Nonempty (WfD Γ a V)
--   := ⟨Nonempty.intro ∘ Wf.toWfD, λ⟨h⟩ => h.toWf⟩

-- TODO: for a discrete order on α, WfD unique

inductive Body.WfD : Ctx α ε → Body φ → Ctx α ε → Type _
  | nil : WfD Γ nil []
  | let1 : a.WfD Γ ⟨A, e⟩ → b.WfD (⟨A, ⊥⟩::Γ) Δ → (let1 a b).WfD Γ (⟨A, ⊥⟩::Δ)
  | let2 : a.WfD Γ ⟨(Ty.prod A B), e⟩
    → b.WfD (⟨A, ⊥⟩::⟨B, ⊥⟩::Γ) Δ
    → (let2 a b).WfD Γ (⟨B, ⊥⟩::⟨A, ⊥⟩::Δ)

def Body.WfD.cast_src {Γ Γ' : Ctx α ε} {b : Body φ} {Δ} (h : Γ = Γ') (d : b.WfD Γ Δ)
  : b.WfD Γ' Δ := h ▸ d

def Body.WfD.cast_trg {Γ : Ctx α ε} {b : Body φ} {Δ Δ'} (d : b.WfD Γ Δ) (h : Δ = Δ')
  : b.WfD Γ Δ' := h ▸ d

def Body.WfD.cast_body {Γ : Ctx α ε} {b b' : Body φ} {Δ} (h : b.WfD Γ Δ) (hb : b = b')
  : b'.WfD Γ Δ := hb ▸ h

inductive Body.Wf : Ctx α ε → Body φ → Ctx α ε → Prop
  | nil : Wf Γ nil []
  | let1 : a.Wf Γ ⟨A, e⟩ → b.Wf (⟨A, ⊥⟩::Γ) Δ → (let1 a b).Wf Γ (⟨A, ⊥⟩::Δ)
  | let2 : a.Wf Γ ⟨(Ty.prod A B), e⟩
    → b.Wf (⟨A, ⊥⟩::⟨B, ⊥⟩::Γ) Δ
    → (let2 a b).Wf Γ (⟨B, ⊥⟩::⟨A, ⊥⟩::Δ)

theorem Body.Wf.eq_nil_of_empty_trg {Γ : Ctx α ε} {b : Body φ} (h : Wf Γ b []) : b = Body.nil
  := by cases h; rfl

theorem Body.Wf.empty_trg {Γ : Ctx α ε} (h : Wf Γ (@Body.nil φ) Δ) : Δ = []
  := by cases h; rfl

theorem Body.Wf.empty_trg_iff {Γ : Ctx α ε} {b : Body φ} (h : Wf Γ b Δ)
  : b = Body.nil ↔ Δ = []
  := by constructor <;> intro h' <;> cases h' <;> cases h <;> rfl

theorem Body.Wf.exists_of_let1_binding {Γ : Ctx α ε} {a : Term φ} {b} {Δ}
  (h : Wf Γ (Body.let1 a b) Δ) : ∃V, a.Wf Γ V
  := by cases h; exact ⟨_, by assumption⟩

theorem Body.Wf.exists_trg_of_let1 {Γ : Ctx α ε} {a : Term φ} {b} {Δ}
  (h : Wf Γ (Body.let1 a b) Δ) : ∃A Δ', Δ = ⟨A, ⊥⟩::Δ'
  := by cases h; exact ⟨_, _, rfl⟩

theorem Body.Wf.len_ge_one_of_let1 {Γ : Ctx α ε} {a : Term φ} {b} {Δ}
  (h : Wf Γ (Body.let1 a b) Δ) : 1 ≤ Δ.length
  := by cases h; simp

theorem Body.Wf.trg_nonempty_of_let1 {Γ : Ctx α ε} {a : Term φ} {b} {Δ}
  (h : Wf Γ (Body.let1 a b) Δ) : Δ ≠ []
  := by cases h; simp

theorem Body.Wf.head_eq_of_let1 {Γ : Ctx α ε} {a : Term φ} {b} {Δ}
  (h : Wf Γ (Body.let1 a b) Δ)
  : Δ.head h.trg_nonempty_of_let1 = ⟨(Δ.head h.trg_nonempty_of_let1).1, ⊥⟩
  := by cases h; simp

theorem Body.Wf.of_let1_tail {Γ : Ctx α ε} {a : Term φ} {b} {Δ}
  (h : Wf Γ (Body.let1 a b) Δ) : b.Wf ((Δ.head h.trg_nonempty_of_let1)::Γ) Δ.tail
  := by cases h; assumption

theorem Body.Wf.exists_of_let2_binding {Γ : Ctx α ε} {a : Term φ} {b} {Δ}
  (h : Wf Γ (Body.let2 a b) Δ) : ∃A B e, a.Wf Γ ⟨Ty.prod A B, e⟩
  := by cases h; exact ⟨_, _, _, by assumption⟩

theorem Body.Wf.exists_trg_of_let2 {Γ : Ctx α ε} {a : Term φ} {b} {Δ}
  (h : Wf Γ (Body.let2 a b) Δ) : ∃A B Δ', Δ = ⟨A, ⊥⟩::⟨B, ⊥⟩::Δ'
  := by cases h; exact ⟨_, _, _, rfl⟩

theorem Body.Wf.len_ge_two_of_let2 {Γ : Ctx α ε} {a : Term φ} {b} {Δ}
  (h : Wf Γ (Body.let2 a b) Δ) : 2 ≤ Δ.length
  := by cases h; simp

theorem Body.Wf.trg_nonempty_of_let2 {Γ : Ctx α ε} {a : Term φ} {b} {Δ}
  (h : Wf Γ (Body.let2 a b) Δ) : Δ ≠ []
  := by cases h; simp

theorem Body.Wf.trg_tail_nonempty_of_let2 {Γ : Ctx α ε} {a : Term φ} {b} {Δ}
  (h : Wf Γ (Body.let2 a b) Δ) : Δ.tail ≠ []
  := by cases h; simp

-- theorem Body.Wf.of_let2_tail {Γ : Ctx α ε} {a : Term φ} {b} {Δ}
--   (h : Wf Γ (Body.let2 a b) Δ)
--   : b.Wf ((Δ.head h.trg_nonempty_of_let2)::(Δ.tail.head h.trg_tail_nonempty_of_let2)::Γ) Δ.tail.tail
--   := by cases h; assumption

theorem Body.WfD.num_defs_eq_length {Γ : Ctx α ε} {b : Body φ} {Δ} (h : b.WfD Γ Δ)
  : b.num_defs = Δ.length
  := by induction h <;> simp [num_defs, *]

theorem Body.WfD.toWf {Γ : Ctx α ε} {b : Body φ} {Δ} (h : WfD Γ b Δ) : Wf Γ b Δ
  := match h with
  | Body.WfD.nil => Wf.nil
  | Body.WfD.let1 a b => Wf.let1 a.toWf b.toWf
  | Body.WfD.let2 a b => Wf.let2 a.toWf b.toWf

def LCtx (α) := List (Ty α)

structure LCtx.Trg (L : LCtx α) (n : ℕ) (A : Ty α) : Prop where
  length : n < L.length
  get : A ≤ L.get ⟨n, length⟩

instance : Append (LCtx α) := (inferInstance : Append (List (Ty α)))

instance : Membership (Ty α) (LCtx α) := (inferInstance : Membership (Ty α) (List (Ty α)))

def LCtx.IsInitial (L : LCtx α) : Prop := ∀A ∈ L, Ty.IsInitial A

@[simp]
theorem LCtx.IsInitial.append (L K : LCtx α) : (L ++ K).IsInitial ↔ L.IsInitial ∧ K.IsInitial
  := ⟨
    λh => ⟨λV hV => h V (List.mem_append_left _ hV), λV hV => h V (List.mem_append_right _ hV)⟩,
    λ⟨h, h'⟩ V hV => (List.mem_append.mp hV).elim (h V) (h' V)⟩

def LCtx.take (n : ℕ) (L : LCtx α) : LCtx α := List.take n L

def LCtx.drop (n : ℕ) (L : LCtx α) : LCtx α := List.drop n L

def FLCtx (α) := Σn, Fin n → Ty α

-- TODO: FLCtx append

inductive Terminator.WfD : Ctx α ε → Terminator φ → LCtx α → Type _
  | br : L.Trg n A → a.WfD Γ ⟨A, ⊥⟩ → WfD Γ (br n a) L
  | case : a.WfD Γ ⟨Ty.coprod A B, e⟩
    → s.WfD (⟨A, ⊥⟩::Γ) L
    → t.WfD (⟨B, ⊥⟩::Γ) L
    → WfD Γ (case a s t) L

inductive Terminator.Wf : Ctx α ε → Terminator φ → LCtx α → Prop
  | br : L.Trg n A → a.Wf Γ ⟨A, ⊥⟩ → Wf Γ (br n a) L
  | case : a.Wf Γ ⟨Ty.coprod A B, e⟩
    → s.Wf (⟨A, ⊥⟩::Γ) L
    → t.Wf (⟨B, ⊥⟩::Γ) L
    → Wf Γ (case a s t) L

inductive Terminator.WfJED : Ctx α ε → Terminator φ → LCtx α → Type _
  | br : L.Trg n A → a.WfD Γ ⟨A, e⟩ → WfJED Γ (br n a) L
  | case : a.WfD Γ ⟨Ty.coprod A B, e⟩
    → s.WfJED (⟨A, ⊥⟩::Γ) L
    → t.WfJED (⟨B, ⊥⟩::Γ) L
    → WfJED Γ (case a s t) L

inductive Terminator.WfJE : Ctx α ε → Terminator φ → LCtx α → Prop
  | br : L.Trg n A → a.Wf Γ ⟨A, e⟩ → WfJE Γ (br n a) L
  | case : a.Wf Γ ⟨Ty.coprod A B, e⟩
    → s.WfJE (⟨A, ⊥⟩::Γ) L
    → t.WfJE (⟨B, ⊥⟩::Γ) L
    → WfJE Γ (case a s t) L

structure Block.WfD (Γ : Ctx α ε) (β : Block φ) (Δ : Ctx α ε) (L : LCtx α) where
  body : β.body.WfD Γ Δ
  terminator : β.terminator.WfD (Δ.reverse ++ Γ) L

structure Block.Wf (Γ : Ctx α ε) (β : Block φ) (Δ : Ctx α ε) (L : LCtx α) : Prop where
  body : β.body.Wf Γ Δ
  terminator : β.terminator.Wf (Δ.reverse ++ Γ) L

structure Block.WfJED (Γ : Ctx α ε) (β : Block φ) (Δ : Ctx α ε) (L : LCtx α) where
  body : β.body.WfD Γ Δ
  terminator : β.terminator.WfJED (Δ.reverse ++ Γ) L

structure Block.WfJE (Γ : Ctx α ε) (β : Block φ) (Δ : Ctx α ε) (L : LCtx α) : Prop where
  body : β.body.Wf Γ Δ
  terminator : β.terminator.WfJE (Δ.reverse ++ Γ) L

inductive BBRegion.WfD : Ctx α ε → BBRegion φ → LCtx α → Type _
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.WfD Γ Δ (R ++ L) →
    (∀i : Fin n, (G i).WfD (⟨R.get (i.cast hR.symm), ⊥⟩::(Δ ++ Γ)) (R ++ L)) →
    WfD Γ (cfg β n G) L

inductive BBRegion.Wf : Ctx α ε → BBRegion φ → LCtx α → Prop
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.Wf Γ Δ (R ++ L) →
    (∀i : Fin n, (G i).Wf (⟨R.get (i.cast hR.symm), ⊥⟩::(Δ ++ Γ)) (R ++ L)) →
    Wf Γ (cfg β n G) L

inductive BBRegion.WfJED : Ctx α ε → BBRegion φ → LCtx α → Type _
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.WfJED Γ Δ (R ++ L) →
    (∀i : Fin n, (G i).WfJED (⟨R.get (i.cast hR.symm), ⊥⟩::(Δ ++ Γ)) (R ++ L)) →
    WfJED Γ (cfg β n G) L

inductive BBRegion.WfJE : Ctx α ε → BBRegion φ → LCtx α → Prop
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.WfJE Γ Δ (R ++ L) →
    (∀i : Fin n, (G i).WfJE (⟨R.get (i.cast hR.symm), ⊥⟩::(Δ ++ Γ)) (R ++ L)) →
    WfJE Γ (cfg β n G) L

inductive TRegion.WfD : Ctx α ε → TRegion φ → LCtx α → Type _
  | let1 : a.WfD Γ ⟨A, e⟩ → t.WfD (⟨A, ⊥⟩::Γ) L → (let1 a t).WfD Γ L
  | let2 : a.WfD Γ ⟨(Ty.prod A B), e⟩ → t.WfD (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L → (let2 a t).WfD Γ L
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.WfD Γ (R ++ L) →
    (∀i : Fin n, (G i).WfD (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    WfD Γ (cfg β n G) L

inductive TRegion.Wf : Ctx α ε → TRegion φ → LCtx α → Prop
  | let1 : a.Wf Γ ⟨A, e⟩ → t.Wf (⟨A, ⊥⟩::Γ) L → (let1 a t).Wf Γ L
  | let2 : a.Wf Γ ⟨(Ty.prod A B), e⟩ → t.Wf (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L → (let2 a t).Wf Γ L
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.Wf Γ (R ++ L) →
    (∀i : Fin n, (G i).Wf (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    Wf Γ (cfg β n G) L

inductive TRegion.WfJED : Ctx α ε → TRegion φ → LCtx α → Type _
  | let1 : a.WfD Γ ⟨A, e⟩ → t.WfJED (⟨A, ⊥⟩::Γ) L → (let1 a t).WfJED Γ L
  | let2 : a.WfD Γ ⟨(Ty.prod A B), e⟩ → t.WfJED (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L → (let2 a t).WfJED Γ L
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.WfJED Γ (R ++ L) →
    (∀i : Fin n, (G i).WfJED (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    WfJED Γ (cfg β n G) L

inductive TRegion.WfJE : Ctx α ε → TRegion φ → LCtx α → Prop
  | let1 : a.Wf Γ ⟨A, e⟩ → t.WfJE (⟨A, ⊥⟩::Γ) L → (let1 a t).WfJE Γ L
  | let2 : a.Wf Γ ⟨(Ty.prod A B), e⟩ → t.WfJE (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L → (let2 a t).WfJE Γ L
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.WfJE Γ (R ++ L) →
    (∀i : Fin n, (G i).WfJE (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    WfJE Γ (cfg β n G) L

inductive Region.WfD : Ctx α ε → Region φ → LCtx α → Type _
  | br : L.Trg n A → a.WfD Γ ⟨A, ⊥⟩ → WfD Γ (br n a) L
  | case : e.WfD Γ ⟨Ty.coprod A B, ⊥⟩
    → s.WfD (⟨A, ⊥⟩::Γ) L
    → t.WfD (⟨B, ⊥⟩::Γ) L
    → WfD Γ (case e s t) L
  | let1 : a.WfD Γ ⟨A, e⟩ → t.WfD (⟨A, ⊥⟩::Γ) L → (let1 a t).WfD Γ L
  | let2 : a.WfD Γ ⟨(Ty.prod A B), e⟩ → t.WfD (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L → (let2 a t).WfD Γ L
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.WfD Γ (R ++ L) →
    (∀i : Fin n, (G i).WfD (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    WfD Γ (cfg β n G) L

inductive Region.Wf : Ctx α ε → Region φ → LCtx α → Prop
  | br : L.Trg n A → a.Wf Γ ⟨A, ⊥⟩ → Wf Γ (br n a) L
  | case : a.Wf Γ ⟨Ty.coprod A B, e⟩
    → s.Wf (⟨A, ⊥⟩::Γ) L
    → t.Wf (⟨B, ⊥⟩::Γ) L
    → Wf Γ (case a s t) L
  | let1 : a.Wf Γ ⟨A, e⟩ → t.Wf (⟨A, ⊥⟩::Γ) L → (let1 a t).Wf Γ L
  | let2 : a.Wf Γ ⟨(Ty.prod A B), e⟩ → t.Wf (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L → (let2 a t).Wf Γ L
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.Wf Γ (R ++ L) →
    (∀i : Fin n, (G i).Wf (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    Wf Γ (cfg β n G) L

inductive Region.WfJED : Ctx α ε → Region φ → LCtx α → Type _
  | br : L.Trg n A → a.WfD Γ ⟨A, e⟩ → WfJED Γ (br n a) L
  | case : a.WfD Γ ⟨Ty.coprod A B, e⟩
    → s.WfJED (⟨A, ⊥⟩::Γ) L
    → t.WfJED (⟨B, ⊥⟩::Γ) L
    → WfJED Γ (case a s t) L
  | let1 : a.WfD Γ ⟨A, e⟩ → t.WfJED (⟨A, ⊥⟩::Γ) L → (let1 a t).WfJED Γ L
  | let2 : a.WfD Γ ⟨(Ty.prod A B), e⟩ → t.WfJED (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L → (let2 a t).WfJED Γ L
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.WfJED Γ (R ++ L) →
    (∀i : Fin n, (G i).WfJED (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    WfJED Γ (cfg β n G) L

inductive Region.WfJE : Ctx α ε → Region φ → LCtx α → Prop
  | br : L.Trg n A → a.Wf Γ ⟨A, e⟩ → WfJE Γ (br n a) L
  | case : a.Wf Γ ⟨Ty.coprod A B, e⟩
    → s.WfJE (⟨A, ⊥⟩::Γ) L
    → t.WfJE (⟨B, ⊥⟩::Γ) L
    → WfJE Γ (case a s t) L
  | let1 : a.Wf Γ ⟨A, e⟩ → t.WfJE (⟨A, ⊥⟩::Γ) L → (let1 a t).WfJE Γ L
  | let2 : a.Wf Γ ⟨(Ty.prod A B), e⟩ → t.WfJE (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L → (let2 a t).WfJE Γ L
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.WfJE Γ (R ++ L) →
    (∀i : Fin n, (G i).WfJE (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    WfJE Γ (cfg β n G) L

def Region.WfD.src {Γ : Ctx α ε} {r : Region φ} {L} (_ : r.WfD Γ L) := Γ

def Region.WfD.trg {Γ : Ctx α ε} {r : Region φ} {L} (_ : r.WfD Γ L) := L

def Region.WfD.tm {Γ : Ctx α ε} {r : Region φ} {L} (_ : r.WfD Γ L) := r

def Region.WfD.cfg_arity {Γ : Ctx α ε} {β : Region φ} {n G} {L}
  (_ : (Region.cfg β n G).WfD Γ L) : ℕ := n

-- TODO: normalize region to TRegion; type preservation

-- TODO: normalize TRegion to BBRegion; type preservation

end Basic

section Weakening

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]
  {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} -- {a b : Term φ} {A B : Ty α} {e e' : ε}

def Ctx.Wkn (Γ Δ : Ctx α ε) (ρ : ℕ → ℕ) : Prop -- TODO: fin argument as defeq?
  := ∀i, (h : i < Δ.length) → Γ.Var (ρ i) (Δ.get ⟨i, h⟩)

theorem Ctx.Wkn_def (Γ Δ : Ctx α ε) (ρ : ℕ → ℕ) : Γ.Wkn Δ ρ ↔
  ∀i, (h : i < Δ.length) → Γ.Var (ρ i) (Δ.get ⟨i, h⟩) := Iff.rfl

theorem Ctx.Wkn_def' (Γ Δ : Ctx α ε) (ρ : ℕ → ℕ) : Γ.Wkn Δ ρ ↔
  ∀i : Fin Δ.length, Γ.Var (ρ i) (Δ.get i) := ⟨λh ⟨i, hi⟩ => h i hi, λh i hi => h ⟨i, hi⟩⟩

theorem Ctx.Wkn_iff (Γ Δ : Ctx α ε) (ρ : ℕ → ℕ) : Γ.Wkn Δ ρ ↔ List.NWkn Γ Δ ρ
  := ⟨λh i hi => have h' := h i hi; ⟨h'.length, h'.get⟩, λh i hi => have h' := h i hi; ⟨h'.1, h'.2⟩⟩

@[simp]
theorem Ctx.Wkn.id {Γ : Ctx α ε} : Γ.Wkn Γ id := λ_ hi => ⟨hi, le_refl _⟩

theorem Ctx.Wkn.lift {V V' : Ty α × ε} (hV : V ≤ V') (h : Γ.Wkn Δ ρ)
  : Wkn (V::Γ) (V'::Δ) (Nat.liftWk ρ)
  := (Wkn_iff _ _ _).mpr (((Wkn_iff _ _ _).mp h).lift hV)

theorem Ctx.Wkn.lift_tail {head head' : Ty α × ε} (h : Wkn (head::Γ) (head'::Δ) (Nat.liftWk ρ))
  : Wkn Γ Δ ρ := λi hi => Var.of_step (h (i + 1) (Nat.succ_lt_succ hi))

theorem Ctx.Wkn.lift_head {head head' : Ty α × ε} (h : Wkn (head::Γ) (head'::Δ) (Nat.liftWk ρ))
  : head ≤ head'
  := sorry

theorem Ctx.Wkn.slift {head : Ty α × ε} (h : Γ.Wkn Δ ρ)
  : Wkn (head::Γ) (head::Δ) (Nat.liftWk ρ)
  := h.lift (le_refl head)

theorem Ctx.Wkn.lift_id {V V' : Ty α × ε} (hV : V ≤ V') (h : Γ.Wkn Δ _root_.id)
  : Wkn (V::Γ) (V'::Δ) _root_.id
  := Nat.liftWk_id ▸ h.lift hV

theorem Ctx.Wkn.slift_id {head : Ty α × ε} (h : Γ.Wkn Δ _root_.id)
  : Wkn (head::Γ) (head::Δ) _root_.id
  := h.lift_id (le_refl _)

theorem Ctx.Wkn.step {head : Ty α × ε} (h : Γ.Wkn Δ ρ) : Wkn (head::Γ) Δ (Nat.stepWk ρ)
  := (Wkn_iff _ _ _).mpr (((Wkn_iff _ _ _).mp h).step _)

theorem Ctx.Wkn.succ {head} {Γ : Ctx α ε}
  : Wkn (head::Γ) Γ Nat.succ
  := step (head := head) (id (Γ := Γ))

theorem Ctx.Wkn.wk1 {head inserted} {Γ : Ctx α ε}
  : Wkn (head::inserted::Γ) (head::Γ) (Nat.liftWk Nat.succ)
  := succ.slift

theorem Ctx.Wkn.lift₂ {V₁ V₁' V₂ V₂' : Ty α × ε} (hV₁ : V₁ ≤ V₁') (hV₂ : V₂ ≤ V₂') (h : Γ.Wkn Δ ρ)
  : Wkn (V₁::V₂::Γ) (V₁'::V₂'::Δ) (Nat.liftWk (Nat.liftWk ρ))
  := (Wkn_iff _ _ _).mpr (((Wkn_iff _ _ _).mp h).lift₂ hV₁ hV₂)

theorem Ctx.Wkn.slift₂ {left right : Ty α × ε} (h : Γ.Wkn Δ ρ)
  : Wkn (left::right::Γ) (left::right::Δ) (Nat.liftWk (Nat.liftWk ρ))
  := h.lift₂ (le_refl _) (le_refl _)

theorem Ctx.Wkn.lift_id₂ {V₁ V₁' V₂ V₂' : Ty α × ε} (hV₁ : V₁ ≤ V₁') (hV₂ : V₂ ≤ V₂') (h : Γ.Wkn Δ _root_.id)
  : Wkn (V₁::V₂::Γ) (V₁'::V₂'::Δ) _root_.id
  := Nat.liftWk_id ▸ Nat.liftWk_id ▸ h.lift₂ hV₁ hV₂

theorem Ctx.Wkn.slift_id₂ (V₁ V₂ : Ty α × ε) (h : Γ.Wkn Δ _root_.id)
  : Wkn (V₁::V₂::Γ) (V₁::V₂::Δ) _root_.id
  := h.lift_id₂ (le_refl _) (le_refl _)

theorem Ctx.Wkn.liftn₂ {V₁ V₁' V₂ V₂' : Ty α × ε} (hV₁ : V₁ ≤ V₁') (hV₂ : V₂ ≤ V₂') (h : Γ.Wkn Δ ρ)
  : Wkn (V₁::V₂::Γ) (V₁'::V₂'::Δ) (Nat.liftnWk 2 ρ)
  := (Wkn_iff _ _ _).mpr (((Wkn_iff _ _ _).mp h).liftn₂ hV₁ hV₂)

theorem Ctx.Wkn.sliftn₂ {left right : Ty α × ε} (h : Γ.Wkn Δ ρ)
  : Wkn (left::right::Γ) (left::right::Δ) (Nat.liftnWk 2 ρ)
  := h.liftn₂ (le_refl _) (le_refl _)

theorem Ctx.Wkn.liftn_id₂ {V₁ V₁' V₂ V₂' : Ty α × ε} (hV₁ : V₁ ≤ V₁') (hV₂ : V₂ ≤ V₂') (h : Γ.Wkn Δ _root_.id)
  : Wkn (V₁::V₂::Γ) (V₁'::V₂'::Δ) _root_.id
  := Nat.liftnWk_id 2 ▸ h.liftn₂ hV₁ hV₂

theorem Ctx.Wkn.sliftn_id₂ (V₁ V₂ : Ty α × ε) (h : Γ.Wkn Δ _root_.id)
  : Wkn (V₁::V₂::Γ) (V₁::V₂::Δ) _root_.id
  := h.liftn_id₂ (le_refl _) (le_refl _)

theorem Ctx.Wkn.liftn_append (Ξ) (h : Γ.Wkn Δ ρ)
  : Wkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk Ξ.length ρ)
  := (Wkn_iff _ _ _).mpr (((Wkn_iff _ _ _).mp h).liftn_append Ξ)

theorem Ctx.Wkn.liftn_append' {Ξ} (hn : n = Ξ.length) (h : Γ.Wkn Δ ρ)
  : Wkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk n ρ)
  := hn ▸ liftn_append Ξ h

theorem Ctx.Wkn.liftn_append_id (Ξ) (h : Γ.Wkn Δ _root_.id)
  : Wkn (Ξ ++ Γ) (Ξ ++ Δ) _root_.id
  := Nat.liftnWk_id _ ▸ liftn_append Ξ h

theorem Ctx.Wkn.liftn_append_cons (A Ξ) (h : Γ.Wkn Δ ρ)
  : Wkn (A::(Ξ ++ Γ)) (A::(Ξ ++ Δ)) (Nat.liftnWk (Ξ.length + 1) ρ)
  := liftn_append (A::Ξ) h

theorem Ctx.Wkn.liftn_append_cons' (A) {Ξ} (hn : n = Ξ.length + 1) (h : Γ.Wkn Δ ρ)
  : Wkn (A::(Ξ ++ Γ)) (A::(Ξ ++ Δ)) (Nat.liftnWk n ρ)
  := hn ▸ liftn_append_cons A Ξ h

theorem Ctx.Wkn.liftn_append_cons_id (A Ξ) (h : Γ.Wkn Δ _root_.id)
  : Wkn (A::(Ξ ++ Γ)) (A::(Ξ ++ Δ)) _root_.id
  := Nat.liftnWk_id _ ▸  liftn_append_cons A Ξ h

theorem Ctx.Wkn.stepn_append (Ξ) (h : Γ.Wkn Δ ρ)
  : Wkn (Ξ ++ Γ) Δ (Nat.stepnWk Ξ.length ρ)
  := (Wkn_iff _ _ _).mpr (((Wkn_iff _ _ _).mp h).stepn_append Ξ)

theorem Ctx.Wkn.stepn_append' {Ξ} (hn : n = Ξ.length) (h : Γ.Wkn Δ ρ)
  : Wkn (Ξ ++ Γ) Δ (Nat.stepnWk n ρ)
  := hn ▸ stepn_append Ξ h

theorem Ctx.Wkn.id_len_le : Γ.Wkn Δ _root_.id → Δ.length ≤ Γ.length := by
  rw [Wkn_iff]; apply List.NWkn.id_len_le

def Ctx.Types (Γ : Ctx α ε) : List (Ty α) := Γ.map Prod.fst

theorem Ctx.length_types (Γ : Ctx α ε) : Γ.Types.length = Γ.length := by
  simp [Ctx.Types]

def Ctx.Effects (Γ : Ctx α ε) : List ε := Γ.map Prod.snd

theorem Ctx.length_effects (Γ : Ctx α ε) : Γ.Effects.length = Γ.length := by
  simp [Ctx.Effects]

def Ctx.WknTy (Γ Δ : Ctx α ε) (ρ : ℕ → ℕ) : Prop := Γ.Types.NWkn Δ.Types ρ

theorem Ctx.WknTy.id_types_len_le : Γ.WknTy Δ _root_.id → Δ.Types.length ≤ Γ.Types.length
  := List.NWkn.id_len_le

theorem Ctx.WknTy.id_len_le : Γ.WknTy Δ _root_.id → Δ.length ≤ Γ.length
  := Δ.length_types ▸ Γ.length_types ▸ Ctx.WknTy.id_types_len_le

theorem Ctx.Var.wk_res (h : V ≤ V') (hΓ : Γ.Var n V) : Γ.Var n V' where
  length := hΓ.length
  get := le_trans hΓ.get h

theorem Ctx.Var.wk_res₂ (hA : A ≤ A') (he : e ≤ e') (hΓ : Γ.Var n ⟨A, e⟩) : Γ.Var n ⟨A', e⟩
  := hΓ.wk_res (by simp [hA, he])

theorem Ctx.Var.wk_ty (h : A ≤ A') (hΓ : Γ.Var n ⟨A, e⟩) : Γ.Var n ⟨A', e⟩
  := hΓ.wk_res (by simp [h])

theorem Ctx.Var.wk_eff (h : e ≤ e') (hΓ : Γ.Var n ⟨A, e⟩) : Γ.Var n ⟨A, e'⟩
  := hΓ.wk_res (by simp [h])

theorem Ctx.Var.wk (h : Γ.Wkn Δ ρ) (hΓ : Δ.Var n ⟨A, e⟩) : Γ.Var (ρ n) ⟨A, e⟩ where
  length := (h n hΓ.length).1
  get := le_trans (h n hΓ.length).2 hΓ.get

/-- Weaken the effect of a term derivation -/
def Term.WfD.wk_eff {a : Term φ} {A e} (h : e ≤ e') : WfD Γ a ⟨A, e⟩ → WfD Γ a ⟨A, e'⟩
  | var dv => var (dv.wk_eff h)
  | op df de => op (df.wk_eff h) (de.wk_eff h)
  | pair dl dr => pair (dl.wk_eff h) (dr.wk_eff h)
  | inl dl => inl (dl.wk_eff h)
  | inr dr => inr (dr.wk_eff h)
  | abort da => abort (da.wk_eff h)
  | unit e => unit e'

/-- Weaken the type of a term derivation -/
def Term.WfD.wk_ty {a : Term φ} {A e} (h : A ≤ A') (da : WfD Γ a ⟨A, e⟩) : WfD Γ a ⟨A', e⟩
  := match da, A', h with
  | var dv, _, h => var (dv.wk_ty h)
  | op df de, _, h => op (df.wk_trg h) de
  | pair dl dr, Ty.prod A B, h => pair (dl.wk_ty h.prod_left) (dr.wk_ty h.prod_right)
  | inl dl, Ty.coprod A B, h => inl (dl.wk_ty h.coprod_left)
  | inr dr, Ty.coprod A B, h => inr (dr.wk_ty h.coprod_right)
  | abort da, _, h => abort da
  | unit e, Ty.unit, h => unit e

/-- Weaken the result of a term derivation -/
def Term.WfD.wk_res₂ {a : Term φ} (hA : A ≤ A') (he : e ≤ e') (da : WfD Γ a ⟨A, e⟩)
  : WfD Γ a ⟨A', e'⟩ := da.wk_eff he |>.wk_ty hA

/-- Weaken the result of a term derivation -/
def Term.WfD.wk_res {a : Term φ} (h : V ≤ V') (da : WfD Γ a V) : WfD Γ a V'
  := match V, V', h with
  | ⟨_, _⟩, ⟨_, _⟩, ⟨hA, he⟩ => da.wk_res₂ hA he

/-- Weaken a term derivation -/
def Term.WfD.wk {a : Term φ} (h : Γ.Wkn Δ ρ) : WfD Δ a ⟨A, e⟩ → WfD Γ (a.wk ρ) ⟨A, e⟩
  | var dv => var (dv.wk h)
  | op df de => op df (de.wk h)
  | pair dl dr => pair (dl.wk h) (dr.wk h)
  | inl dl => inl (dl.wk h)
  | inr dr => inr (dr.wk h)
  | abort da => abort (da.wk h)
  | unit e => unit e

def Term.WfD.wk1 {Γ : Ctx α ε} {L} {r : Term φ} (dr : WfD (A::Γ) r L) : WfD (A::B::Γ) r.wk1 L
  := dr.wk Ctx.Wkn.wk1

def Term.WfD.wk0 {Γ : Ctx α ε} {L} {r : Term φ} (dr : WfD Γ r L)
  : WfD (A::Γ) (r.wk Nat.succ) L
  := dr.wk Ctx.Wkn.succ

def Term.WfD.wk_id {a : Term φ} (h : Γ.Wkn Δ id) : WfD Δ a ⟨A, e⟩ → WfD Γ a ⟨A, e⟩
  | var dv => var (dv.wk h)
  | op df de => op df (de.wk_id h)
  | pair dl dr => pair (dl.wk_id h) (dr.wk_id h)
  | inl dl => inl (dl.wk_id h)
  | inr dr => inr (dr.wk_id h)
  | abort da => abort (da.wk_id h)
  | unit e => unit e

def Body.WfD.wk {Γ Δ : Ctx α ε} {ρ} {b : Body φ} (h : Γ.Wkn Δ ρ) : WfD Δ b Ξ → WfD Γ (b.wk ρ) Ξ
  | nil => nil
  | let1 a b => let1 (a.wk h) (b.wk h.slift)
  | let2 a b => let2 (a.wk h) (b.wk h.sliftn₂)

def Body.WfD.wk_id {Γ Δ : Ctx α ε} {b : Body φ} (h : Γ.Wkn Δ id) : WfD Δ b Ξ → WfD Γ b Ξ
  | nil => nil
  | let1 a b => let1 (a.wk_id h) (b.wk_id (Nat.liftWk_id ▸ h.slift))
  | let2 a b => let2 (a.wk_id h) (b.wk_id (Nat.liftnWk_id 2 ▸ h.sliftn₂))

variable {L K : LCtx α}

def LCtx.Wkn (L K : LCtx α) (ρ : ℕ → ℕ) : Prop -- TODO: fin argument as defeq?
  := ∀i, (h : i < L.length) → K.Trg (ρ i) (L.get ⟨i, h⟩)

theorem LCtx.Wkn.id (L : LCtx α) : L.Wkn L id := λ_ hi => ⟨hi, le_refl _⟩

theorem LCtx.Wkn_def (L K : LCtx α) (ρ : ℕ → ℕ) : L.Wkn K ρ ↔
  ∀i, (h : i < L.length) → K.Trg (ρ i) (L.get ⟨i, h⟩) := Iff.rfl

theorem LCtx.Wkn_def' (L K : LCtx α) (ρ : ℕ → ℕ) : L.Wkn K ρ ↔
  ∀i : Fin L.length, K.Trg (ρ i) (L.get i) := ⟨λh ⟨i, hi⟩ => h i hi, λh i hi => h ⟨i, hi⟩⟩

theorem LCtx.Wkn_iff (L K : LCtx α) (ρ : ℕ → ℕ) : L.Wkn K ρ ↔ @List.NWkn (Ty α)ᵒᵈ _ K L ρ
  := ⟨λh i hi => have h' := h i hi; ⟨h'.length, h'.get⟩, λh i hi => have h' := h i hi; ⟨h'.1, h'.2⟩⟩

theorem LCtx.Wkn.step {A : Ty α} (h : L.Wkn K ρ) : Wkn L (A::K) (Nat.stepWk ρ)
  := (Wkn_iff _ _ _).mpr (((Wkn_iff _ _ _).mp h).step _)

theorem LCtx.Wkn.liftn_append {L K : LCtx α} {ρ : ℕ → ℕ} (R : LCtx α) (h : L.Wkn K ρ)
  : (R ++ L).Wkn (R ++ K) (Nat.liftnWk R.length ρ) := by
  rw [LCtx.Wkn_iff]
  apply List.NWkn.liftn_append
  rw [<-LCtx.Wkn_iff]
  exact h

theorem LCtx.Trg.wk (h : L.Wkn K ρ) (hK : L.Trg n A) : K.Trg (ρ n) A where
  length := (h n hK.length).1
  get := le_trans hK.get (h n hK.length).2

def Terminator.WfD.vwk {Γ Δ : Ctx α ε} {ρ} {t : Terminator φ} (h : Γ.Wkn Δ ρ)
  : WfD Δ t L → WfD Γ (t.vwk ρ) L
  | br hL ha => br hL (ha.wk h)
  | case he hs ht => case (he.wk h) (hs.vwk h.slift) (ht.vwk h.slift)

def Terminator.WfD.vwk_id {Γ Δ : Ctx α ε} {t : Terminator φ} (h : Γ.Wkn Δ id)
  : WfD Δ t L → WfD Γ t L
  | br hL ha => br hL (ha.wk_id h)
  | case he hs ht => case (he.wk_id h) (hs.vwk_id h.slift_id) (ht.vwk_id h.slift_id)

def Terminator.WfD.lwk {Γ : Ctx α ε} {t : Terminator φ} (h : L.Wkn K ρ)
  : WfD Γ t L → WfD Γ (t.lwk ρ) K
  | br hL ha => br (hL.wk h) ha
  | case he hs ht => case he (hs.lwk h) (ht.lwk h)

def Block.WfD.vwk {β : Block φ} (h : Γ.Wkn Δ ρ) (hβ : WfD Δ β Ξ L) : WfD Γ (β.vwk ρ) Ξ L where
  body := hβ.body.wk h
  terminator := hβ.terminator.vwk
    (hβ.body.num_defs_eq_length ▸ (h.liftn_append' (by simp [Ctx.reverse])))

def Block.WfD.vwk_id {β : Block φ} (h : Γ.Wkn Δ id) (hβ : WfD Δ β Ξ L) : WfD Γ β Ξ L where
  body := hβ.body.wk_id h
  terminator := hβ.terminator.vwk_id (h.liftn_append_id _)

def Block.WfD.lwk {β : Block φ} (h : L.Wkn K ρ) (hβ : WfD Γ β Ξ L) : WfD Γ (β.lwk ρ) Ξ K where
  body := hβ.body
  terminator := hβ.terminator.lwk h

def BBRegion.WfD.vwk {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} {L} {r : BBRegion φ} (h : Γ.Wkn Δ ρ)
  : WfD Δ r L → WfD Γ (r.vwk ρ) L
  | cfg n R hR hβ hG =>
    cfg n R hR (hβ.vwk h) (λi => (hG i).vwk (hβ.body.num_defs_eq_length ▸ h.liftn_append_cons _ _))

def BBRegion.WfD.vwk_id {Γ Δ : Ctx α ε} {L} {r : BBRegion φ} (h : Γ.Wkn Δ id)
  : WfD Δ r L → WfD Γ r L
  | cfg n R hR hβ hG =>
    cfg n R hR (hβ.vwk_id h) (λi => (hG i).vwk_id (h.liftn_append_cons_id _ _))

def BBRegion.WfD.lwk {Γ : Ctx α ε} {ρ : ℕ → ℕ} {L K : LCtx α} {r : BBRegion φ} (h : L.Wkn K ρ)
  : WfD Γ r L → WfD Γ (r.lwk ρ) K
  | cfg n R hR hβ hG =>
    have trg_wk : (R ++ L).Wkn (R ++ K) (Nat.liftnWk n ρ) := hR ▸ h.liftn_append R
    cfg n R hR (hβ.lwk trg_wk) (λi => (hG i).lwk trg_wk)

def TRegion.WfD.vwk {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} {L} {r : TRegion φ} (h : Γ.Wkn Δ ρ)
  : WfD Δ r L → WfD Γ (r.vwk ρ) L
  | let1 ha ht => let1 (ha.wk h) (ht.vwk h.slift)
  | let2 ha ht => let2 (ha.wk h) (ht.vwk h.sliftn₂)
  | cfg n R hR hr hG => cfg n R hR (hr.vwk h) (λi => (hG i).vwk h.slift)

def TRegion.WfD.vwk_id {Γ Δ : Ctx α ε} {L} {r : TRegion φ} (h : Γ.Wkn Δ id)
  : WfD Δ r L → WfD Γ r L
  | let1 ha ht => let1 (ha.wk_id h) (ht.vwk_id h.slift_id)
  | let2 ha ht => let2 (ha.wk_id h) (ht.vwk_id (h.slift_id₂ _ _))
  | cfg n R hR hr hG => cfg n R hR (hr.vwk_id h) (λi => (hG i).vwk_id h.slift_id)

def TRegion.WfD.lwk {Γ : Ctx α ε} {ρ : ℕ → ℕ} {L K : LCtx α} {r : TRegion φ} (h : L.Wkn K ρ)
  : WfD Γ r L → WfD Γ (r.lwk ρ) K
  | let1 ha ht => let1 ha (ht.lwk h)
  | let2 ha ht => let2 ha (ht.lwk h)
  | cfg n R hR hr hG =>
    have trg_wk : (R ++ L).Wkn (R ++ K) (Nat.liftnWk n ρ) := hR ▸ h.liftn_append R
    cfg n R hR (hr.lwk trg_wk) (λi => (hG i).lwk trg_wk)

def Region.WfD.vwk {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} {L} {r : Region φ} (h : Γ.Wkn Δ ρ)
  : WfD Δ r L → WfD Γ (r.vwk ρ) L
  | br hL ha => br hL (ha.wk h)
  | case he hs ht => case (he.wk h) (hs.vwk h.slift) (ht.vwk h.slift)
  | let1 ha ht => let1 (ha.wk h) (ht.vwk h.slift)
  | let2 ha ht => let2 (ha.wk h) (ht.vwk h.sliftn₂)
  | cfg n R hR hr hG => cfg n R hR (hr.vwk h) (λi => (hG i).vwk h.slift)

def Region.WfD.vwk1 {Γ : Ctx α ε} {L} {r : Region φ} (dr : WfD (A::Γ) r L) : WfD (A::B::Γ) r.vwk1 L
  := dr.vwk Ctx.Wkn.wk1

def Region.WfD.vwk0 {Γ : Ctx α ε} {L} {r : Region φ} (dr : WfD Γ r L)
  : WfD (A::Γ) (r.vwk Nat.succ) L
  := dr.vwk Ctx.Wkn.succ

def Region.WfD.vwk_id {Γ Δ : Ctx α ε} {L} {r : Region φ} (h : Γ.Wkn Δ id)
  : WfD Δ r L → WfD Γ r L
  | br hL ha => br hL (ha.wk_id h)
  | case he hs ht => case (he.wk_id h) (hs.vwk_id h.slift_id) (ht.vwk_id h.slift_id)
  | let1 ha ht => let1 (ha.wk_id h) (ht.vwk_id h.slift_id)
  | let2 ha ht => let2 (ha.wk_id h) (ht.vwk_id (h.slift_id₂ _ _))
  | cfg n R hR hr hG => cfg n R hR (hr.vwk_id h) (λi => (hG i).vwk_id h.slift_id)

def Region.WfD.lwk {Γ : Ctx α ε} {ρ : ℕ → ℕ} {L K : LCtx α} {r : Region φ} (h : L.Wkn K ρ)
  : WfD Γ r L → WfD Γ (r.lwk ρ) K
  | br hL ha => br (hL.wk h) ha
  | case he hs ht => case he (hs.lwk h) (ht.lwk h)
  | let1 ha ht => let1 ha (ht.lwk h)
  | let2 ha ht => let2 ha (ht.lwk h)
  | cfg n R hR hβ hG =>
    have trg_wk : (R ++ L).Wkn (R ++ K) (Nat.liftnWk n ρ) := hR ▸ h.liftn_append R
    cfg n R hR (hβ.lwk trg_wk) (λi => (hG i).lwk trg_wk)

end Weakening

section OrderBot

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [OrderBot ε]

def Ctx.var_bot_head {Γ : Ctx α ε} : Var (⟨A, ⊥⟩::Γ) 0 ⟨A, e⟩
  := Var.head (by simp) Γ

end OrderBot

section Minimal

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

def Term.WfD.var0_pure {ty} {Γ : Ctx α ε} {effect}
  : WfD (⟨ty, ⊥⟩::Γ) (@Term.var φ 0) ⟨ty, effect⟩
  := var (by simp)

def Term.WfD.var1_pure {head ty} {Γ : Ctx α ε} {effect}
  : WfD (head::⟨ty, ⊥⟩::Γ) (@Term.var φ 1) ⟨ty, effect⟩
  := var (by simp)

theorem Term.WfD.effect_le
  {Γ : Ctx α ε} {a : Term φ} {A e} (h : WfD Γ a ⟨A, e⟩) : a.effect Γ.effect ≤ e
  := match h with
  | var dv => by simp [Ctx.effect, effect, dv.length, dv.get.right]
  | op df de => sup_le_iff.mpr ⟨df.effect, de.effect_le⟩
  | pair dl dr => sup_le_iff.mpr ⟨dl.effect_le, dr.effect_le⟩
  | inl dl => dl.effect_le
  | inr dr => dr.effect_le
  | abort da => da.effect_le
  | unit _ => bot_le

def Ctx.Var.toEffect {Γ : Ctx α ε} {n : ℕ} {V} (h : Γ.Var n V)
  : Γ.Var n ⟨V.1, Γ.effect n⟩
  := ⟨h.length, by
    constructor
    exact h.get.1
    simp [Ctx.effect, h.length]
  ⟩

def Term.WfD.toEffect {Γ : Ctx α ε} {a : Term φ} {V}
  : WfD Γ a V → WfD Γ a ⟨V.1, a.effect Γ.effect⟩
  | var dv => var dv.toEffect
  | op df de => op
    ⟨⟨df.src, df.trg⟩, by simp [effect]⟩
    (de.toEffect.wk_eff (by simp [effect]))
  | pair dl dr => pair
    (dl.toEffect.wk_eff (by simp [effect]))
    (dr.toEffect.wk_eff (by simp [effect]))
  | inl dl => inl dl.toEffect
  | inr dr => inr dr.toEffect
  | abort da => abort da.toEffect
  | unit e => unit ⊥

-- def Body.minDefs (Γ : Ctx α ε) : Body φ → Ctx α ε
--   | Body.nil => []
--   | Body.let1 a b => ⟨a.infTy Γ, ⊥⟩ :: b.minDefs (⟨a.infTy Γ, ⊥⟩::Γ)
--   | Body.let2 a b =>
--     ⟨a.infTy Γ, ⊥⟩ :: ⟨a.infTy Γ, ⊥⟩ :: b.minDefs (⟨a.infTy Γ, ⊥⟩::⟨a.infTy Γ, ⊥⟩::Γ)

-- TODO: ...
-- def Body.Wf.toWfD {Γ : Ctx α ε} {b : Body φ} {Δ} (h : Wf Γ b Δ) : WfD Γ b Δ
--   := match b, Δ, h with
--   | Body.nil, [], _ => WfD.nil
--   | Body.let1 a b, ⟨A, e⟩::Δ, _ => sorry--WfD.let1 sorry sorry
--   | Body.let2 a b, ⟨A, e⟩::⟨B, e'⟩::Δ, _ => sorry

-- def Body.WfD.toMinDefs {Γ : Ctx α ε} {b : Body φ} {Δ} : b.WfD Γ Δ → WfD Γ b (b.minDefs Γ)
--   | Body.WfD.nil => nil
--   | Body.WfD.let1 a b => let1 a.toInfTy (b.wk_id sorry).toMinDefs
--   | Body.WfD.let2 a b => let2 a.toInfTy (b.wk_id sorry).toMinDefs

end Minimal

-- == SPECULATIVE ==

-- TODO: FWfD, FWf, associated lore

-- TODO: propositional variants for below...

-- TODO: substitution-terminator typing

-- TODO: substitution-CFG typing

-- TODO: _partial_ substitutions for more standard SSA? parameter tagging?

-- TODO: 3 address code via var-only substitution; everything trivially SSA with preserved vars
-- via id-substitution.

end BinSyntax
