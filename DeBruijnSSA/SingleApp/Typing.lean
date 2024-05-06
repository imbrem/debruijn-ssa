import Discretion.Wk.Basic
import DeBruijnSSA.SingleApp.Syntax
import DeBruijnSSA.InstSet

namespace SingleApp

variable [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Zero ε]

  inductive Ty (α : Type u) where
  | base : α → Ty α
  | pair : Ty α → Ty α → Ty α
  | unit : Ty α
  | bool : Ty α
  deriving Repr, DecidableEq

inductive Ty.LE : Ty α → Ty α → Prop where
  | base {x y} : x ≤ y → LE (base x) (base y)
  | pair {x₁ x₂ y₁ y₂} : LE x₁ y₁ → LE x₂ y₂ → LE (pair x₁ x₂) (pair y₁ y₂)
  | unit : LE unit unit
  | bool : LE bool bool

theorem Ty.LE.refl : ∀{A : Ty α}, LE A A
  | Ty.base x => base (le_refl x)
  | Ty.pair _ _ => pair refl refl
  | Ty.unit => unit
  | Ty.bool => bool

theorem Ty.LE.trans : ∀{A B C : Ty α}, LE A B → LE B C → LE A C
  | _, _, _, base h, base h' => base (le_trans h h')
  | _, _, _, pair h₁ h₂, pair h₁' h₂' => pair (h₁.trans h₁') (h₂.trans h₂')
  | _, _, _, unit, unit => unit
  | _, _, _, bool, bool => bool

theorem Ty.LE.antisymm : ∀{A B : Ty α}, LE A B → LE B A → A = B
  | _, _, base h, base h' => by rw [le_antisymm h h']
  | _, _, pair h₁ h₂, pair h₁' h₂' => by rw [Ty.LE.antisymm h₁ h₁', Ty.LE.antisymm h₂ h₂']
  | _, _, unit, unit => rfl
  | _, _, bool, bool => rfl

instance : PartialOrder (Ty α) where
  le := Ty.LE
  le_refl _ := Ty.LE.refl
  le_trans _ _ _ := Ty.LE.trans
  le_antisymm _ _ := Ty.LE.antisymm

-- TODO: Ty.LE is decidable if α is

-- TODO: Ty.LE is a discrete order if α is

def Ctx (α ε) := List (Ty α × ε)

structure Ctx.Var (Γ : Ctx α ε) (n : ℕ) (V : Ty α × ε) : Prop where
  length : n < Γ.length
  get : Γ.get ⟨n, length⟩ ≤ V

def Ctx.Wkn (Γ Δ : Ctx α ε) (ρ : ℕ → ℕ) : Prop -- TODO: fin argument as defeq?
  := ∀i, (h : i < Δ.length) → Γ.Var (ρ i) (Δ.get ⟨i, h⟩)

theorem Ctx.Wkn_def (Γ Δ : Ctx α ε) (ρ : ℕ → ℕ) : Γ.Wkn Δ ρ ↔
  ∀i, (h : i < Δ.length) → Γ.Var (ρ i) (Δ.get ⟨i, h⟩) := Iff.rfl

theorem Ctx.Wkn_def' (Γ Δ : Ctx α ε) (ρ : ℕ → ℕ) : Γ.Wkn Δ ρ ↔
  ∀i : Fin Δ.length, Γ.Var (ρ i) (Δ.get i) := ⟨λh ⟨i, hi⟩ => h i hi, λh i hi => h ⟨i, hi⟩⟩

theorem Ctx.Wkn_iff (Γ Δ : Ctx α ε) (ρ : ℕ → ℕ) : Γ.Wkn Δ ρ ↔ List.NWkn Γ Δ ρ
  := ⟨λh i hi => have h' := h i hi; ⟨h'.length, h'.get⟩, λh i hi => have h' := h i hi; ⟨h'.1, h'.2⟩⟩

theorem Ctx.Var.wk_res {Γ : Ctx α ε} {n : ℕ} {V V'} (h : V ≤ V') (hΓ : Γ.Var n V) : Γ.Var n V' where
  length := hΓ.length
  get := le_trans hΓ.get h

theorem Ctx.Var.wk_res₂ {Γ : Ctx α ε} {n : ℕ} {A A'} {e e'} (hA : A ≤ A') (he : e ≤ e')
  (hΓ : Γ.Var n ⟨A, e⟩) : Γ.Var n ⟨A', e⟩ := hΓ.wk_res (by simp [hA, he])

theorem Ctx.Var.wk_ty {Γ : Ctx α ε} {n : ℕ} {A A'} {e} (h : A ≤ A')
  (hΓ : Γ.Var n ⟨A, e⟩) : Γ.Var n ⟨A', e⟩ := hΓ.wk_res (by simp [h])

theorem Ctx.Var.wk_eff {Γ : Ctx α ε} {n : ℕ} {A} {e e'} (h : e ≤ e')
  (hΓ : Γ.Var n ⟨A, e⟩) : Γ.Var n ⟨A, e'⟩ := hΓ.wk_res (by simp [h])

theorem Ctx.Var.wk
  {Γ : Ctx α ε} {n : ℕ} {A : Ty α} {e : ε}
  {Δ : Ctx α ε} {ρ : ℕ → ℕ} (h : Γ.Wkn Δ ρ) (hΓ : Δ.Var n ⟨A, e⟩) : Γ.Var (ρ n) ⟨A, e⟩ where
  length := (h n hΓ.length).1
  get := le_trans (h n hΓ.length).2 hΓ.get

instance : Append (Ctx α ε) := (inferInstance : Append (List (Ty α × ε)))

def FCtx (α ε) := Σn, Fin n → Ty α × ε

-- TODO: FCtx append

inductive Term.Wf : Ctx α ε → Term φ → Ty α → ε → Prop
| var {Γ n A e} : Γ.Var n ⟨A, e⟩ → Wf Γ (var n) A e
| op {f : φ} {a e A B} : Φ.Fn f A B e → Wf Γ a A e → Wf Γ (op f a) B e
| pair {a b A B e} : Wf Γ a A e → Wf Γ b B e → Wf Γ (pair a b) (Ty.pair A B) e
| unit (e) : Wf Γ unit Ty.unit e
| bool (b e) : Wf Γ (bool b) Ty.bool e

inductive Term.WfD : Ctx α ε → Term φ → Ty α → ε → Type _
| var : Γ.Var n ⟨A, e⟩ → WfD Γ (var n) A e
| op : Φ.Fn f A B e → WfD Γ a A e → WfD Γ (op f a) B e
| pair : WfD Γ a A e → WfD Γ b B e → WfD Γ (pair a b) (Ty.pair A B) e
| unit (e) : WfD Γ unit Ty.unit e
| bool (b e) : WfD Γ (bool b) Ty.bool e

-- TODO: WfD ==> Wf

-- TODO: Wf ==> ∃WfD

/-- Weaken the effect of a term derivation -/
def Term.WfD.wk_eff
  {Γ : Ctx α ε} {a : Term φ} {A e} (h : e ≤ e') : WfD Γ a A e → WfD Γ a A e'
  | var dv => var (dv.wk_eff h)
  | op df de => op (df.wk_eff h) (de.wk_eff h)
  | pair dl dr => pair (dl.wk_eff h) (dr.wk_eff h)
  | unit e => unit e'
  | bool b e => bool b e'

/-- Weaken a term derivation -/
def Term.WfD.wk
  {Γ : Ctx α ε} {a : Term φ} {A e} {Δ : Ctx α ε} {ρ : ℕ → ℕ} (h : Γ.Wkn Δ ρ)
  : WfD Δ a A e → WfD Γ (a.wk ρ) A e
  | var dv => var (dv.wk h)
  | op df de => op df (de.wk h)
  | pair dl dr => pair (dl.wk h) (dr.wk h)
  | unit e => unit e
  | bool b e => bool b e

-- TODO: for a discrete order on α, WfD unique, Wf ==> WfD

-- TODO: FWfD, FWf, associated lore

def LCtx (α) := List (Ty α)

structure LCtx.Trg (L : LCtx α) (n : ℕ) (A : Ty α) : Prop where
  length : n < L.length
  get : A ≤ L.get ⟨n, length⟩

def LCtx.Wkn (L K : LCtx α) (ρ : ℕ → ℕ) : Prop -- TODO: fin argument as defeq?
  := ∀i, (h : i < L.length) → K.Trg (ρ i) (L.get ⟨i, h⟩)

theorem LCtx.Wkn_def (L K : LCtx α) (ρ : ℕ → ℕ) : L.Wkn K ρ ↔
  ∀i, (h : i < L.length) → K.Trg (ρ i) (L.get ⟨i, h⟩) := Iff.rfl

theorem LCtx.Wkn_def' (L K : LCtx α) (ρ : ℕ → ℕ) : L.Wkn K ρ ↔
  ∀i : Fin L.length, K.Trg (ρ i) (L.get i) := ⟨λh ⟨i, hi⟩ => h i hi, λh i hi => h ⟨i, hi⟩⟩

theorem LCtx.Wkn_iff (L K : LCtx α) (ρ : ℕ → ℕ) : L.Wkn K ρ ↔ @List.NWkn (Ty α)ᵒᵈ _ K L ρ
  := ⟨λh i hi => have h' := h i hi; ⟨h'.length, h'.get⟩, λh i hi => have h' := h i hi; ⟨h'.1, h'.2⟩⟩

theorem LCtx.Trg.wk
  {L : LCtx α} {n : ℕ} {A : Ty α}
  {K : LCtx α} {ρ : ℕ → ℕ} (h : L.Wkn K ρ) (hK : L.Trg n A) : K.Trg (ρ n) A where
  length := (h n hK.length).1
  get := le_trans hK.get (h n hK.length).2

instance : Append (LCtx α) := (inferInstance : Append (List (Ty α)))

def FLCtx (α) := Σn, Fin n → Ty α

-- TODO: FLCtx append

inductive Terminator.WfD : Ctx α ε → Terminator φ → LCtx α → Type _
  | br : L.Trg n A → a.WfD Γ A 0 → WfD Γ (br n a) L
  | ite : e.WfD Γ Ty.bool 0 → s.WfD Γ L → t.WfD Γ L → WfD Γ (ite e s t) L

-- TODO: weakening

-- TODO: label-weakening

inductive Body.WfD : Ctx α ε → Body φ → Ctx α ε → Type _
  | nil : WfD Γ nil []
  | let1 : a.WfD Γ A e → b.WfD (⟨A, e⟩::Γ) Δ → (let1 a b).WfD Γ (⟨A, e⟩::Δ)
  | let2 : a.WfD Γ (Ty.pair A B) e
    → b.WfD (⟨A, e⟩::⟨B, e⟩::Γ) Δ
    → (let2 a b).WfD Γ (⟨A, e⟩::⟨B, e⟩::Δ)

-- TODO: weakening

structure Block.WfD (Γ : Ctx α ε) (β : Block φ) (Δ : Ctx α ε) (L : LCtx α) where
  body : β.body.WfD Γ Δ
  terminator : β.terminator.WfD (Δ ++ Γ) L

-- TODO: weakening

-- TODO: label-weakening

inductive BBRegion.WfD : Ctx α ε → BBRegion φ → LCtx α → Type _
  | cfg {Δ} : β.WfD Γ Δ K → (∀i : Fin n, (G i).WfD (Δ ++ Γ) K)
    → L = K.drop n → BBRegion.WfD Γ (cfg β n G) L

-- TODO: weakening

-- TODO: label-weakening

inductive TRegion.WfD : Ctx α ε → TRegion φ → LCtx α → Type _
  | let1 : a.WfD Γ A e → t.WfD (⟨A, e⟩::Γ) L → (let1 a t).WfD Γ L
  | let2 : a.WfD Γ (Ty.pair A B) e → t.WfD (⟨A, e⟩::⟨B, e⟩::Γ) L → (let2 a t).WfD Γ L
  | cfg : t.WfD Γ K → (∀i : Fin n, (G i).WfD Γ K) → L = K.drop n → WfD Γ (cfg t n G) L

-- TODO: weakening

-- TODO: label-weakening

inductive Region.WfD [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Zero ε]
    : Ctx α ε → Region φ → LCtx α → Type _
  | br : L.Trg n A → a.WfD Γ A 0 → WfD Γ (br n a) L
  | ite : e.WfD Γ Ty.bool 0 → s.WfD Γ L → t.WfD Γ L → WfD Γ (ite e s t) L
  | let1 : a.WfD Γ A e → t.WfD (⟨A, e⟩::Γ) L → (let1 a t).WfD Γ L
  | let2 : a.WfD Γ (Ty.pair A B) e → t.WfD (⟨A, e⟩::⟨B, e⟩::Γ) L → (let2 a t).WfD Γ L
  | cfg : β.WfD Γ K → (∀i : Fin n, (G i).WfD Γ K) → L = K.drop n → WfD Γ (cfg β n G) L

-- TODO: weakening

-- TODO: label-weakening

-- TODO: normalize region to TRegion; type preservation

-- TODO: normalize TRegion to BBRegion; type preservation

-- == SPECULATIVE ==

-- TODO: substitution-terminator typing

-- TODO: substitution-CFG typing

-- TODO: _partial_ substitutions for more standard SSA? parameter tagging?

-- TODO: 3 address code via var-only substitution; everything trivially SSA with preserved vars
-- via id-substitution.

end SingleApp
