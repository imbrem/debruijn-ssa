import Discretion.Wk.Basic
import DeBruijnSSA.SingleApp.Syntax
import DeBruijnSSA.InstSet

namespace SingleApp

section Basic

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

theorem Ty.LE.eq [d : DiscreteOrder α] {A B : Ty α} : LE A B → A = B
  | base h => by rw [d.le_eq _ _ h]
  | pair h₁ h₂ => by rw [eq h₁, eq h₂]
  | bool | unit => rfl

instance [DiscreteOrder α] : DiscreteOrder (Ty α) where
  le_eq _ _ := Ty.LE.eq

-- TODO: Ty.LE is decidable if ≤ on α is

def Ctx (α ε) := List (Ty α × ε)

structure Ctx.Var (Γ : Ctx α ε) (n : ℕ) (V : Ty α × ε) : Prop where
  length : n < Γ.length
  get : Γ.get ⟨n, length⟩ ≤ V

instance : Append (Ctx α ε) := (inferInstance : Append (List (Ty α × ε)))

def FCtx (α ε) := Σn, Fin n → Ty α × ε

-- TODO: FCtx append

/-- A well-formed term -/
inductive Term.Wf : Ctx α ε → Term φ → Ty α → ε → Prop
  | var : Γ.Var n ⟨A, e⟩ → Wf Γ (var n) A e
  | op : Φ.Fn f A B e → Wf Γ a A e → Wf Γ (op f a) B e
  | pair : Wf Γ a A e → Wf Γ b B e → Wf Γ (pair a b) (Ty.pair A B) e
  | unit (e) : Wf Γ unit Ty.unit e
  | bool (b e) : Wf Γ (bool b) Ty.bool e

/-- A derivation that a term is well-formed -/
inductive Term.WfD : Ctx α ε → Term φ → Ty α → ε → Type _
  | var : Γ.Var n ⟨A, e⟩ → WfD Γ (var n) A e
  | op : Φ.Fn f A B e → WfD Γ a A e → WfD Γ (op f a) B e
  | pair : WfD Γ a A e → WfD Γ b B e → WfD Γ (pair a b) (Ty.pair A B) e
  | unit (e) : WfD Γ unit Ty.unit e
  | bool (b e) : WfD Γ (bool b) Ty.bool e

/-- The minimal type for which a term may be well-typed -/
def Term.min_ty (Γ : Ctx α ε) : Term φ → Ty α
  | var n => if h : n < Γ.length then (Γ.get ⟨n, h⟩).1 else Ty.unit
  | op f _ => Φ.trg f
  | pair a b => Ty.pair (a.min_ty Γ) (b.min_ty Γ)
  | unit => Ty.unit
  | bool _ => Ty.bool

-- TODO: WfD ==> Wf

-- TODO: Wf ==> ∃WfD

-- def Term.Wf.toWFD
--   {Γ : Ctx α ε} {a : Term φ} {A e} (h : Wf Γ a A e) : WfD Γ a A e
--   := match a with
--   | Term.var n => WfD.var sorry
--   | Term.op f a => WfD.op sorry sorry
--   | Term.pair a b => WfD.pair sorry sorry
--   | Term.unit => sorry
--   | Term.bool b => sorry

-- TODO: for a discrete order on α, WfD unique, Wf ==> WfD

-- TODO: FWfD, FWf, associated lore

-- TODO: propositional variants for below...

inductive Body.WfD : Ctx α ε → Body φ → Ctx α ε → Type _
  | nil : WfD Γ nil []
  | let1 : a.WfD Γ A e → b.WfD (⟨A, e⟩::Γ) Δ → (let1 a b).WfD Γ (⟨A, e⟩::Δ)
  | let2 : a.WfD Γ (Ty.pair A B) e
    → b.WfD (⟨A, e⟩::⟨B, e⟩::Γ) Δ
    → (let2 a b).WfD Γ (⟨A, e⟩::⟨B, e⟩::Δ)

theorem Body.WfD.num_defs_eq_length {Γ : Ctx α ε} {b : Body φ} {Δ} (h : b.WfD Γ Δ)
  : b.num_defs = Δ.length
  := by induction h <;> simp [num_defs, *]

def LCtx (α) := List (Ty α)

structure LCtx.Trg (L : LCtx α) (n : ℕ) (A : Ty α) : Prop where
  length : n < L.length
  get : A ≤ L.get ⟨n, length⟩

instance : Append (LCtx α) := (inferInstance : Append (List (Ty α)))

def LCtx.take (n : ℕ) (L : LCtx α) : LCtx α := List.take n L

def LCtx.drop (n : ℕ) (L : LCtx α) : LCtx α := List.drop n L

def FLCtx (α) := Σn, Fin n → Ty α

-- TODO: FLCtx append

inductive Terminator.WfD : Ctx α ε → Terminator φ → LCtx α → Type _
  | br : L.Trg n A → a.WfD Γ A 0 → WfD Γ (br n a) L
  | ite : e.WfD Γ Ty.bool 0 → s.WfD Γ L → t.WfD Γ L → WfD Γ (ite e s t) L

structure Block.WfD (Γ : Ctx α ε) (β : Block φ) (Δ : Ctx α ε) (L : LCtx α) where
  body : β.body.WfD Γ Δ
  terminator : β.terminator.WfD (Δ ++ Γ) L

inductive BBRegion.WfD : Ctx α ε → BBRegion φ → LCtx α → Type _
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.WfD Γ Δ (R ++ L) →
    (∀i : Fin n, (G i).WfD (⟨R.get (i.cast hR.symm), 0⟩::(Δ ++ Γ)) (R ++ L)) →
    WfD Γ (cfg β n G) L

inductive TRegion.WfD : Ctx α ε → TRegion φ → LCtx α → Type _
  | let1 : a.WfD Γ A e → t.WfD (⟨A, e⟩::Γ) L → (let1 a t).WfD Γ L
  | let2 : a.WfD Γ (Ty.pair A B) e → t.WfD (⟨A, e⟩::⟨B, e⟩::Γ) L → (let2 a t).WfD Γ L
  | cfg  (n : ℕ) {G} : t.WfD Γ K → (∀i : Fin n, (G i).WfD Γ K) → L = K.drop n → WfD Γ (cfg t n G) L

inductive Region.WfD : Ctx α ε → Region φ → LCtx α → Type _
  | br : L.Trg n A → a.WfD Γ A 0 → WfD Γ (br n a) L
  | ite : e.WfD Γ Ty.bool 0 → s.WfD Γ L → t.WfD Γ L → WfD Γ (ite e s t) L
  | let1 : a.WfD Γ A e → t.WfD (⟨A, e⟩::Γ) L → (let1 a t).WfD Γ L
  | let2 : a.WfD Γ (Ty.pair A B) e → t.WfD (⟨A, e⟩::⟨B, e⟩::Γ) L → (let2 a t).WfD Γ L
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.WfD Γ (R ++ L) →
    (∀i : Fin n, (G i).WfD (⟨R.get (i.cast hR.symm), 0⟩::Γ) (R ++ L)) →
    WfD Γ (cfg β n G) L

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
  [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Zero ε]
  {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} -- {a b : Term φ} {A B : Ty α} {e e' : ε}

def Ctx.Wkn (Γ Δ : Ctx α ε) (ρ : ℕ → ℕ) : Prop -- TODO: fin argument as defeq?
  := ∀i, (h : i < Δ.length) → Γ.Var (ρ i) (Δ.get ⟨i, h⟩)

theorem Ctx.Wkn_def (Γ Δ : Ctx α ε) (ρ : ℕ → ℕ) : Γ.Wkn Δ ρ ↔
  ∀i, (h : i < Δ.length) → Γ.Var (ρ i) (Δ.get ⟨i, h⟩) := Iff.rfl

theorem Ctx.Wkn_def' (Γ Δ : Ctx α ε) (ρ : ℕ → ℕ) : Γ.Wkn Δ ρ ↔
  ∀i : Fin Δ.length, Γ.Var (ρ i) (Δ.get i) := ⟨λh ⟨i, hi⟩ => h i hi, λh i hi => h ⟨i, hi⟩⟩

theorem Ctx.Wkn_iff (Γ Δ : Ctx α ε) (ρ : ℕ → ℕ) : Γ.Wkn Δ ρ ↔ List.NWkn Γ Δ ρ
  := ⟨λh i hi => have h' := h i hi; ⟨h'.length, h'.get⟩, λh i hi => have h' := h i hi; ⟨h'.1, h'.2⟩⟩

theorem Ctx.Wkn.lift {V V' : Ty α × ε} (hV : V ≤ V') (h : Γ.Wkn Δ ρ)
  : Wkn (V::Γ) (V'::Δ) (Nat.liftWk ρ)
  := (Wkn_iff _ _ _).mpr (((Wkn_iff _ _ _).mp h).lift hV)

theorem Ctx.Wkn.lift₂ {V₁ V₁' V₂ V₂' : Ty α × ε} (hV₁ : V₁ ≤ V₁') (hV₂ : V₂ ≤ V₂') (h : Γ.Wkn Δ ρ)
  : Wkn (V₁::V₂::Γ) (V₁'::V₂'::Δ) (Nat.liftWk (Nat.liftWk ρ))
  := (Wkn_iff _ _ _).mpr (((Wkn_iff _ _ _).mp h).lift₂ hV₁ hV₂)

theorem Ctx.Wkn.liftn₂ {V₁ V₁' V₂ V₂' : Ty α × ε} (hV₁ : V₁ ≤ V₁') (hV₂ : V₂ ≤ V₂') (h : Γ.Wkn Δ ρ)
  : Wkn (V₁::V₂::Γ) (V₁'::V₂'::Δ) (Nat.liftnWk 2 ρ)
  := (Wkn_iff _ _ _).mpr (((Wkn_iff _ _ _).mp h).liftn₂ hV₁ hV₂)

theorem Ctx.Wkn.liftn_append (Ξ) (h : Γ.Wkn Δ ρ)
  : Wkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk Ξ.length ρ)
  := (Wkn_iff _ _ _).mpr (((Wkn_iff _ _ _).mp h).liftn_append Ξ)

theorem Ctx.Wkn.liftn_append_cons (A Ξ) (h : Γ.Wkn Δ ρ)
  : Wkn (A::(Ξ ++ Γ)) (A::(Ξ ++ Δ)) (Nat.liftnWk (Ξ.length + 1) ρ)
  := liftn_append (A::Ξ) h

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
def Term.WfD.wk_eff {a : Term φ} {A e} (h : e ≤ e') : WfD Γ a A e → WfD Γ a A e'
  | var dv => var (dv.wk_eff h)
  | op df de => op (df.wk_eff h) (de.wk_eff h)
  | pair dl dr => pair (dl.wk_eff h) (dr.wk_eff h)
  | unit e => unit e'
  | bool b e => bool b e'

/-- Weaken a term derivation -/
def Term.WfD.wk {a : Term φ} (h : Γ.Wkn Δ ρ) : WfD Δ a A e → WfD Γ (a.wk ρ) A e
  | var dv => var (dv.wk h)
  | op df de => op df (de.wk h)
  | pair dl dr => pair (dl.wk h) (dr.wk h)
  | unit e => unit e
  | bool b e => bool b e

def Body.WfD.wk {Γ Δ : Ctx α ε} {ρ} {b : Body φ} (h : Γ.Wkn Δ ρ) : WfD Δ b Ξ → WfD Γ (b.wk ρ) Ξ
  | nil => nil
  | let1 a b => let1 (a.wk h) (b.wk (h.lift (le_refl _)))
  | let2 a b => let2 (a.wk h) (b.wk (h.liftn₂ (le_refl _) (le_refl _)))

variable {L K : LCtx α}

def LCtx.Wkn (L K : LCtx α) (ρ : ℕ → ℕ) : Prop -- TODO: fin argument as defeq?
  := ∀i, (h : i < L.length) → K.Trg (ρ i) (L.get ⟨i, h⟩)

theorem LCtx.Wkn_def (L K : LCtx α) (ρ : ℕ → ℕ) : L.Wkn K ρ ↔
  ∀i, (h : i < L.length) → K.Trg (ρ i) (L.get ⟨i, h⟩) := Iff.rfl

theorem LCtx.Wkn_def' (L K : LCtx α) (ρ : ℕ → ℕ) : L.Wkn K ρ ↔
  ∀i : Fin L.length, K.Trg (ρ i) (L.get i) := ⟨λh ⟨i, hi⟩ => h i hi, λh i hi => h ⟨i, hi⟩⟩

theorem LCtx.Wkn_iff (L K : LCtx α) (ρ : ℕ → ℕ) : L.Wkn K ρ ↔ @List.NWkn (Ty α)ᵒᵈ _ K L ρ
  := ⟨λh i hi => have h' := h i hi; ⟨h'.length, h'.get⟩, λh i hi => have h' := h i hi; ⟨h'.1, h'.2⟩⟩

theorem LCtx.Wkn.liftn_append {L K : LCtx α} {ρ : ℕ → ℕ} (R : LCtx α) (h : L.Wkn K ρ)
  : (R ++ L).Wkn (R ++ K) (Nat.liftnWk R.length ρ) := by
  rw [LCtx.Wkn_iff]
  apply List.NWkn.liftn_append
  rw [<-LCtx.Wkn_iff]
  exact h

theorem LCtx.Trg.wk (h : L.Wkn K ρ) (hK : L.Trg n A) : K.Trg (ρ n) A where
  length := (h n hK.length).1
  get := le_trans hK.get (h n hK.length).2

def Terminator.WfD.vwk {t : Terminator φ} (h : Γ.Wkn Δ ρ) : WfD Δ t L → WfD Γ (t.vwk ρ) L
  | br hL ha => br hL (ha.wk h)
  | ite he hs ht => ite (he.wk h) (hs.vwk h) (ht.vwk h)

def Terminator.WfD.lwk {t : Terminator φ} (h : L.Wkn K ρ) : WfD Γ t L → WfD Γ (t.lwk ρ) K
  | br hL ha => br (hL.wk h) ha
  | ite he hs ht => ite he (hs.lwk h) (ht.lwk h)

def Block.WfD.vwk {β : Block φ} (h : Γ.Wkn Δ ρ) (hβ : WfD Δ β Ξ L) : WfD Γ (β.vwk ρ) Ξ L where
  body := hβ.body.wk h
  terminator := hβ.terminator.vwk (hβ.body.num_defs_eq_length ▸ (h.liftn_append Ξ))

def Block.WfD.lwk {β : Block φ} (h : L.Wkn K ρ) (hβ : WfD Γ β Ξ L) : WfD Γ (β.lwk ρ) Ξ K where
  body := hβ.body
  terminator := hβ.terminator.lwk h

def BBRegion.WfD.vwk {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} {L} {r : BBRegion φ} (h : Γ.Wkn Δ ρ)
  : WfD Δ r L → WfD Γ (r.vwk ρ) L
  | cfg n R hR hβ hG =>
    cfg n R hR (hβ.vwk h) (λi => (hG i).vwk (hβ.body.num_defs_eq_length ▸h.liftn_append_cons _ _))

-- TODO: label-weakening

-- TODO: TRegion:

-- TODO: weakening

-- TODO: label-weakening

def Region.WfD.vwk {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} {L} {r : Region φ} (h : Γ.Wkn Δ ρ)
  : WfD Δ r L → WfD Γ (r.vwk ρ) L
  | br hL ha => br hL (ha.wk h)
  | ite he hs ht => ite (he.wk h) (hs.vwk h) (ht.vwk h)
  | let1 ha ht => let1 (ha.wk h) (ht.vwk (h.lift (le_refl _)))
  | let2 ha ht => let2 (ha.wk h) (ht.vwk (h.liftn₂ (le_refl _) (le_refl _)))
  | cfg n R hR hr hG => cfg n R hR (hr.vwk h) (λi => (hG i).vwk (h.lift (le_refl _)))

def Region.WfD.lwk {Γ : Ctx α ε} {ρ : ℕ → ℕ} {L K : LCtx α} {r : Region φ} (h : L.Wkn K ρ)
  : WfD Γ r L → WfD Γ (r.lwk ρ) K
  | br hL ha => br (hL.wk h) ha
  | ite he hs ht => ite he (hs.lwk h) (ht.lwk h)
  | let1 ha ht => let1 ha (ht.lwk h)
  | let2 ha ht => let2 ha (ht.lwk h)
  | cfg n R hR hβ hG =>
    have trg_wk : (R ++ L).Wkn (R ++ K) (Nat.liftnWk n ρ) := hR ▸ h.liftn_append R
    cfg n R hR (hβ.lwk trg_wk) (λi => (hG i).lwk trg_wk)

end Weakening

section Minimal

variable [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε] [Zero ε]

def Term.min_effect (Γ : Ctx α ε) : Term φ → ε
  | var n => if h : n < Γ.length then (Γ.get ⟨n, h⟩).2 else 0
  | op f _ => Φ.effect f
  | pair a b => a.min_effect Γ ⊔ b.min_effect Γ
  | unit => ⊥
  | bool _ => ⊥

theorem Term.WfD.min_effect_le
  {Γ : Ctx α ε} {a : Term φ} {A e} (h : WfD Γ a A e) : a.min_effect Γ ≤ e
  := match h with
  | var dv => by simp [min_effect, dv.length, dv.get.right]
  | op df de => df.effect
  | pair dl dr => sup_le_iff.mpr ⟨dl.min_effect_le, dr.min_effect_le⟩
  | unit _ | bool _ _ => bot_le

def Body.min_defs (Γ : Ctx α ε) : Body φ → Ctx α ε
  | Body.nil => []
  | Body.let1 a b => ⟨a.min_ty Γ, a.min_effect Γ⟩ :: b.min_defs (⟨a.min_ty Γ, a.min_effect Γ⟩::Γ)
  | Body.let2 a b =>
    ⟨a.min_ty Γ, a.min_effect Γ⟩ ::
    ⟨a.min_ty Γ, a.min_effect Γ⟩ ::
    b.min_defs (⟨a.min_ty Γ, a.min_effect Γ⟩::⟨a.min_ty Γ, a.min_effect Γ⟩::Γ)

end Minimal

-- == SPECULATIVE ==

-- TODO: substitution-terminator typing

-- TODO: substitution-CFG typing

-- TODO: _partial_ substitutions for more standard SSA? parameter tagging?

-- TODO: 3 address code via var-only substitution; everything trivially SSA with preserved vars
-- via id-substitution.

end SingleApp
