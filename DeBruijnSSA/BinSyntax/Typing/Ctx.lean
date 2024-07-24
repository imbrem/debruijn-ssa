import Discretion.Wk.List
import Discretion.Basic
import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Fv.Basic
import DeBruijnSSA.BinSyntax.Syntax.Effect.Definitions
import DeBruijnSSA.BinSyntax.Typing.Ty

namespace BinSyntax

section Basic

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]

abbrev Ctx (α ε) := List (Ty α × ε)

namespace Ctx

-- instance Ctx.instGetElemNatLtLength
--   : GetElem (Ctx α ε) ℕ (Ty α × ε) (λΓ => (· < Γ.length))
--   := List.instGetElemNatLtLength

def reverse (Γ : Ctx α ε) : Ctx α ε := List.reverse Γ

structure Var (Γ : Ctx α ε) (n : ℕ) (V : Ty α × ε) : Prop where
  length : n < Γ.length
  getElem : Γ[n] ≤ V

theorem Var.get {Γ : Ctx α ε} {n V} (h : Var Γ n V) : Γ.get ⟨n, h.length⟩ ≤ V := h.getElem

theorem Var.head (h : V ≤ V') (Γ : Ctx α ε) : Var (V::Γ) 0 V' where
  length := by simp
  getElem := h

theorem Var.refl {Γ : Ctx α ε} {n} (h : n < Γ.length) : Var Γ n Γ[n] := ⟨h, le_refl _⟩

@[simp]
theorem Var.head_iff {V V' : Ty α × ε} {Γ : Ctx α ε} : Var (V::Γ) 0 V' ↔ V ≤ V'
  := ⟨λh => h.getElem, λh => Var.head h Γ⟩

theorem Var.shead {head : Ty α × ε} {Γ : Ctx α ε}
  : Var (head::Γ) 0 head := Var.head (le_refl _) Γ

theorem Var.step {Γ : Ctx α ε} (h : Var Γ n V) : Var (V'::Γ) (n+1) V
  := ⟨by simp [h.length], by simp [h.getElem]⟩

theorem Var.tail {Γ : Ctx α ε} {n} (h : Var (V'::Γ) (n+1) V) : Var Γ n V
  := ⟨Nat.lt_of_succ_lt_succ h.length, h.getElem⟩

@[simp]
theorem Var.step_iff {V V' : Ty α × ε} {Γ : Ctx α ε} {n} : Var (V'::Γ) (n+1) V ↔ Var Γ n V
  := ⟨Var.tail, Var.step⟩

def effect (Γ : Ctx α ε) : ℕ → ε := λn => if h : n < Γ.length then (Γ.get ⟨n, h⟩).2 else ⊥

theorem effect_append_bot {head : Ty α} {tail : Ctx α ε}
  : effect (⟨head, ⊥⟩::tail) = Nat.liftBot tail.effect
  := by funext k; cases k with
  | zero => simp [effect, Nat.liftBot]
  | succ k => simp [effect, Nat.liftBot]

theorem effect_append_bot₂ {left right : Ty α} {tail : Ctx α ε}
  : effect (⟨left, ⊥⟩::⟨right, ⊥⟩::tail) = Nat.liftnBot 2 tail.effect
  := by simp only [effect_append_bot, Nat.liftnBot_two_apply]

instance : Append (Ctx α ε) := (inferInstance : Append (List (Ty α × ε)))

instance : Membership (Ty α × ε) (Ctx α ε)
  := (inferInstance : Membership (Ty α × ε) (List (Ty α × ε)))

def IsInitial (Γ : Ctx α ε) : Prop := ∃V ∈ Γ, Ty.IsInitial V.1 ∧ V.2 = ⊥

theorem IsInitial.append_left {Γ : Ctx α ε} (h : Γ.IsInitial) (Δ) : (Γ ++ Δ).IsInitial
  := let ⟨V, hV, hV0⟩ := h; ⟨V, List.mem_append_left _ hV, hV0⟩

theorem IsInitial.append_right (Γ) {Δ : Ctx α ε} (h : Δ.IsInitial) : (Γ ++ Δ).IsInitial
  := let ⟨V, hV, hV0⟩ := h; ⟨V, List.mem_append_right _ hV, hV0⟩

@[simp]
theorem IsInitial.append {Γ Δ : Ctx α ε} : (Γ ++ Δ).IsInitial ↔ Γ.IsInitial ∨ Δ.IsInitial
  := ⟨
    λ⟨V, hV, hV0⟩ => (List.mem_append.mp hV).elim (Or.inl ⟨V, ·, hV0⟩) (Or.inr ⟨V, ·, hV0⟩),
    λh => h.elim (append_left · _) (append_right _)⟩

theorem IsInitial.head {A} (h : Ty.IsInitial A) (Γ : Ctx α ε)
  : IsInitial (⟨A, ⊥⟩::Γ)
  := ⟨⟨A, ⊥⟩, List.mem_cons_self _ _, h, rfl⟩

theorem IsInitial.head' {A e} (hA : Ty.IsInitial A) (he : e = ⊥) (Γ : Ctx α ε)
  : IsInitial (⟨A, e⟩::Γ)
  := by cases he; apply head; exact hA

theorem IsInitial.cons {head} {Γ : Ctx α ε} (h : IsInitial Γ)
  : IsInitial (head::Γ)
  := let ⟨V', hV, hV0⟩ := h; ⟨V', List.mem_cons_of_mem _ hV, hV0⟩

theorem IsInitial.head_or_tail {head} {Γ : Ctx α ε} (h : IsInitial (head::Γ))
  : (Ty.IsInitial head.1 ∧ head.2 = ⊥) ∨ IsInitial Γ
  := let ⟨V, hV, hV0⟩ := h;
  by cases hV with
  | head => exact Or.inl hV0
  | tail _ hV => exact Or.inr ⟨V, hV, hV0⟩

theorem IsInitial.cons_iff {head} {Γ : Ctx α ε}
  : IsInitial (head::Γ) ↔ (Ty.IsInitial head.1 ∧ head.2 = ⊥) ∨ IsInitial Γ
  := ⟨IsInitial.head_or_tail, λ| Or.inl ⟨hA, he⟩ => head' hA he Γ | Or.inr h => h.cons⟩

-- TODO: HAppend of Ctx and List?

theorem append_assoc : (Γ Δ Ξ : Ctx α ε) → Γ ++ Δ ++ Ξ = Γ ++ (Δ ++ Ξ)
  := List.append_assoc

theorem reverse_append : (Γ Δ : Ctx α ε) → (Γ ++ Δ).reverse = Δ.reverse ++ Γ.reverse
  := List.reverse_append

theorem length_reverse : (Γ : Ctx α ε) → Γ.reverse.length = Γ.length
  := List.length_reverse

def FCtx (α ε) := Σn, Fin n → Ty α × ε

-- TODO: FCtx append

def Wkn (Γ Δ : Ctx α ε) (ρ : ℕ → ℕ) : Prop -- TODO: fin argument as defeq?
  := ∀i, (h : i < Δ.length) → Γ.Var (ρ i) (Δ.get ⟨i, h⟩)

def InS (Γ Δ : Ctx α ε) : Type _ := {ρ : ℕ → ℕ | Γ.Wkn Δ ρ}

variable {Γ Δ Ξ Γ' Δ' : Ctx α ε}

instance InS.instCoeOut : CoeOut (InS Γ Δ) (ℕ → ℕ)
  := ⟨λt => t.val⟩

@[ext]
theorem InS.ext {h h' : InS Γ Δ} (hh : (h : ℕ → ℕ) = (h' : ℕ → ℕ)) : h = h' := by
  cases h; cases h'; cases hh; rfl

instance InS.instSetoid : Setoid (InS Γ Δ) where
  r ρ σ := ∀i, i < Δ.length → (ρ : ℕ → ℕ) i = (σ : ℕ → ℕ) i
  iseqv := {
    refl := (λ_ _ _ => rfl)
    symm := (λh i hi => (h i hi).symm)
    trans := (λh h' i hi => (h i hi).trans (h' i hi))
  }

def InS.cast (hΓ : Γ = Γ') (hΔ : Δ = Δ') (ρ : InS Γ Δ) : InS Γ' Δ'
  := ⟨ρ, hΓ ▸ hΔ ▸ ρ.2⟩

theorem Wkn_def : Γ.Wkn Δ ρ ↔ ∀i, (h : i < Δ.length) → Γ.Var (ρ i) (Δ.get ⟨i, h⟩) := Iff.rfl

theorem Wkn_def' : Γ.Wkn Δ ρ ↔
  ∀i : Fin Δ.length, Γ.Var (ρ i) (Δ.get i) := ⟨λh ⟨i, hi⟩ => h i hi, λh i hi => h ⟨i, hi⟩⟩

theorem Wkn_iff : Γ.Wkn Δ ρ ↔ List.NWkn Γ Δ ρ
  := ⟨λh i hi => have h' := h i hi; ⟨h'.length, h'.getElem⟩,
      λh i hi => have h' := h i hi; ⟨h'.1, h'.2⟩⟩

@[simp]
theorem Wkn.id {Γ : Ctx α ε} : Γ.Wkn Γ id := λ_ hi => ⟨hi, le_refl _⟩

def InS.id (Γ : Ctx α ε) : InS Γ Γ := ⟨_root_.id, Wkn.id⟩

theorem Wkn.lift {lo hi : Ty α × ε} (h : lo ≤ hi) (hρ : Γ.Wkn Δ ρ)
  : Wkn (lo::Γ) (hi::Δ) (Nat.liftWk ρ)
  := Wkn_iff.mpr ((Wkn_iff.mp hρ).lift h)

def InS.lift {lo hi : Ty α × ε} (h : lo ≤ hi) (hρ : InS Γ Δ)
  : InS (lo::Γ) (hi::Δ)
  := ⟨Nat.liftWk hρ.1, hρ.2.lift h⟩

abbrev InS.slift {head : Ty α × ε} (hρ : InS Γ Δ)
  : InS (head::Γ) (head::Δ)
  := hρ.lift (le_refl _)

theorem Wkn.lift_tail {head head' : Ty α × ε} (h : Wkn (head::Γ) (head'::Δ) (Nat.liftWk ρ))
  : Wkn Γ Δ ρ := λi hi => Var.tail (h (i + 1) (Nat.succ_lt_succ hi))

theorem Wkn.lift_head {head head' : Ty α × ε} (h : Wkn (head::Γ) (head'::Δ) (Nat.liftWk ρ))
  : head ≤ head'
  := (h 0 (by simp)).getElem

@[simp]
theorem Wkn.lift_iff {head head' : Ty α × ε} {Γ Δ}
    : Wkn (head::Γ) (head'::Δ) (Nat.liftWk ρ) ↔ head ≤ head' ∧ Wkn Γ Δ ρ
    := ⟨λh => ⟨h.lift_head, h.lift_tail⟩, λ⟨h, h'⟩ => h'.lift h⟩

theorem Wkn.slift {head : Ty α × ε} (h : Γ.Wkn Δ ρ)
  : Wkn (head::Γ) (head::Δ) (Nat.liftWk ρ)
  := h.lift (le_refl head)

theorem Wkn.lift_id {V V' : Ty α × ε} (hV : V ≤ V') (h : Γ.Wkn Δ _root_.id)
  : Wkn (V::Γ) (V'::Δ) _root_.id
  := Nat.liftWk_id ▸ h.lift hV

theorem Wkn.lift_id_tail {head head' : Ty α × ε} (h : Wkn (head::Γ) (head'::Δ) _root_.id)
  : Wkn Γ Δ _root_.id := λi hi => (h (i + 1) (Nat.succ_lt_succ hi)).tail

theorem Wkn.lift_id_head {head head' : Ty α × ε} (h : Wkn (head::Γ) (head'::Δ) _root_.id)
  : head ≤ head'
  := (h 0 (by simp)).getElem

@[simp]
theorem Wkn.lift_id_iff {head head' : Ty α × ε} {Γ Δ}
    : Wkn (head::Γ) (head'::Δ) _root_.id ↔ head ≤ head' ∧ Wkn Γ Δ _root_.id
    := ⟨λh => ⟨h.lift_id_head, h.lift_id_tail⟩, λ⟨h, h'⟩ => h'.lift_id h⟩

theorem Wkn.slift_id {head : Ty α × ε} (h : Γ.Wkn Δ _root_.id)
  : Wkn (head::Γ) (head::Δ) _root_.id
  := h.lift_id (le_refl _)

theorem Wkn.slift_iff {head : Ty α × ε} {Γ Δ}
  : Wkn (head::Γ) (head::Δ) (Nat.liftWk ρ) ↔ Wkn Γ Δ ρ
  := by simp

theorem Wkn.slift_id_iff {head : Ty α × ε} {Γ Δ}
  : Wkn (head::Γ) (head::Δ) _root_.id ↔ Wkn Γ Δ _root_.id
  := by simp

theorem Wkn.step {head : Ty α × ε} (h : Γ.Wkn Δ ρ) : Wkn (head::Γ) Δ (Nat.stepWk ρ)
  := Wkn_iff.mpr ((Wkn_iff.mp h).step _)

theorem Wkn.step_tail {head : Ty α × ε} (h : Wkn (head::Γ) Δ (Nat.stepWk ρ))
  : Wkn Γ Δ ρ := λi hi => (h i hi).tail

@[simp]
theorem Wkn.step_iff {head : Ty α × ε} {Γ Δ}
  : Wkn (head::Γ) Δ (Nat.stepWk ρ) ↔ Wkn Γ Δ ρ
  := ⟨λh => h.step_tail, λh => h.step⟩

@[simp]
theorem Wkn.succ_comp_iff {head : Ty α × ε} {Γ Δ}
  : Wkn (head::Γ) Δ (Nat.succ ∘ ρ) ↔ Wkn Γ Δ ρ
  := Wkn.step_iff

@[simp]
theorem Wkn.succ {head} {Γ : Ctx α ε}
  : Wkn (head::Γ) Γ Nat.succ
  := step (head := head) (id (Γ := Γ))

def InS.wk0 {head} {Γ : Ctx α ε}
  : InS (head::Γ) Γ
  := ⟨Nat.succ, Wkn.succ⟩

@[simp]
theorem InS.coe_wk0 {head} {Γ : Ctx α ε}
  : (InS.wk0 (Γ := Γ) (head := head) : ℕ → ℕ) = Nat.succ
  := rfl

theorem Wkn.wk1 {head inserted} {Γ : Ctx α ε}
  : Wkn (head::inserted::Γ) (head::Γ) (Nat.liftWk Nat.succ)
  := succ.slift

def InS.wk1 {head inserted} {Γ : Ctx α ε}
  : InS (head::inserted::Γ) (head::Γ)
  := ⟨Nat.liftWk Nat.succ, Wkn.wk1⟩

@[simp]
theorem InS.coe_wk1 {head inserted} {Γ : Ctx α ε}
  : (InS.wk1 (Γ := Γ) (head := head) (inserted := inserted) : ℕ → ℕ) = Nat.liftWk Nat.succ
  := rfl

@[simp]
theorem InS.coe_lift {lo hi : Ty α × ε} {Γ Δ} (h : lo ≤ hi) (hρ : InS Γ Δ)
  : (InS.lift h hρ : ℕ → ℕ) = Nat.liftWk hρ
  := rfl

theorem InS.coe_slift {head : Ty α × ε} {Γ Δ} (hρ : InS Γ Δ)
  : (InS.slift (head := head) hρ : ℕ → ℕ) = Nat.liftWk hρ
  := rfl

@[simp]
theorem InS.lift_wk0 {head inserted} {Γ : Ctx α ε}
  : wk0.lift (le_refl _) = (wk1 : InS (head::inserted::Γ) (head::Γ))
  := rfl

theorem Wkn.swap01 {left right : Ty α × ε} {Γ : Ctx α ε}
  : Wkn (left::right::Γ) (right::left::Γ) (Nat.swap0 1)
  | 0, _ => by simp
  | 1, _ => by simp
  | n + 2, hn => ⟨hn, by simp⟩

def InS.swap01 {left right : Ty α × ε} {Γ : Ctx α ε}
  : InS (left::right::Γ) (right::left::Γ)
  := ⟨Nat.swap0 1, Wkn.swap01⟩

@[simp]
theorem InS.coe_swap01 {left right : Ty α × ε} {Γ : Ctx α ε}
  : (InS.swap01 (Γ := Γ) (left := left) (right := right) : ℕ → ℕ) = Nat.swap0 1
  := rfl

theorem Wkn.swap02 {first second third : Ty α × ε} {Γ : Ctx α ε}
  : Wkn (first::second::third::Γ) (third::first::second::Γ) (Nat.swap0 2)
  | 0, _ => by simp
  | 1, _ => by simp
  | 2, _ => by simp
  | n + 3, hn => ⟨hn, by simp⟩

def InS.swap02 {first second third : Ty α × ε} {Γ : Ctx α ε}
  : InS (first::second::third::Γ) (third::first::second::Γ)
  := ⟨Nat.swap0 2, Wkn.swap02⟩

@[simp]
theorem InS.coe_swap02 {first second third : Ty α × ε} {Γ : Ctx α ε}
  : (InS.swap02 (Γ := Γ) (first := first) (second := second) (third := third) : ℕ → ℕ) = Nat.swap0 2
  := rfl

@[simp]
theorem Wkn.add2 {first second} {Γ : Ctx α ε}
  : Wkn (first::second::Γ) Γ (· + 2)
  := λn hn => ⟨by simp [hn], by simp⟩

theorem Wkn.lift₂ {V₁ V₁' V₂ V₂' : Ty α × ε} (hV₁ : V₁ ≤ V₁') (hV₂ : V₂ ≤ V₂') (h : Γ.Wkn Δ ρ)
  : Wkn (V₁::V₂::Γ) (V₁'::V₂'::Δ) (Nat.liftWk (Nat.liftWk ρ))
  := Wkn_iff.mpr ((Wkn_iff.mp h).lift₂ hV₁ hV₂)

theorem Wkn.slift₂ {left right : Ty α × ε} (h : Γ.Wkn Δ ρ)
  : Wkn (left::right::Γ) (left::right::Δ) (Nat.liftWk (Nat.liftWk ρ))
  := h.lift₂ (le_refl _) (le_refl _)

theorem Wkn.lift_id₂ {V₁ V₁' V₂ V₂' : Ty α × ε} (hV₁ : V₁ ≤ V₁') (hV₂ : V₂ ≤ V₂') (h : Γ.Wkn Δ _root_.id)
  : Wkn (V₁::V₂::Γ) (V₁'::V₂'::Δ) _root_.id
  := Nat.liftWk_id ▸ Nat.liftWk_id ▸ h.lift₂ hV₁ hV₂

theorem Wkn.slift_id₂ (V₁ V₂ : Ty α × ε) (h : Γ.Wkn Δ _root_.id)
  : Wkn (V₁::V₂::Γ) (V₁::V₂::Δ) _root_.id
  := h.lift_id₂ (le_refl _) (le_refl _)

theorem Wkn.liftn₂ {V₁ V₁' V₂ V₂' : Ty α × ε} (hV₁ : V₁ ≤ V₁') (hV₂ : V₂ ≤ V₂') (h : Γ.Wkn Δ ρ)
  : Wkn (V₁::V₂::Γ) (V₁'::V₂'::Δ) (Nat.liftnWk 2 ρ)
  := Wkn_iff.mpr ((Wkn_iff.mp h).liftn₂ hV₁ hV₂)

def InS.liftn₂ {V₁ V₁' V₂ V₂' : Ty α × ε} (hV₁ : V₁ ≤ V₁') (hV₂ : V₂ ≤ V₂') (ρ : InS Γ Δ)
  : InS (V₁::V₂::Γ) (V₁'::V₂'::Δ)
  := ⟨Nat.liftnWk 2 ρ, ρ.prop.liftn₂ hV₁ hV₂⟩

theorem InS.lift_lift
  {V₁ V₁' V₂ V₂' : Ty α × ε} (hV₁ : V₁ ≤ V₁') (hV₂ : V₂ ≤ V₂') (ρ : InS Γ Δ)
  : (ρ.lift hV₂).lift hV₁ = ρ.liftn₂ hV₁ hV₂
  := by cases ρ; simp [lift, liftn₂, Nat.liftnWk_two]

abbrev InS.sliftn₂ {left right : Ty α × ε} (h : InS Γ Δ)
  : InS (left::right::Γ) (left::right::Δ)
  := h.liftn₂ (le_refl _) (le_refl _)

theorem InS.slift_slift
  {left right : Ty α × ε} (h : InS Γ Δ)
  : h.slift.slift = h.sliftn₂ (left := left) (right := right)
  := lift_lift (le_refl left) (le_refl right) h

theorem Wkn.sliftn₂ {left right : Ty α × ε} (h : Γ.Wkn Δ ρ)
  : Wkn (left::right::Γ) (left::right::Δ) (Nat.liftnWk 2 ρ)
  := h.liftn₂ (le_refl _) (le_refl _)

theorem Wkn.liftn_id₂ {V₁ V₁' V₂ V₂' : Ty α × ε} (hV₁ : V₁ ≤ V₁') (hV₂ : V₂ ≤ V₂')
  (h : Γ.Wkn Δ _root_.id)
  : Wkn (V₁::V₂::Γ) (V₁'::V₂'::Δ) _root_.id
  := Nat.liftnWk_id 2 ▸ h.liftn₂ hV₁ hV₂

theorem Wkn.sliftn_id₂ (V₁ V₂ : Ty α × ε) (h : Γ.Wkn Δ _root_.id)
  : Wkn (V₁::V₂::Γ) (V₁::V₂::Δ) _root_.id
  := h.liftn_id₂ (le_refl _) (le_refl _)

theorem Wkn.wk2 {left right inserted} {Γ : Ctx α ε}
  : Wkn (left::right::inserted::Γ) (left::right::Γ) (Nat.liftnWk 2 Nat.succ)
  := succ.sliftn₂

def InS.wk2 {left right inserted} {Γ : Ctx α ε}
  : InS (left::right::inserted::Γ) (left::right::Γ)
  := ⟨Nat.liftnWk 2 Nat.succ, Wkn.wk2⟩

@[simp]
theorem InS.coe_wk2 {left right inserted} {Γ : Ctx α ε}
  : (InS.wk2 (Γ := Γ) (left := left) (right := right) (inserted := inserted) : ℕ → ℕ)
  = Nat.liftnWk 2 Nat.succ
  := rfl

@[simp]
theorem InS.coe_liftn₂ {V₁ V₁' V₂ V₂' : Ty α × ε} (hV₁ : V₁ ≤ V₁') (hV₂ : V₂ ≤ V₂') (ρ : InS Γ Δ)
  : (InS.liftn₂ hV₁ hV₂ ρ : ℕ → ℕ) = Nat.liftnWk 2 ρ
  := rfl

theorem InS.coe_sliftn₂ {left right : Ty α × ε} (h : InS Γ Δ)
  : (InS.sliftn₂ (left := left) (right := right) h : ℕ → ℕ) = Nat.liftnWk 2 h
  := rfl

@[simp]
theorem InS.lift_wk1 {left right inserted} {Γ : Ctx α ε}
  : wk1.lift (le_refl _) = (wk2 : InS (left::right::inserted::Γ) (left::right::Γ))
  := by ext; simp [Nat.liftnWk_two]

theorem Wkn.liftn_append (Ξ) (h : Γ.Wkn Δ ρ)
  : Wkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk Ξ.length ρ)
  := Wkn_iff.mpr ((Wkn_iff.mp h).liftn_append Ξ)

def InS.liftn_append (Ξ) (ρ : InS Γ Δ)
  : InS (Ξ ++ Γ) (Ξ ++ Δ)
  := ⟨Nat.liftnWk Ξ.length ρ, ρ.prop.liftn_append Ξ⟩

theorem Wkn.liftn_append' {Ξ} (hn : n = Ξ.length) (h : Γ.Wkn Δ ρ)
  : Wkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk n ρ)
  := hn ▸ liftn_append Ξ h

theorem Wkn.liftn_append_id (Ξ) (h : Γ.Wkn Δ _root_.id)
  : Wkn (Ξ ++ Γ) (Ξ ++ Δ) _root_.id
  := Nat.liftnWk_id _ ▸ liftn_append Ξ h

theorem Wkn.liftn_append_cons (A Ξ) (h : Γ.Wkn Δ ρ)
  : Wkn (A::(Ξ ++ Γ)) (A::(Ξ ++ Δ)) (Nat.liftnWk (Ξ.length + 1) ρ)
  := liftn_append (A::Ξ) h

theorem Wkn.liftn_append_cons' (A) {Ξ} (hn : n = Ξ.length + 1) (h : Γ.Wkn Δ ρ)
  : Wkn (A::(Ξ ++ Γ)) (A::(Ξ ++ Δ)) (Nat.liftnWk n ρ)
  := hn ▸ liftn_append_cons A Ξ h

theorem Wkn.liftn_append_cons_id (A Ξ) (h : Γ.Wkn Δ _root_.id)
  : Wkn (A::(Ξ ++ Γ)) (A::(Ξ ++ Δ)) _root_.id
  := Nat.liftnWk_id _ ▸  liftn_append_cons A Ξ h

theorem Wkn.stepn_append (Ξ) (h : Γ.Wkn Δ ρ)
  : Wkn (Ξ ++ Γ) Δ (Nat.stepnWk Ξ.length ρ)
  := Wkn_iff.mpr ((Wkn_iff.mp h).stepn_append Ξ)

theorem Wkn.stepn_append' {Ξ} (hn : n = Ξ.length) (h : Γ.Wkn Δ ρ)
  : Wkn (Ξ ++ Γ) Δ (Nat.stepnWk n ρ)
  := hn ▸ stepn_append Ξ h

theorem Wkn.id_len_le : Γ.Wkn Δ _root_.id → Δ.length ≤ Γ.length := by
  rw [Wkn_iff]; apply List.NWkn.id_len_le

theorem Wkn.comp {Γ Δ Ξ : Ctx α ε} {ρ σ}
  : Γ.Wkn Δ ρ → Δ.Wkn Ξ σ → Γ.Wkn Ξ (ρ ∘ σ)
  := by
  simp only [Wkn_iff]
  apply List.NWkn.comp

def InS.comp {Γ Δ Ξ : Ctx α ε} (ρ : InS Γ Δ) (σ : InS Δ Ξ) : InS Γ Ξ
  := ⟨(ρ : ℕ → ℕ) ∘ (σ : ℕ → ℕ), ρ.2.comp σ.2⟩

theorem InS.lift_comp_lift {Γ Δ Ξ : Ctx α ε} (ρ : InS Γ Δ) (σ : InS Δ Ξ)
  {lo hi : Ty α × ε} (hρ : lo ≤ mid) (hσ : mid ≤ hi)
  : (ρ.lift hρ).comp (σ.lift hσ) = (ρ.comp σ).lift (le_trans hρ hσ)
  := by
    cases ρ; cases σ
    simp only [comp, lift, Nat.liftWk_comp]

theorem InS.liftn₂_comp_liftn₂ {Γ Δ Ξ : Ctx α ε} (ρ : InS Γ Δ) (σ : InS Δ Ξ)
  (hρ : lo ≤ mid) (hσ : mid ≤ hi) (hρ' : lo' ≤ mid') (hσ' : mid' ≤ hi')
  : (ρ.liftn₂ hρ hρ').comp (σ.liftn₂ hσ hσ') = (ρ.comp σ).liftn₂ (le_trans hρ hσ) (le_trans hρ' hσ')
  := by simp [<-lift_lift, lift_comp_lift]

@[simp]
theorem InS.coe_comp {Γ Δ Ξ : Ctx α ε} (ρ : InS Γ Δ) (σ : InS Δ Ξ)
  : (ρ.comp σ : ℕ → ℕ) = (ρ : ℕ → ℕ) ∘ (σ : ℕ → ℕ)
  := rfl

theorem InS.comp_congr {Γ Δ Ξ : Ctx α ε} {ρ ρ' : InS Γ Δ} {σ σ' : InS Δ Ξ}
    (hρ : ρ ≈ ρ') (hσ : σ ≈ σ') : ρ.comp σ ≈ ρ'.comp σ' := λi hi => by
  simp only [Set.mem_setOf_eq, coe_comp, Function.comp_apply, hσ i hi, hρ _ (σ'.prop i hi).length]

theorem Wkn.drop {ρ : ℕ → ℕ} : Γ.Wkn [] ρ
  := λi hi => by cases hi

def InS.drop : InS Γ [] := ⟨_root_.id, Wkn.drop⟩

theorem InS.drop_congr (ρ σ : InS Γ []) : ρ ≈ σ := λi hi => by cases hi

theorem Wkn.from_nil {ρ : ℕ → ℕ} (hρ : Wkn [] Γ ρ) : Γ = []
  := by cases Γ with
  | nil => rfl
  | cons => cases (hρ 0 (by simp)).length

theorem Wkn.nil_iff {ρ : ℕ → ℕ} : Wkn [] Γ ρ ↔ Γ = []
  := ⟨Wkn.from_nil, λh => h.symm ▸ Wkn.drop⟩

def EWkn (Γ Δ : Ctx α ε) (ρ : ℕ → ℕ) : Prop -- TODO: fin argument as defeq?
  := List.NEWkn Γ Δ ρ

theorem EWkn.wkn {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} (h : Γ.EWkn Δ ρ) : Γ.Wkn Δ ρ
  := Wkn_iff.mpr h.toNWkn

theorem EWkn.var {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} (h : Γ.EWkn Δ ρ) {i} (hi : i < Δ.length)
  : Γ.Var (ρ i) (Δ.get ⟨i, hi⟩)
  := h.wkn i hi

theorem EWkn.var_inv {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} (h : Γ.EWkn Δ ρ)
  (hi : i < Δ.length) (hv : Γ.Var (ρ i) V)
  : Δ.Var i V := ⟨hi, have ⟨_, he⟩ := h i hi; he ▸ hv.get⟩

@[simp]
theorem EWkn.id {Γ : Ctx α ε} : Γ.EWkn Γ id := List.NEWkn.id _

theorem EWkn.lift {V : Ty α × ε} (h : Γ.EWkn Δ ρ)
  : EWkn (V::Γ) (V::Δ) (Nat.liftWk ρ)
  := List.NEWkn.lift h

theorem EWkn.lift_tail {left right : Ty α × ε} (h : EWkn (left::Γ) (right::Δ) (Nat.liftWk ρ))
  : EWkn Γ Δ ρ := List.NEWkn.lift_tail h

theorem EWkn.lift_head {left right : Ty α × ε} (h : EWkn (left::Γ) (right::Δ) (Nat.liftWk ρ))
  : left = right := List.NEWkn.lift_head h

@[simp]
theorem EWkn.lift_iff {left right : Ty α × ε} {Γ Δ}
    : EWkn (left::Γ) (right::Δ) (Nat.liftWk ρ) ↔ left = right ∧ EWkn Γ Δ ρ
    := ⟨λh => ⟨h.lift_head, h.lift_tail⟩, λ⟨h, h'⟩ => h ▸ h'.lift⟩

theorem EWkn.lift_id {V : Ty α × ε} (h : Γ.EWkn Δ _root_.id)
  : EWkn (V::Γ) (V::Δ) _root_.id
  := Nat.liftWk_id ▸ h.lift

theorem EWkn.lift_id_tail {left right : Ty α × ε} (h : EWkn (left::Γ) (right::Δ) _root_.id)
  : EWkn Γ Δ _root_.id := (Nat.liftWk_id ▸ h).lift_tail

theorem EWkn.lift_id_head {left right : Ty α × ε} (h : EWkn (left::Γ) (right::Δ) _root_.id)
  : left = right := (Nat.liftWk_id ▸ h).lift_head

@[simp]
theorem EWkn.lift_id_iff {left right : Ty α × ε} {Γ Δ}
    : EWkn (left::Γ) (right::Δ) _root_.id ↔ left = right ∧ EWkn Γ Δ _root_.id
    := ⟨λh => ⟨h.lift_id_head, h.lift_id_tail⟩, λ⟨h, h'⟩ => h ▸ h'.lift_id⟩

theorem EWkn.step {head : Ty α × ε} (h : Γ.EWkn Δ ρ) : EWkn (head::Γ) Δ (Nat.stepWk ρ)
  := List.NEWkn.step _ h

theorem EWkn.step_tail {head : Ty α × ε} (h : EWkn (head::Γ) Δ (Nat.stepWk ρ))
  : EWkn Γ Δ ρ := List.NEWkn.step_tail h

@[simp]
theorem EWkn.step_iff {head : Ty α × ε} {Γ Δ}
  : EWkn (head::Γ) Δ (Nat.stepWk ρ) ↔ EWkn Γ Δ ρ
  := List.NEWkn.step_iff _ _ _ _

@[simp]
theorem EWkn.succ_comp_iff {head : Ty α × ε} {Γ Δ}
  : EWkn (head::Γ) Δ (Nat.succ ∘ ρ) ↔ EWkn Γ Δ ρ
  := List.NEWkn.step_iff _ _ _ _

@[simp]
theorem EWkn.succ {head} {Γ : Ctx α ε}
  : EWkn (head::Γ) Γ Nat.succ
  := step (head := head) (id (Γ := Γ))

theorem EWkn.wk1 {head inserted} {Γ : Ctx α ε}
  : EWkn (head::inserted::Γ) (head::Γ) (Nat.liftWk Nat.succ)
  := succ.lift

theorem EWkn.lift₂ {left right : Ty α × ε} (h : Γ.EWkn Δ ρ)
  : EWkn (left::right::Γ) (left::right::Δ) (Nat.liftWk (Nat.liftWk ρ))
  := h.lift.lift

theorem EWkn.lift_id₂ {left right : Ty α × ε} (h : Γ.EWkn Δ _root_.id)
  : EWkn (left::right::Γ) (left::right::Δ) _root_.id
  := h.lift_id.lift_id

theorem EWkn.liftn₂ {left right : Ty α × ε} (h : Γ.EWkn Δ ρ)
  : EWkn (left::right::Γ) (left::right::Δ) (Nat.liftnWk 2 ρ)
  := Nat.liftnWk_two ▸ h.lift₂

theorem EWkn.liftn_id₂ {left right : Ty α × ε} (h : Γ.EWkn Δ _root_.id)
  : EWkn (left::right::Γ) (left::right::Δ) _root_.id
  := h.lift_id₂

theorem EWkn.liftn_append (Ξ) (h : Γ.EWkn Δ ρ)
  : EWkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk Ξ.length ρ)
  := List.NEWkn.liftn_append _ h

theorem EWkn.liftn_append' {Ξ} (hn : n = Ξ.length) (h : Γ.EWkn Δ ρ)
  : EWkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk n ρ)
  := hn ▸ liftn_append Ξ h

theorem EWkn.liftn_append_id (Ξ) (h : Γ.EWkn Δ _root_.id)
  : EWkn (Ξ ++ Γ) (Ξ ++ Δ) _root_.id
  := Nat.liftnWk_id _ ▸ liftn_append Ξ h

theorem EWkn.liftn_append_cons (A Ξ) (h : Γ.EWkn Δ ρ)
  : EWkn (A::(Ξ ++ Γ)) (A::(Ξ ++ Δ)) (Nat.liftnWk (Ξ.length + 1) ρ)
  := liftn_append (A::Ξ) h

theorem EWkn.liftn_append_cons' (A) {Ξ} (hn : n = Ξ.length + 1) (h : Γ.EWkn Δ ρ)
  : EWkn (A::(Ξ ++ Γ)) (A::(Ξ ++ Δ)) (Nat.liftnWk n ρ)
  := hn ▸ liftn_append_cons A Ξ h

theorem EWkn.liftn_append_cons_id (A Ξ) (h : Γ.EWkn Δ _root_.id)
  : EWkn (A::(Ξ ++ Γ)) (A::(Ξ ++ Δ)) _root_.id
  := Nat.liftnWk_id _ ▸  liftn_append_cons A Ξ h

theorem EWkn.stepn_append (Ξ) (h : Γ.EWkn Δ ρ)
  : EWkn (Ξ ++ Γ) Δ (Nat.stepnWk Ξ.length ρ)
  := List.NEWkn.stepn_append _ h

theorem EWkn.stepn_append' {Ξ} (hn : n = Ξ.length) (h : Γ.EWkn Δ ρ)
  : EWkn (Ξ ++ Γ) Δ (Nat.stepnWk n ρ)
  := hn ▸ stepn_append Ξ h

theorem Var.mem {Γ : Ctx α ε} {n V} (h : Var Γ n V) : ∃V', V' ∈ Γ ∧ V' ≤ V
  := by induction n generalizing Γ with
  | zero =>
    cases Γ with
    | nil => cases h.length
    | cons H Γ => exact ⟨H, List.Mem.head _, h.get⟩
  | succ n I =>
    cases Γ with
    | nil => cases h.length
    | cons H Γ =>
      have ⟨V', hV', hV⟩ := I h.tail;
      exact ⟨V', List.Mem.tail _ hV', hV⟩

theorem Var.exists_of_mem {Γ : Ctx α ε} {V} (h : V ∈ Γ)
  : ∃n, ∃h : Var Γ n V, Γ.get ⟨n, h.length⟩ = V
  := by induction h with
  | head => exact ⟨0, by simp, rfl⟩
  | tail _ _ I =>
    have ⟨n, hn, hn'⟩ := I;
    exact ⟨n + 1, hn.step, by simp only [List.length_cons, List.get_eq_getElem,
      List.getElem_cons_succ]; exact hn'⟩

theorem mem_wk {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} (h : Γ.Wkn Δ ρ) (hV : V ∈ Δ) : ∃V', V' ∈ Γ ∧ V' ≤ V
  :=
  have ⟨n, hn, hn'⟩ := Var.exists_of_mem hV;
  have hρn := h n hn.length;
  have ⟨V', hV', hV⟩ := Var.mem hρn;
  ⟨V', hV', hn' ▸ hV⟩

theorem Wkn.effect {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} (h : Γ.Wkn Δ ρ) (i : ℕ) (hi : i < Δ.length)
  : (Γ.effect (ρ i)) ≤ Δ.effect i
  := by
    simp only [Ctx.effect, (h i hi).length, ↓reduceDIte, List.get_eq_getElem, hi]
    exact (h i hi).get.2

-- theorem EWkn.id_len_le : Γ.EWkn Δ _root_.id → Δ.length ≤ Γ.length := by
--   apply List.NEWkn.id_len_le

def Types (Γ : Ctx α ε) : List (Ty α) := Γ.map Prod.fst

theorem length_types (Γ : Ctx α ε) : Γ.Types.length = Γ.length := by
  simp [Types]

def Effects (Γ : Ctx α ε) : List ε := Γ.map Prod.snd

theorem length_effects (Γ : Ctx α ε) : Γ.Effects.length = Γ.length := by
  simp [Effects]

def WknTy (Γ Δ : Ctx α ε) (ρ : ℕ → ℕ) : Prop := Γ.Types.NWkn Δ.Types ρ

theorem WknTy.id_types_len_le : Γ.WknTy Δ _root_.id → Δ.Types.length ≤ Γ.Types.length
  := List.NWkn.id_len_le

theorem WknTy.id_len_le : Γ.WknTy Δ _root_.id → Δ.length ≤ Γ.length
  := Δ.length_types ▸ Γ.length_types ▸ WknTy.id_types_len_le

theorem Var.wk_res (h : V ≤ V') (hΓ : Γ.Var n V) : Γ.Var n V' where
  length := hΓ.length
  getElem := le_trans hΓ.get h

theorem Var.wk_res₂ (hA : A ≤ A') (he : e ≤ e') (hΓ : Γ.Var n ⟨A, e⟩) : Γ.Var n ⟨A', e⟩
  := hΓ.wk_res (by simp [hA, he])

theorem Var.wk_ty (h : A ≤ A') (hΓ : Γ.Var n ⟨A, e⟩) : Γ.Var n ⟨A', e⟩
  := hΓ.wk_res (by simp [h])

theorem Var.wk_eff (h : e ≤ e') (hΓ : Γ.Var n ⟨A, e⟩) : Γ.Var n ⟨A, e'⟩
  := hΓ.wk_res (by simp [h])

theorem Var.wk (h : Γ.Wkn Δ ρ) (hΓ : Δ.Var n V) : Γ.Var (ρ n) V where
  length := (h n hΓ.length).1
  getElem := le_trans (h n hΓ.length).2 hΓ.get

def Var.toEffect {Γ : Ctx α ε} {n : ℕ} {V} (h : Γ.Var n V)
  : Γ.Var n ⟨V.1, Γ.effect n⟩
  := ⟨h.length, by
    constructor
    exact h.get.1
    simp [effect, h.length]
  ⟩

end Ctx

end Basic

section OrderBot

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [OrderBot ε]

theorem Ctx.Var.bhead {head : Ty α} {e : ε} {Γ : Ctx α ε}
  : Var (⟨head, ⊥⟩::Γ) 0 ⟨head, e⟩ := Var.head (by simp) Γ

def Ctx.var_bot_head {Γ : Ctx α ε} : Var (⟨A, ⊥⟩::Γ) 0 ⟨A, e⟩
  := Var.head (by simp) Γ

theorem Ctx.IsInitial.wk {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} (h : Γ.Wkn Δ ρ) : IsInitial Δ → IsInitial Γ
  | ⟨_, hV, hI⟩ =>
    have ⟨V', hV', hV⟩ := mem_wk h hV;
    ⟨V', hV', hI.1.anti hV.1, le_bot_iff.mp (hI.2 ▸ hV.2)⟩

end OrderBot
