import Discretion.Wk.List
import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Fv.Basic
import DeBruijnSSA.BinSyntax.Syntax.Effect.Definitions

import DeBruijnSSA.BinSyntax.Typing.Ctx
import DeBruijnSSA.BinSyntax.Typing.Term.Basic

namespace BinSyntax

section Basic

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]

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

def Body.WfD.wk {Γ Δ : Ctx α ε} {ρ} {b : Body φ} (h : Γ.Wkn Δ ρ) : WfD Δ b Ξ → WfD Γ (b.wk ρ) Ξ
  | nil => nil
  | let1 a b => let1 (a.wk h) (b.wk h.slift)
  | let2 a b => let2 (a.wk h) (b.wk h.sliftn₂)

def Body.WfD.wk_id {Γ Δ : Ctx α ε} {b : Body φ} (h : Γ.Wkn Δ id) : WfD Δ b Ξ → WfD Γ b Ξ
  | nil => nil
  | let1 a b => let1 (a.wk_id h) (b.wk_id (Nat.liftWk_id ▸ h.slift))
  | let2 a b => let2 (a.wk_id h) (b.wk_id (Nat.liftnWk_id 2 ▸ h.sliftn₂))
