import DeBruijnSSA.BinSyntax.Rewrite.Term.Eqv
import DeBruijnSSA.BinSyntax.Typing.Term.Compose

import Discretion.Utils.Quotient

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

--TODO: seq here is the opposite of seq for region; think about fixing this...

def Eqv.nil {A : Ty α} {Γ : Ctx α ε} : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A, e⟩
  := var 0 (by simp)

theorem Eqv.wk0_nil {A : Ty α} {Γ : Ctx α ε}
  : (nil : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A, e⟩).wk0 (head := ⟨head, ⊥⟩) = (var 1 (by simp)) := rfl

@[simp]
theorem Eqv.wk_id_nil {A : Ty α} {Γ Δ : Ctx α ε} {hΓ : Ctx.Wkn (⟨A, ⊥⟩::Γ) ((A, ⊥)::Δ) id}
  : (nil : Eqv φ (⟨A, ⊥⟩::Δ) ⟨A, e⟩).wk_id hΓ = nil := rfl

@[simp]
theorem Eqv.wk1_nil {A : Ty α} {Γ : Ctx α ε}
  : (nil (φ := φ) (A := A) (Γ := Γ) (e := e)).wk1 (inserted := inserted) = nil
  := rfl

@[simp]
theorem Eqv.wk2_nil {A : Ty α} {Γ : Ctx α ε}
  : (nil (φ := φ) (A := A) (Γ := head::Γ) (e := e)).wk2 (inserted := inserted) = nil
  := rfl

@[simp]
theorem Eqv.wk_lift_nil {A : Ty α} {Δ : Ctx α ε} {ρ : Ctx.InS Γ Δ}
  : (nil : Eqv φ (⟨A, ⊥⟩::Δ) ⟨A, e⟩).wk (ρ.lift (le_refl _)) = nil := rfl

@[simp]
theorem Eqv.wk_liftn₂_nil {A : Ty α} {Δ : Ctx α ε} {ρ : Ctx.InS Γ Δ}
  : (nil : Eqv φ (⟨A, ⊥⟩::⟨B, ⊥⟩::Δ) ⟨A, e⟩).wk (ρ.liftn₂ (le_refl _) (le_refl _)) = nil := rfl

@[simp]
theorem Eqv.subst_lift_nil {A : Ty α} {Γ : Ctx α ε} {σ : Subst.Eqv φ Γ Δ} {h}
  : (nil : Eqv φ (⟨A, ⊥⟩::Δ) ⟨A, e⟩).subst (σ.lift h) = nil := by
  induction σ using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.wk_eff_nil {A : Ty α} {Γ : Ctx α ε} (h : lo ≤ hi)
  : (nil (φ := φ) (A := A) (Γ := Γ)).wk_eff h = nil
  := rfl

theorem Eqv.nil_pure {A : Ty α} {Γ : Ctx α ε}
  : (nil : Eqv φ (⟨A, ⊥⟩::Γ) ⟨A, e⟩) = nil.wk_eff bot_le
  := rfl

@[simp]
theorem Eqv.subst0_nil_wk1 {Γ : Ctx α ε}
  (a : Eqv φ (⟨A, ⊥⟩::Γ) V) : a.wk1.subst nil.subst0 = a
  := by simp [nil]

@[simp]
theorem Eqv.nil_subst0 {Γ : Ctx α ε} (a : Eqv φ Γ ⟨A, ⊥⟩)
  : (nil (e := e)).subst a.subst0 = a.wk_eff bot_le
  := by induction a using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.nil_subst_lift {Γ : Ctx α ε} {σ : Subst.Eqv φ Γ Δ}
  : (nil : Eqv φ (⟨A, ⊥⟩::Δ) ⟨A, e⟩).subst (σ.lift (le_refl _)) = nil := by
  induction σ using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.nil_subst_liftn₂ {Γ : Ctx α ε} {σ : Subst.Eqv φ Γ Δ}
  : (nil : Eqv φ (⟨A, ⊥⟩::⟨B, ⊥⟩::Δ) ⟨A, e⟩).subst (σ.liftn₂ (le_refl _) (le_refl _)) = nil := by
  induction σ using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.Pure.nil {A : Ty α} {Γ : Ctx α ε} : (nil (φ := φ) (A := A) (Γ := Γ) (e := e)).Pure
  := ⟨Eqv.nil, rfl⟩

def Eqv.seq {A B C : Ty α} {Γ : Ctx α ε}
(a : Eqv φ ((A, ⊥)::Γ) (B, e)) (b : Eqv φ ((B, ⊥)::Γ) (C, e))
  : Eqv φ ((A, ⊥)::Γ) (C, e)
  := let1 a b.wk1

infixl:65 " ;;' "  => Eqv.seq

theorem Eqv.seq_pure {A B C : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ ((A, ⊥)::Γ) (B, ⊥)) (b : Eqv φ ((B, ⊥)::Γ) (C, ⊥)) : a ;;' b = b.wk1.subst a.subst0
  := let1_beta_pure

theorem Eqv.pure_seq {A B C : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ ((A, ⊥)::Γ) (B, ⊥)) (b : Eqv φ ((B, ⊥)::Γ) (C, e))
  : (a.wk_eff (by simp)) ;;' b = b.wk1.subst a.subst0
  := let1_beta

theorem Eqv.wk_lift_seq {A B C : Ty α} {Δ : Ctx α ε} {ρ : Ctx.InS Γ Δ}
  (a : Eqv φ ((A, ⊥)::Δ) (B, e)) (b : Eqv φ ((B, ⊥)::Δ) (C, e))
  : (a ;;' b).wk (ρ.lift (le_refl _)) = (a.wk (ρ.lift (le_refl _))) ;;' (b.wk (ρ.lift (le_refl _)))
  := by rw [seq, seq, wk_let1]; simp only [wk1, wk_wk]; congr 2; ext k; cases k <;> rfl

theorem Eqv.subst_lift_seq {A B C : Ty α} {Δ : Ctx α ε} {σ : Subst.Eqv φ Γ Δ}
  (a : Eqv φ ((A, ⊥)::Δ) (B, e)) (b : Eqv φ ((B, ⊥)::Δ) (C, e))
  : (a ;;' b).subst (σ.lift (le_refl _))
  = (a.subst (σ.lift (le_refl _))) ;;' (b.subst (σ.lift (le_refl _))) := by
  rw [seq, seq, subst_let1]
  congr
  induction σ using Quotient.inductionOn
  induction b using Quotient.inductionOn
  apply Eqv.eq_of_term_eq
  simp only [Set.mem_setOf_eq, InS.coe_subst, Subst.InS.coe_lift, InS.coe_wk, Ctx.InS.coe_wk1, ←
    Term.subst_fromWk, Term.subst_subst]
  congr
  funext k; cases k <;> simp only [Subst.comp, Term.subst, Nat.liftWk_succ, Nat.succ_eq_add_one,
    Subst.lift_succ, Term.wk_wk, Term.subst_fromWk, Nat.liftWk_succ_comp_succ] <;> rfl

theorem Eqv.wk0_seq {A B C : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ ((A, ⊥)::Γ) (B, e)) (b : Eqv φ ((B, ⊥)::Γ) (C, e))
  : (a ;;' b).wk0 (head := ⟨head, ⊥⟩) = a.wk0 ;;' b.wk1 := by rw [seq, wk0_let1]; rfl

theorem Eqv.wk1_seq {A B C : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ ((A, ⊥)::Γ) (B, e)) (b : Eqv φ ((B, ⊥)::Γ) (C, e))
  : (a ;;' b).wk1 (inserted := inserted) = a.wk1 ;;' b.wk1 := by rw [seq, seq, wk1_let1, wk1_wk2]

theorem Eqv.wk2_seq {A B C : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ ((A, ⊥)::head::Γ) (B, e)) (b : Eqv φ ((B, ⊥)::head::Γ) (C, e))
  : (a ;;' b).wk2 (inserted := inserted) = a.wk2 ;;' b.wk2
  := by simp only [wk2, <-Ctx.InS.lift_wk1, wk_lift_seq]

@[simp]
theorem Eqv.seq_quot {A B C : Ty α} {Γ : Ctx α ε}
  (a : InS φ ((A, ⊥)::Γ) (B, e)) (b : InS φ ((B, ⊥)::Γ) (C, e))
  : ⟦a⟧ ;;' ⟦b⟧ = ⟦a.seq b⟧
  := rfl

theorem Eqv.seq_wk_eff {A B C : Ty α} {Γ : Ctx α ε} {h : lo ≤ hi}
  {a : Eqv φ ((A, ⊥)::Γ) (B, lo)} {b : Eqv φ ((B, ⊥)::Γ) (C, lo)}
  : (a.wk_eff h) ;;' (b.wk_eff h) = (a ;;' b).wk_eff h := by
  induction a using Quotient.inductionOn;
  induction b using Quotient.inductionOn;
  rfl

theorem Eqv.wk_eff_seq {A B C : Ty α} {Γ : Ctx α ε} {h : lo ≤ hi}
  {a : Eqv φ ((A, ⊥)::Γ) (B, lo)} {b : Eqv φ ((B, ⊥)::Γ) (C, lo)}
  : (a ;;' b).wk_eff h = (a.wk_eff h) ;;' (b.wk_eff h) := seq_wk_eff.symm

theorem Eqv.seq_nil {A B : Ty α} {Γ : Ctx α ε} (a : Eqv φ ((A, ⊥)::Γ) (B, e))
  : a ;;' nil = a := let1_eta

theorem Eqv.nil_seq {A B : Ty α} {Γ : Ctx α ε} (a : Eqv φ ((A, ⊥)::Γ) (B, e))
  : nil ;;' a = a := by
  rw [seq, <-wk_eff_nil (lo := ⊥), let1_beta, subst0_nil_wk1]

theorem Eqv.seq_let1 {A B C : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ ((A, ⊥)::Γ) (B, e))
  (b : Eqv φ ((B, ⊥)::(A, ⊥)::Γ) (C, e)) (c : Eqv φ ((C, ⊥)::Γ) (D, e))
  : a.let1 b ;;' c = a.let1 (b ;;' c.wk1) := by rw [seq, seq, let1_let1]

theorem Eqv.seq_let2 {A B C D : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ ((A, ⊥)::Γ) (B.prod B', e))
  (b : Eqv φ ((B', ⊥)::(B, ⊥)::(A, ⊥)::Γ) (C, e)) (c : Eqv φ ((C, ⊥)::Γ) (D, e))
  : a.let2 b ;;' c = a.let2 (b ;;' c.wk1.wk1) := by rw [seq, seq, let1_let2]

theorem Eqv.let1_seq {A B C : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ ((A, ⊥)::Γ) (B, e))
  (b : Eqv φ ((B, ⊥)::Γ) (C, e)) (c : Eqv φ ((C, ⊥)::(A, ⊥)::Γ) (D, e))
  : let1 (a ;;' b) c = let1 a (b.wk1 ;;' c)
  := by rw [seq, let1_let1]; rfl

theorem Eqv.seq_assoc {A B C D : Ty α} {Γ : Ctx α ε}
  (a : Eqv φ ((A, ⊥)::Γ) (B, e)) (b : Eqv φ ((B, ⊥)::Γ) (C, e)) (c : Eqv φ ((C, ⊥)::Γ) (D, e))
  : a ;;' (b ;;' c) = (a ;;' b) ;;' c := by simp only [seq, let1_let1, wk1_let1, wk1_wk2]
