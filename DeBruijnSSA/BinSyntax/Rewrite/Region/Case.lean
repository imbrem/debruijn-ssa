import DeBruijnSSA.BinSyntax.Rewrite.Region.Eqv

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

theorem Eqv.case_let1
  {x : Term.Eqv φ Γ ⟨X, e⟩} {d : Term.Eqv φ (⟨X, ⊥⟩::Γ) ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) L} {r : Eqv φ (⟨B, ⊥⟩::Γ) L}
  : case (Term.Eqv.let1 x d) l r = let1 x (case d l.vwk1 r.vwk1) := by
  rw [case_bind, let1_let1]
  apply Eq.symm
  rw [case_bind]
  simp [vwk1_vwk2]

theorem Eqv.case_let2
  {x : Term.Eqv φ Γ ⟨X.prod Y, e⟩} {d : Term.Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::Γ) ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) L} {r : Eqv φ (⟨B, ⊥⟩::Γ) L}
  : case (Term.Eqv.let2 x d) l r = let2 x (case d l.vwk1.vwk1 r.vwk1.vwk1) := by
  rw [case_bind, let1_let2]
  apply Eq.symm
  rw [case_bind]
  simp [vwk1_vwk2]

theorem Eqv.case_case
  {dd : Term.Eqv φ Γ ⟨X.coprod Y, e⟩}
  {dl : Term.Eqv φ (⟨X, ⊥⟩::Γ) ⟨Ty.coprod A B, e⟩}
  {dr : Term.Eqv φ (⟨Y, ⊥⟩::Γ) ⟨Ty.coprod A B, e⟩}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) L} {r : Eqv φ (⟨B, ⊥⟩::Γ) L}
  : case (Term.Eqv.case dd dl dr) l r = case dd (case dl l.vwk1 r.vwk1) (case dr l.vwk1 r.vwk1)
  := by
  rw [case_bind, let1_case]
  congr <;> {
    apply Eq.symm
    rw [case_bind]
    simp [vwk1_vwk2]
  }
