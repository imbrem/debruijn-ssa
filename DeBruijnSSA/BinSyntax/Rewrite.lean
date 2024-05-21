import DeBruijnSSA.BinSyntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Subst

namespace BinSyntax

variable [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

-- TODO: define as Subst.cons or smt...
def Term.subst₂ (a b: Term φ) : Subst φ
  | 0 => a
  | 1 => b
  | n + 2 => Term.var n

def Term.WfD.subst₂ {Γ : Ctx α ε} {a b : Term φ}
  (ha : a.WfD Γ ⟨A, e⟩) (hb : b.WfD Γ ⟨B, e'⟩)
  : (a.subst₂ b).WfD Γ (⟨A, e⟩::⟨B, e'⟩::Γ)
  | ⟨0, _⟩ => ha
  | ⟨1, _⟩ => hb
  | ⟨n + 2, h⟩ => var ⟨by simp at h; exact h, le_refl _⟩

inductive Region.Beta (Γ : Ctx α ε) : Region φ → Region φ → Prop
  | let1 (e : Term φ) (r : Region φ)
    : e.infEffect Γ = ⊥ → Beta Γ (r.let1 e) (r.vsubst e.subst0)
  | let2 (a : Term φ) (b : Term φ) (r : Region φ)
    : a.infEffect Γ = ⊥ → b.infEffect Γ = ⊥ → Beta Γ (r.let2 (a.pair b)) (r.vsubst (a.subst₂ b))

theorem Region.Beta.let1_pure {Γ : Ctx α ε} {e} {r r' : Region φ}
  (h : Region.Beta Γ (r.let1 e) r') : e.infEffect Γ = ⊥ := by cases h; assumption

theorem Region.Beta.let1_trg {Γ : Ctx α ε} {e} {r r' : Region φ}
  (h : Region.Beta Γ (r.let1 e) r') : r' = r.vsubst e.subst0 := by cases h; rfl

theorem Region.Beta.let2_left_pure {Γ : Ctx α ε} {a b : Term φ} {r r' : Region φ}
  (h : Region.Beta Γ (r.let2 (a.pair b)) r') : a.infEffect Γ = ⊥ := by cases h; assumption

theorem Region.Beta.let2_right_pure {Γ : Ctx α ε} {a b : Term φ} {r r' : Region φ}
  (h : Region.Beta Γ (r.let2 (a.pair b)) r') : b.infEffect Γ = ⊥ := by cases h; assumption

theorem Region.Beta.let2_trg {Γ : Ctx α ε} {a b : Term φ} {r r' : Region φ}
  (h : Region.Beta Γ (r.let2 (a.pair b)) r') : r' = r.vsubst (a.subst₂ b) := by cases h; rfl

def Region.Beta.WfD {Γ : Ctx α ε} {r r' : Region φ}
  : Region.Beta Γ r r' → r.WfD Γ A → r'.WfD Γ A
  | h, WfD.let1 de dr => h.let1_trg ▸ dr.vsubst (h.let1_pure ▸ de.toInfEffect.subst0)
  | h, WfD.let2 (Term.WfD.pair da db) dr => h.let2_trg ▸
    dr.vsubst ((h.let2_left_pure ▸ da.toInfEffect).subst₂ (h.let2_right_pure ▸ db.toInfEffect))

end BinSyntax
