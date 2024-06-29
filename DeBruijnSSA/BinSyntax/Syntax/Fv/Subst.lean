import Discretion.Wk.Nat
import Discretion.Wk.Fin
import Discretion.Wk.Multiset
import Discretion.Wk.Multiset

import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Fv.Basic

namespace BinSyntax

/-! ### Lemmas about substitution -/
section Subst

@[simp]
theorem Terminator.fl_vsubst (σ : Term.Subst φ) (r : Terminator φ) : (r.vsubst σ).fl = r.fl := by
  induction r generalizing σ <;> simp [*]

@[simp]
theorem TRegion.fl_vsubst (σ : Term.Subst φ) (r : TRegion φ) : (r.vsubst σ).fl = r.fl := by
  induction r generalizing σ <;> simp [*]

@[simp]
theorem Block.fl_vsubst (σ : Term.Subst φ) (r : Block φ) : (r.vsubst σ).fl = r.fl := by simp

@[simp]
theorem BBRegion.fl_vsubst (σ : Term.Subst φ) (r : BBRegion φ) : (r.vsubst σ).fl = r.fl := by
  induction r generalizing σ; simp [*]

@[simp]
theorem Region.fl_vsubst (σ : Term.Subst φ) (r : Region φ) : (r.vsubst σ).fl = r.fl := by
  induction r generalizing σ <;> simp [*]

def Term.Subst.fvs (σ : Term.Subst φ) (i : ℕ) : Set ℕ := (σ i).fvs

theorem Term.fvs_subst (σ : Term.Subst φ) (t : Term φ) : (t.subst σ).fvs = ⋃ x ∈ t.fvs, σ.fvs x
  := by induction t with
  | pair a b Ia Ib =>
    ext k
    simp only [fvs, Ia, Subst.fvs, Ib, Set.mem_union, Set.mem_iUnion, exists_prop]
    constructor
    intro h
    cases h with
    | inl h => exact have ⟨x, h, hk⟩ := h; ⟨x, Or.inl h, hk⟩
    | inr h => exact have ⟨x, h, hk⟩ := h; ⟨x, Or.inr h, hk⟩
    intro ⟨x, h, hk⟩
    cases h with
    | inl h => exact Or.inl ⟨x, h, hk⟩
    | inr h => exact Or.inr ⟨x, h, hk⟩
  | _ => simp [Subst.fvs, *]

-- TODO: Term.Subst.fv

-- TODO: {Terminator, Region}.Subst.{fv, fl}

-- TODO: fv_subst, fv_vsubst

-- TODO: fl_lsubst

end Subst
