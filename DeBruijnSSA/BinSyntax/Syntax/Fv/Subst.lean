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
  | pair a b Ia Ib => simp only [fvs, Set.biUnion_union, *]
  | _ => simp [Subst.fvs, *]

open Classical in
theorem Term.fvs_subst0 (t s : Term φ)
    : (t.subst s.subst0).fvs = t.fvs.liftFv ∪ (if 0 ∈ t.fvs then s.fvs else ∅) := by
  ext k
  simp only [
    fvs_subst, Set.mem_iUnion, exists_prop, Set.mem_union, Set.mem_ite_empty_right, Set.mem_liftFv]
  constructor
  intro ⟨i, hi, hk⟩
  cases i with
  | zero => exact Or.inr ⟨hi, hk⟩
  | succ i => exact Or.inl (hk ▸ hi)
  intro h
  cases h with
  | inl h => exact ⟨k + 1, h, rfl⟩
  | inr h => exact ⟨0, h⟩

theorem Term.fvs_subst0_le (t s : Term φ) : t.fvs.liftFv ⊆ (t.subst s.subst0).fvs
  := by rw [fvs_subst0]; apply Set.subset_union_left

theorem Region.fvs_vsubst (σ : Term.Subst φ) (r : Region φ)
  : (r.vsubst σ).fvs = ⋃ x ∈ r.fvs, σ.fvs x
  := by induction r generalizing σ with
  | br => simp [Term.fvs_subst]
  | let1 =>
    simp only [fvs, Term.fvs_subst, Set.biUnion_union, Set.liftnFv_iUnion, *]
    apply congrArg
    ext k
    simp only [Set.mem_iUnion, exists_prop]
    sorry
  | let2 => sorry
  | case => sorry
  | cfg => sorry

open Classical in
theorem Region.fvs_vsubst0 (t : Region φ) (s : Term φ)
    : (t.vsubst s.subst0).fvs = t.fvs.liftFv ∪ (if 0 ∈ t.fvs then s.fvs else ∅) := by
  ext k
  simp only [
    fvs_vsubst, Set.mem_iUnion, exists_prop, Set.mem_union, Set.mem_ite_empty_right, Set.mem_liftFv]
  constructor
  intro ⟨i, hi, hk⟩
  cases i with
  | zero => exact Or.inr ⟨hi, hk⟩
  | succ i => exact Or.inl (hk ▸ hi)
  intro h
  cases h with
  | inl h => exact ⟨k + 1, h, rfl⟩
  | inr h => exact ⟨0, h⟩

theorem Region.le_fvs_vsubst0 (t : Region φ) (s : Term φ) : t.fvs.liftFv ⊆ (t.vsubst s.subst0).fvs
  := by rw [fvs_vsubst0]; apply Set.subset_union_left

theorem Region.fvs_vsubst0_le (t : Region φ) (s : Term φ)
  : (t.vsubst s.subst0).fvs ⊆ s.fvs ∪ t.fvs.liftFv := by
  rw [fvs_vsubst0]
  split
  . rw [Set.union_comm]
  . simp


-- TODO: {Terminator, Region}.Subst.{fv, fl}

-- TODO: fv_subst, fv_vsubst

-- TODO: fl_lsubst

end Subst
