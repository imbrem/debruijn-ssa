import Discretion.Wk.Nat
import Discretion.Wk.Fin
import Discretion.Wk.Multiset
import Discretion.Wk.Multiset

import DeBruijnSSA.BinSyntax.Syntax.Subst.Term
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

theorem Term.Subst.fvs_lift_def {σ : Term.Subst φ} {i}
  : σ.lift.fvs i = σ.lift.fvs i := rfl

theorem Term.Subst.fvs_liftn_def {σ : Term.Subst φ} {i n}
  : (σ.liftn n).fvs i = (σ.liftn n i).fvs := rfl

theorem Term.Subst.biUnion_fvs_lift {σ : Term.Subst φ} {s : Set ℕ}
  : ⋃i ∈ s, (σ.lift.fvs i).liftFv = ⋃i ∈ s.liftFv, σ.fvs i := by
  ext k
  simp only [Set.mem_iUnion, Set.mem_liftFv, exists_prop', nonempty_prop]
  constructor
  · intro ⟨i, hi, hk⟩
    cases i with
    | zero => simp [Subst.fvs] at hk
    | succ i =>
      simp only [fvs, lift_succ, fvs_wk, Nat.succ_eq_add_one, Set.mem_image, add_left_inj,
        exists_eq_right] at hk
      exact ⟨_, hi, hk⟩
  · intro ⟨i, hi, hk⟩
    exact ⟨i + 1, hi, by simp only [fvs, lift_succ, fvs_wk, Nat.succ_eq_add_one, Set.mem_image,
      add_left_inj, exists_eq_right]; exact hk⟩

theorem Term.Subst.biUnion_fvs_liftn {σ : Term.Subst φ} {s : Set ℕ}
  : ⋃i ∈ s, ((σ.liftn n).fvs i).liftnFv n = ⋃i ∈ s.liftnFv n, σ.fvs i := by
  induction n generalizing σ s with
  | zero => simp
  | succ n I =>
    rw [Set.liftnFv_succ', <-biUnion_fvs_lift]
    simp only [<-Set.liftFv_biUnion]
    rw [<-I]
    simp only [Set.liftFv_biUnion, <-Set.liftnFv_succ', Subst.liftn_succ']

theorem Term.fvs_subst (σ : Term.Subst φ) (t : Term φ) : (t.subst σ).fvs = ⋃ x ∈ t.fvs, σ.fvs x
  := by induction t generalizing σ with
  | pair a b Ia Ib => simp only [fvs, Set.biUnion_union, *]
  | let1 =>
    simp only [fvs, Set.biUnion_union, Set.liftnFv_iUnion, Subst.biUnion_fvs_lift, *]
  | let2 =>
    simp only [fvs, Set.biUnion_union, Set.liftnFv_iUnion, Subst.biUnion_fvs_liftn, *]
  | case =>
    simp only [
      fvs, Set.biUnion_union, Set.liftnFv_iUnion, Subst.biUnion_fvs_lift, Set.union_assoc, *
    ]
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
    simp only [
      fvs, Term.fvs_subst, Set.biUnion_union, Set.liftnFv_iUnion, Term.Subst.biUnion_fvs_lift, *
    ]
  | let2 =>
    simp only [
      fvs, Term.fvs_subst, Set.biUnion_union, Set.liftnFv_iUnion, Term.Subst.biUnion_fvs_liftn, *
    ]
  | case =>
    simp only [
      fvs, Term.fvs_subst, Set.biUnion_union, Set.liftnFv_iUnion, Term.Subst.biUnion_fvs_lift, *
    ]
  | cfg =>
    simp only [
      fvs, Set.biUnion_union, Set.biUnion_iUnion, Set.liftFv_biUnion, Term.Subst.biUnion_fvs_lift, *
    ]

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
  · rw [Set.union_comm]
  · simp

theorem Term.Subst.eqOn_lift_iff {σ σ' : Term.Subst φ} {s : Set ℕ}
  : s.EqOn σ.lift σ'.lift ↔ s.liftFv.EqOn σ σ' := by
  constructor <;> intro h n hn
  · rw [Set.mem_liftFv] at hn
    have h := h hn
    simp only [lift_succ] at h
    exact Term.wk0_injective h
  · cases n with | zero => rfl | _ => simp [Subst.lift, h ((Set.mem_liftFv _ _).mpr hn)]

theorem Term.Subst.eqOn_liftn_iff {σ σ' : Term.Subst φ} {s : Set ℕ}
  : s.EqOn (σ.liftn n) (σ'.liftn n) ↔ (s.liftnFv n).EqOn σ σ' := by
  induction n generalizing σ σ' s <;> simp [Subst.liftn_succ', Set.liftnFv_succ', eqOn_lift_iff, *]

theorem Term.subst_eq_iff {t : Term φ} {σ σ' : Subst φ}
  : t.subst σ = t.subst σ' ↔ t.fvs.EqOn σ σ' := by induction t generalizing σ σ' with
  | _ => simp [Subst.eqOn_lift_iff, Subst.eqOn_liftn_iff, and_assoc, *]

theorem Term.subst_eqOn_fvs_iff {t : Term φ} {σ σ' : Subst φ}
  : t.fvs.EqOn σ σ' ↔ t.subst σ = t.subst σ' := subst_eq_iff.symm

theorem Term.subst_eqOn_fvs {t : Term φ} {σ σ' : Subst φ}
  : t.fvs.EqOn σ σ' → t.subst σ = t.subst σ' := subst_eq_iff.mpr

theorem Term.subst_eqOn_fvi {t : Term φ} {σ σ' : Subst φ} (h : (Set.Iio t.fvi).EqOn σ σ')
  : t.subst σ = t.subst σ' := t.subst_eqOn_fvs (h.mono t.fvs_fvi)

theorem Region.vsubst_eq_iff {r : Region φ} {σ σ' : Term.Subst φ}
  : r.vsubst σ = r.vsubst σ' ↔ r.fvs.EqOn σ σ' := by induction r generalizing σ σ' with
  | _ => simp [
    Term.subst_eq_iff, and_assoc, Term.Subst.eqOn_lift_iff, Term.Subst.eqOn_liftn_iff,
    funext_iff, Set.eqOn_iUnion, *
  ]

theorem Region.vsubst_eqOn_fvs {r : Region φ} {σ σ' : Term.Subst φ} (h : r.fvs.EqOn σ σ')
  : r.vsubst σ = r.vsubst σ' := by induction r generalizing σ σ' with
  | br => simp [Term.subst_eqOn_fvs h]
  | let1 _ _ I =>
    simp only [vsubst, let1.injEq]
    constructor
    exact Term.subst_eqOn_fvs (h.mono (by simp))
    apply I
    rw [Term.Subst.eqOn_lift_iff]
    exact h.mono (by simp)
  | let2 _ _ I =>
    simp only [vsubst, let2.injEq]
    constructor
    exact Term.subst_eqOn_fvs (h.mono (by simp))
    apply I
    rw [Term.Subst.eqOn_liftn_iff]
    exact h.mono (by simp)
  | case _ _ _ Il Ir =>
    simp only [vsubst, case.injEq]
    constructor
    exact Term.subst_eqOn_fvs (h.mono (by simp [Set.union_assoc]))
    constructor
    apply Il
    rw [Term.Subst.eqOn_lift_iff]
    exact h.mono (by apply Set.subset_union_of_subset_left; simp)
    apply Ir
    rw [Term.Subst.eqOn_lift_iff]
    exact h.mono (by apply Set.subset_union_of_subset_right; simp)
  | cfg _ _ _ Iβ IG =>
    simp only [vsubst, cfg.injEq, heq_eq_eq, true_and]
    constructor
    exact Iβ (h.mono (by simp))
    ext k
    apply IG
    rw [Term.Subst.eqOn_lift_iff]
    apply h.mono
    apply Set.subset_union_of_subset_right
    apply Set.subset_iUnion_of_subset
    rfl

theorem Region.vsubst_eqOn_fvi {r : Region φ} {σ σ' : Term.Subst φ} (h : (Set.Iio r.fvi).EqOn σ σ')
  : r.vsubst σ = r.vsubst σ' := r.vsubst_eqOn_fvs (h.mono r.fvs_fvi)

-- theorem Region.lsubst_eqOn_fls {r : Region φ} {σ σ' : Subst φ} (h : r.fls.EqOn σ σ')
--   : r.lsubst σ = r.lsubst σ' := by sorry

-- TODO: {Terminator, Region}.Subst.{fv, fl}

-- TODO: fv_subst, fv_vsubst

-- TODO: fl_lsubst

end Subst
