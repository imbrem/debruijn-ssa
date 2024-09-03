import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.CategoryTheory.PathCategory
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Discretion.Correspondence.Definitions

import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Effect.Subst
import DeBruijnSSA.BinSyntax.Syntax.Fv

namespace BinSyntax

variable {φ : Type u} {ε : Type v} [Φ: EffectSet φ ε] [SemilatticeSup ε] [OrderBot ε]

-- -- TODO: define as Subst.cons or smt...
-- def Term.subst₂ (a b: Term φ) : Subst φ
--   | 0 => a
--   | 1 => b
--   | n + 2 => Term.var n

namespace Region

open Term

-- TODO: StepD is effect monotonic

inductive CongD (P : Region φ → Region φ → Sort _) : Region φ → Region φ → Sort _
  | let1 (e) : CongD P r r' → CongD P (let1 e r) (let1 e r')
  | let2 (e) : CongD P r r' → CongD P (let2 e r) (let2 e r')
  | case_left (e) : CongD P r r' → (s : Region φ)
    → CongD P (case e r s) (case e r' s)
  | case_right (e r) : CongD P s s' → CongD P (case e r s) (case e r s')
  | cfg_entry
    : CongD P r r' → (n : _) → (G : _) → CongD P (cfg r n G) (cfg r' n G)
  | cfg_block (β n G i) : CongD P (G i) g' →
    CongD P (cfg β n G) (cfg β n (Function.update G i g'))
  | rel : P r r' → CongD P r r'

inductive Cong (P : Region φ → Region φ → Sort _) : Region φ → Region φ → Prop
  | let1 (e) : Cong P r r' → Cong P (let1 e r) (let1 e r')
  | let2 (e) : Cong P r r' → Cong P (let2 e r) (let2 e r')
  | case_left (e) : Cong P r r' → (s : Region φ)
    → Cong P (case e r s) (case e r' s)
  | case_right (e r) : Cong P s s' → Cong P (case e r s) (case e r s')
  | cfg_entry
    : Cong P r r' → (n : _) → (G : _) → Cong P (cfg r n G) (cfg r' n G)
  | cfg_block (β n G i) : Cong P (G i) g' → Cong P (cfg β n G) (cfg β n (Function.update G i g'))
  | rel : P r r' → Cong P r r'

theorem CongD.cong
  {P : Region φ → Region φ → Sort _} {r r' : Region φ} (p : CongD P r r')
    : Cong P r r'
  := by induction p with
    | rel p => apply Cong.rel; assumption
    | _ => constructor; assumption

def CongD.map {P : Region φ → Region φ → Sort _} {P' : Region φ → Region φ → Sort _}
  (f : ∀r r', P r r' → P' r r') {r r'} : CongD P r r' → CongD P' r r'
  | CongD.let1 e p => CongD.let1 e (map f p)
  | CongD.let2 e p => CongD.let2 e (map f p)
  | CongD.case_left e p s => CongD.case_left e (map f p) s
  | CongD.case_right e r p => CongD.case_right e r (map f p)
  | CongD.cfg_entry p n G => CongD.cfg_entry (map f p) n G
  | CongD.cfg_block β n G i p => CongD.cfg_block β n G i (map f p)
  | CongD.rel p => CongD.rel (f _ _ p)

theorem Cong.map {P P' : Region φ → Region φ → Sort _}
  (f : ∀r r', P r r' → P' r r') {r r'} (d : Cong P r r') : Cong P' r r'
  := by induction d with
  | rel p => exact Cong.rel (f _ _ p)
  | _ => constructor; assumption

theorem Cong.mono {P P' : Region φ → Region φ → Prop}
  (h : P ≤ P') {r r'} : Cong P r r' ≤ Cong P' r r'
  := λd => d.map h

theorem Cong.nonempty
  {P : Region φ → Region φ → Sort _} {r r' : Region φ} (p : Cong P r r')
    : Nonempty (CongD P r r')
  := by induction p with
    | rel p => constructor; apply CongD.rel; assumption
    | _ => constructor; constructor; apply Classical.choice; assumption

theorem Cong.of_nonempty
  {P : Region φ → Region φ → Sort _} {r r' : Region φ} (p : Nonempty (CongD P r r'))
    : Cong P r r'
  := let ⟨p⟩ := p; p.cong

theorem Cong.nonempty_iff
  {P : Region φ → Region φ → Sort _} {r r' : Region φ} : Cong P r r' ↔ Nonempty (CongD P r r')
  := ⟨Cong.nonempty, Cong.of_nonempty⟩

theorem Cong.eqv_let1 (e) {r r' : Region φ} (p : Relation.EqvGen (Cong P) r r')
  : Relation.EqvGen (Cong P) (r.let1 e) (r'.let1 e)
  := by induction p with
    | rel _ _ p => exact Relation.EqvGen.rel _ _ $ Cong.let1 _ p
    | symm _ _ _ I => exact I.symm _ _
    | refl => apply Relation.EqvGen.refl
    | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

theorem Cong.eqv_let2 (e) {r r' : Region φ} (p : Relation.EqvGen (Cong P) r r')
  : Relation.EqvGen (Cong P) (r.let2 e) (r'.let2 e)
  := by induction p with
    | rel _ _ p => exact Relation.EqvGen.rel _ _ $ Cong.let2 _ p
    | symm _ _ _ I => exact I.symm _ _
    | refl => apply Relation.EqvGen.refl
    | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

theorem Cong.eqv_case_left (e) {r r'} (p : Relation.EqvGen (Cong P) r r') (s)
  : Relation.EqvGen (Cong P) (case e r s) (case e r' s)
  := by induction p with
    | rel _ _ p => exact Relation.EqvGen.rel _ _ $ Cong.case_left _ p s
    | symm _ _ _ I => exact I.symm _ _
    | refl => apply Relation.EqvGen.refl
    | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

theorem Cong.eqv_case_right (e r) {s s'} (p : Relation.EqvGen (Cong P) s s')
  : Relation.EqvGen (Cong P) (case e r s) (case e r s')
  := by induction p with
    | rel _ _ p => exact Relation.EqvGen.rel _ _ $ Cong.case_right _ _ p
    | symm _ _ _ I => exact I.symm _ _
    | refl => apply Relation.EqvGen.refl
    | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

theorem Cong.eqv_case (e) {r r' s s'}
  (pr : Relation.EqvGen (Cong P) r r') (ps : Relation.EqvGen (Cong P) s s')
  : Relation.EqvGen (Cong P) (case e r s) (case e r' s')
  := Relation.EqvGen.trans _ _ _ (eqv_case_left e pr _) (eqv_case_right e _ ps)

theorem Cong.eqv_cfg_entry {r r'} (p : Relation.EqvGen (Cong P) r r') (n) (G)
  : Relation.EqvGen (Cong P) (cfg r n G) (cfg r' n G)
  := by induction p with
    | rel _ _ p => apply Relation.EqvGen.rel; apply Cong.cfg_entry; assumption
    | symm _ _ _ I => exact I.symm _ _
    | refl => apply Relation.EqvGen.refl
    | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

theorem Cong.eqv_cfg_block (β n G i) (p : Relation.EqvGen (Cong P) (G i) g')
  : Relation.EqvGen (Cong P) (cfg β n G) (cfg β n (Function.update G i g')) := by
  generalize hg : G i = g
  rw [hg] at p
  induction p generalizing G with
  | rel _ _ p =>
    cases hg
    apply Relation.EqvGen.rel
    apply Cong.cfg_block
    assumption
  | symm x y _ I =>
    apply Relation.EqvGen.symm
    have h : β.cfg n G = β.cfg n (Function.update (Function.update G i x) i y) := by cases hg; simp
    rw [h]
    apply I
    simp
  | refl =>
    cases hg
    rw [Function.update_eq_self]
    apply Relation.EqvGen.refl
  | trans x y z _ _ Il Ir =>
    apply Relation.EqvGen.trans
    apply Il _ hg
    have h : Function.update G i z = Function.update (Function.update G i y) i z := by simp
    rw [h]
    apply Ir
    simp

-- TODO: generalize partial update lemma in Discretion.Utils
-- TODO: only need to require i < k...
theorem Cong.eqv_cfg_blocks_partial (β n) (G G' : Fin n → Region φ)
  (p : ∀i, Relation.EqvGen (Cong P) (G i) (G' i)) (k : ℕ)
  : Relation.EqvGen (Cong P) (cfg β n G) (cfg β n (λi => if i < k then G' i else G i)) := by
  induction k with
  | zero => simp only [Nat.not_lt_zero, ↓reduceIte]; apply Relation.EqvGen.refl
  | succ k I =>
    apply Relation.EqvGen.trans
    apply I
    if h : k < n then
      have h' :
        (λi : Fin n => if i < k + 1 then G' i else G i)
        = Function.update (λi : Fin n => if i < k then G' i else G i) ⟨k, h⟩ (G' ⟨k, h⟩)
        := by funext i; split
              case isTrue h => cases h with
                | refl => simp
                | step h =>
                  have h := Nat.lt_of_succ_le h
                  rw [Function.update_noteq]
                  rw [ite_cond_eq_true]
                  simp [h]
                  simp only [ne_eq, Fin.ext_iff]
                  exact Nat.ne_of_lt h
              case isFalse h =>
                have h := Nat.lt_of_succ_le $ Nat.le_of_not_lt h
                rw [Function.update_noteq]
                rw [ite_cond_eq_false]
                simp [Nat.not_lt_of_lt h]
                simp only [ne_eq, Fin.ext_iff]
                exact Ne.symm $ Nat.ne_of_lt h
      rw [h']
      apply eqv_cfg_block
      simp only [lt_self_iff_false, ↓reduceIte]
      exact p ⟨k, h⟩
    else
      have h : ∀i : Fin n, i < k := λi => Nat.lt_of_lt_of_le i.prop (Nat.le_of_not_lt h)
      have h' : ∀i : Fin n, i < (k + 1) := λi => Nat.lt_succ_of_lt (h i)
      simp only [h, h', ↓reduceIte]
      apply Relation.EqvGen.refl

theorem Cong.eqv_cfg_blocks (β n) (G G' : Fin n → Region φ)
  (p : ∀i, Relation.EqvGen (Cong P) (G i) (G' i))
  : Relation.EqvGen (Cong P) (cfg β n G) (cfg β n G') := by
  have h : cfg β n G' = cfg β n (λi => if i < n then G' i else G i) := by simp
  rw [h]
  apply eqv_cfg_blocks_partial
  apply p

theorem Cong.eqv_cfg
  (pβ : Relation.EqvGen (Cong P) β β) (n) {G G' : Fin n → Region φ}
  (pG : ∀i : Fin n, Relation.EqvGen (Cong P) (G i) (G' i))
  : Relation.EqvGen (Cong P) (cfg β n G) (cfg β n G') := by
  apply Relation.EqvGen.trans
  apply eqv_cfg_entry
  assumption
  apply eqv_cfg_blocks
  assumption

def CongD.cast_trg {P : Region φ → Region φ → Sort _}
  {r₀ r₁ r₁' : Region φ} (p : CongD P r₀ r₁) (h : r₁ = r₁')
  : CongD P r₀ r₁' := h ▸ p

def CongD.cast_src {P : Region φ → Region φ → Sort _}
  {r₀ r₀' r₁ : Region φ} (h : r₀' = r₀) (p : CongD P r₀ r₁)
  : CongD P r₀' r₁ := h ▸ p

def CongD.cast {P : Region φ → Region φ → Sort _}
  {r₀ r₀' r₁ r₁' : Region φ} (h₀ : r₀ = r₀') (h₁ : r₁ = r₁')
  (p : CongD P r₀ r₁) : CongD P r₀' r₁' := h₁ ▸ h₀ ▸ p

def CongD.cfg_block' {P : Region φ → Region φ → Sort _}
  (β n G i) (p : CongD P g g')
  : CongD P (cfg β n (Function.update G i g)) (cfg β n (Function.update G i g'))
  := (CongD.cfg_block β n (Function.update G i g) i (by simp only [Function.update_same]; exact p)
    ).cast_trg (by simp)

def CongD.vwk {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (toVwk : ∀ρ r r', P r r' → P (r.vwk ρ) (r'.vwk ρ)) (ρ)
  : CongD P r r' → CongD P (r.vwk ρ) (r'.vwk ρ)
  | let1 e p => let1 (e.wk ρ) (p.vwk toVwk (Nat.liftWk ρ))
  | let2 e p => let2 (e.wk ρ) (p.vwk toVwk (Nat.liftnWk 2 ρ))
  | case_left e p s => case_left (e.wk ρ) (p.vwk toVwk (Nat.liftWk ρ)) (s.vwk (Nat.liftWk ρ))
  | case_right e r p => case_right (e.wk ρ) (r.vwk (Nat.liftWk ρ)) (p.vwk toVwk (Nat.liftWk ρ))
  | cfg_entry p n G => cfg_entry (p.vwk toVwk _) n _
  | cfg_block β n G i p => by
    simp only [Region.vwk, Function.comp_update_apply]
    exact cfg_block _ _ _ _ (p.vwk toVwk (Nat.liftWk ρ))
  | rel p => rel (toVwk ρ _ _ p)

theorem Cong.vwk {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (toVwk : ∀ρ r r', P r r' → P (r.vwk ρ) (r'.vwk ρ)) (ρ) (p : Cong P r r')
  : Cong P (r.vwk ρ) (r'.vwk ρ)
  := let ⟨d⟩ := p.nonempty; (d.vwk toVwk ρ).cong

theorem Cong.eqv_vwk {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (toVwk : ∀ρ r r', P r r' → P (r.vwk ρ) (r'.vwk ρ)) (ρ) (p : Relation.EqvGen (Cong P) r r')
  : Relation.EqvGen (Cong P) (r.vwk ρ) (r'.vwk ρ)
  := by induction p with
  | rel => apply Relation.EqvGen.rel; apply Cong.vwk <;> assumption
  | symm => apply Relation.EqvGen.symm; assumption
  | refl => apply Relation.EqvGen.refl
  | trans => apply Relation.EqvGen.trans <;> assumption

def CongD.lwk {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (toLwk : ∀ρ r r', P r r' → P (r.lwk ρ) (r'.lwk ρ)) (ρ)
  : CongD P r r' → CongD P (r.lwk ρ) (r'.lwk ρ)
  | let1 e p => let1 e (p.lwk toLwk ρ)
  | let2 e p => let2 e (p.lwk toLwk ρ)
  | case_left e p s => case_left e (p.lwk toLwk ρ) (s.lwk ρ)
  | case_right e r p => case_right e (r.lwk ρ) (p.lwk toLwk ρ)
  | cfg_entry p n G => cfg_entry (p.lwk toLwk _) n _
  | cfg_block β n G i p => by
    simp only [Region.lwk, Function.comp_update_apply]
    exact cfg_block _ _ _ _ (p.lwk toLwk _)
  | rel p => rel (toLwk ρ _ _ p)

theorem Cong.lwk {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (toLwk : ∀ρ r r', P r r' → P (r.lwk ρ) (r'.lwk ρ)) (ρ) (p : Cong P r r')
  : Cong P (r.lwk ρ) (r'.lwk ρ)
  := let ⟨d⟩ := p.nonempty; (d.lwk toLwk ρ).cong

theorem Cong.eqv_lwk {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (toLwk : ∀ρ r r', P r r' → P (r.lwk ρ) (r'.lwk ρ)) (ρ) (p : Relation.EqvGen (Cong P) r r')
  : Relation.EqvGen (Cong P) (r.lwk ρ) (r'.lwk ρ)
  := by induction p with
  | rel => apply Relation.EqvGen.rel; apply Cong.lwk <;> assumption
  | symm => apply Relation.EqvGen.symm; assumption
  | refl => apply Relation.EqvGen.refl
  | trans => apply Relation.EqvGen.trans <;> assumption

theorem Cong.fv_le {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (fvLe : ∀r r', P r r' → r.fv ≤ r'.fv)
  (p : Cong P r r') : r.fv ≤ r'.fv := by
  induction p with
  | rel p => exact (fvLe _ _ p)
  | cfg_block _ _ G i _ I =>
    simp only [fv, add_le_add_iff_left]
    apply Finset.sum_le_sum
    intro k _
    apply Multiset.liftnFv_mono
    if h : k = i then
      cases h
      simp [I]
    else
      simp [h]
  | _ =>
    simp only [fv, add_le_add_iff_right, add_le_add_iff_left, Multiset.liftFv, *] <;>
    apply Multiset.liftnFv_mono <;>
    assumption

theorem Cong.fv_eq {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (fvEq : ∀r r', P r r' → r.fv = r'.fv)
  (p : Cong P r r') : r.fv = r'.fv := by
  induction p with
  | rel p => exact (fvEq _ _ p)
  | cfg_block _ _ G _ _ I =>
    simp only [fv, add_right_inj, Function.comp_update_apply, <-I]
    congr
    funext k
    simp only [<-Function.comp_apply (f := Multiset.liftnFv 1)]
    simp only [<-Function.comp_apply (g := G)]
    rw [Function.comp.assoc]
    rw [Function.update_eq_self]
  | _ => simp [*]

theorem Cong.fvs_le {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (fvsLe : ∀r r', P r r' → r.fvs ⊆ r'.fvs)
  (p : Cong P r r') : r.fvs ⊆ r'.fvs := by
  induction p with
  | rel p => exact (fvsLe _ _ p)
  | let1 =>
    simp only [fvs, Set.union_subset_iff, Set.subset_union_left, true_and]
    apply Set.subset_union_of_subset_right
    apply Set.liftFv_mono
    assumption
  | let2 =>
    simp only [fvs, Set.union_subset_iff, Set.subset_union_left, true_and]
    apply Set.subset_union_of_subset_right
    apply Set.liftnFv_mono
    assumption
  | case_left =>
    simp only [fvs, Set.union_subset_iff, Set.subset_union_right, and_true]
    constructor
    apply Set.subset_union_of_subset_left
    apply Set.subset_union_of_subset_left
    rfl
    apply Set.subset_union_of_subset_left
    apply Set.subset_union_of_subset_right
    apply Set.liftFv_mono
    assumption
  | case_right =>
    simp only [fvs, Set.union_subset_iff, Set.subset_union_left, true_and]
    apply Set.subset_union_of_subset_right
    apply Set.liftFv_mono
    assumption
  | cfg_entry =>
    simp only [fvs, Set.union_subset_iff, Set.subset_union_right, and_true]
    apply Set.subset_union_of_subset_left
    assumption
  | cfg_block _ _ G i _ I =>
    simp only [fvs, Set.union_subset_iff, Set.subset_union_left, Set.iUnion_subset_iff, true_and]
    intro k
    apply Set.subset_union_of_subset_right
    apply Set.subset_iUnion_of_subset k
    apply Set.liftFv_mono
    if h : k = i then
      cases h
      simp [I]
    else
      simp only [ne_eq, h, not_false_eq_true, Function.update_noteq]
      apply le_refl

theorem Cong.fvs_eq {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (fvsEq : ∀r r', P r r' → r.fvs = r'.fvs)
  (p : Cong P r r') : r.fvs = r'.fvs := by
  induction p with
  | rel p => exact (fvsEq _ _ p)
  | cfg_block β _ G i _ I =>
    simp only [fvs]
    apply congrArg
    apply congrArg
    funext k
    if h : k = i then
      cases h
      simp [I]
    else
      simp [h]
  | _ => simp [*]

theorem Cong.fvi_le {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (fviLe : ∀r r', P r r' → r.fvi ≤ r'.fvi)
  (p : Cong P r r') : r.fvi ≤ r'.fvi := by
  induction p with
  | rel p => exact (fviLe _ _ p)
  | let1 =>
    apply max_le_max_left
    apply tsub_le_tsub_right
    assumption
  | let2 =>
    apply max_le_max_left
    apply tsub_le_tsub_right
    assumption
  | case_left =>
    apply max_le_max_left
    apply max_le_max <;>
    apply tsub_le_tsub_right <;>
    simp [*]
  | case_right =>
    apply max_le_max_left
    apply max_le_max <;>
    apply tsub_le_tsub_right <;>
    simp [*]
  | cfg_entry =>
    apply max_le_max_right
    assumption
  | cfg_block _ _ G i _ I =>
    apply max_le_max_left
    apply Finset.sup_le
    intro k hk
    apply Finset.le_sup_of_le hk
    apply tsub_le_tsub_right
    if h : k = i then
      cases h
      simp [I]
    else
      simp [h]

theorem Cong.fvi_eq {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (fviLe : ∀r r', P r r' → r.fvi = r'.fvi)
  (p : Cong P r r') : r.fvi = r'.fvi := by
  induction p with
  | rel p => exact (fviLe _ _ p)
  | cfg_block _ _ G i _ I =>
    simp only [fvi]
    congr
    funext k
    if h : k = i then
      cases h
      simp [I]
    else
      simp [h]
  | _ => simp [*]

theorem Cong.eqv_fv_eq {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (fvEq : ∀r r', P r r' → r.fv = r'.fv)
  (p : Relation.EqvGen (Cong P) r r') : r.fv = r'.fv := by
  induction p with
  | rel _ _ p => exact p.fv_eq fvEq
  | symm _ _ _ I => exact I.symm
  | refl => rfl
  | trans _ _ _ _ _ Il Ir => rw [Il, Ir]

theorem Cong.eqv_fvi_eq {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (fviEq : ∀r r', P r r' → r.fvi = r'.fvi)
  (p : Relation.EqvGen (Cong P) r r') : r.fvi = r'.fvi := by
  induction p with
  | rel _ _ p => exact p.fvi_eq fviEq
  | symm _ _ _ I => exact I.symm
  | refl => rfl
  | trans _ _ _ _ _ Il Ir => rw [Il, Ir]

theorem Cong.eqv_fvs_eq {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (fvsEq : ∀r r', P r r' → r.fvs = r'.fvs)
  (p : Relation.EqvGen (Cong P) r r') : r.fvs = r'.fvs := by
  induction p with
  | rel _ _ p => exact p.fvs_eq fvsEq
  | symm _ _ _ I => exact I.symm
  | refl => rfl
  | trans _ _ _ _ _ Il Ir => rw [Il, Ir]

-- TODO: CongD is effect monotone/antitone iff underlying is
-- ==> CongD is effect preserving iff underlying is

inductive BCongD (P : (ℕ → ε) → Region φ → Region φ → Type _)
  : (ℕ → ε) → Region φ → Region φ → Type _
  | rel : P Γ r r' → BCongD P Γ r r'
  | let1 (e) : BCongD P (Nat.liftBot Γ) r r' → BCongD P Γ (let1 e r) (let1 e r')
  | let2 (e) : BCongD P (Nat.liftnBot 2 Γ) r r' → BCongD P Γ (let2 e r) (let2 e r')
  | case_left (e) : BCongD P (Nat.liftBot Γ) r r' → (s : Region φ)
    → BCongD P Γ (case e r s) (case e r' s)
  | case_right (e r) : BCongD P (Nat.liftBot Γ) s s' → BCongD P Γ (case e r s) (case e r s')
  | cfg_entry
    : BCongD P Γ r r' → (n : _) → (G : _) → BCongD P Γ (cfg r n G) (cfg r' n G)
  | cfg_block (β n G i) : BCongD P (Nat.liftBot Γ) (G i) g' →
    BCongD P Γ (cfg β n G) (cfg β n (Function.update G i g'))

def BCongD.cast_src {P : (ℕ → ε) → Region φ → Region φ → Type _} {Γ : ℕ → ε}
  (h : r₀ = r₀') (p : BCongD P Γ r₀' r₁)
  : BCongD P Γ r₀ r₁ := h ▸ p

def BCongD.cast_trg {P : (ℕ → ε) → Region φ → Region φ → Type _} {Γ : ℕ → ε}
  (p : BCongD P Γ r₀ r₁) (h : r₁ = r₁')
  : BCongD P Γ r₀ r₁' := h ▸ p

def BCongD.cast {P : (ℕ → ε) → Region φ → Region φ → Type _} {Γ : ℕ → ε}
  (h₀ : r₀ = r₀') (h₁ : r₁ = r₁')
  (p : BCongD P Γ r₀' r₁') : BCongD P Γ r₀ r₁ := h₁ ▸ h₀ ▸ p

def BCongD.cfg_block' {P : (ℕ → ε) → Region φ → Region φ → Type _} {Γ : ℕ → ε}
  (β n G i) (p : BCongD P (Nat.liftBot Γ) g g')
  : BCongD P Γ (cfg β n (Function.update G i g)) (cfg β n (Function.update G i g'))
  := (BCongD.cfg_block β n (Function.update G i g) i (by simp only [Function.update_same]; exact p)
    ).cast_trg (by simp)

-- TODO: prefunctor lore

def CongD.let1_func {P : Region φ → Region φ → Type _} (e : Term φ)
  : Corr.Prefunctor (CongD P) (CongD P) where
  obj := Region.let1 e
  map := CongD.let1 e

def CongD.let2_func {P : Region φ → Region φ → Type _} (e : Term φ)
  : Corr.Prefunctor (CongD P) (CongD P) where
  obj := Region.let2 e
  map := CongD.let2 e

def CongD.case_left_func {P : Region φ → Region φ → Type _} (e : Term φ) (s : Region φ)
  : Corr.Prefunctor (CongD P) (CongD P) where
  obj := (Region.case e · s)
  map := (CongD.case_left e · s)

def CongD.case_right_func {P : Region φ → Region φ → Type _} (e : Term φ) (r : Region φ)
  : Corr.Prefunctor (CongD P) (CongD P) where
  obj := Region.case e r
  map := CongD.case_right e r

def CongD.cfg_entry_func {P : Region φ → Region φ → Type _} (n) (G : Fin n → Region φ)
  : Corr.Prefunctor (CongD P) (CongD P) where
  obj := (Region.cfg · n G)
  map := (CongD.cfg_entry · n G)

def CongD.cfg_block_func' {P : Region φ → Region φ → Type _}
  (β : Region φ) (n) (G : Fin n → Region φ) (i : Fin n)
  : Corr.Prefunctor (CongD P) (CongD P) where
  obj := λr => (Region.cfg β n (Function.update G i r))
  map := CongD.cfg_block' β n G i

def BCongD.let1_func {P : (ℕ → ε) → Region φ → Region φ → Type _} {Γ} (e : Term φ)
  : Corr.Prefunctor (BCongD P (Nat.liftBot Γ)) (BCongD P Γ) where
  obj := Region.let1 e
  map := BCongD.let1 e

def BCongD.let2_func {P : (ℕ → ε) → Region φ → Region φ → Type _} {Γ} (e : Term φ)
  : Corr.Prefunctor (BCongD P (Nat.liftnBot 2 Γ)) (BCongD P Γ) where
  obj := Region.let2 e
  map := BCongD.let2 e

def BCongD.case_left_func
  {P : (ℕ → ε) → Region φ → Region φ → Type _} {Γ} (e : Term φ) (s : Region φ)
  : Corr.Prefunctor (BCongD P (Nat.liftBot Γ)) (BCongD P Γ) where
  obj := (Region.case e · s)
  map := (BCongD.case_left e · s)

def BCongD.case_right_func {P : (ℕ → ε) → Region φ → Region φ → Type _} {Γ}
  (e : Term φ) (r : Region φ)
  : Corr.Prefunctor (BCongD P (Nat.liftBot Γ)) (BCongD P Γ) where
  obj := Region.case e r
  map := BCongD.case_right e r

def BCongD.cfg_entry_func {P : (ℕ → ε) → Region φ → Region φ → Type _} {Γ}
  (n) (G : Fin n → Region φ)
  : Corr.Prefunctor (BCongD P Γ) (BCongD P Γ) where
  obj := (Region.cfg · n G)
  map := (BCongD.cfg_entry · n G)

def BCongD.cfg_block_func' {P : (ℕ → ε) → Region φ → Region φ → Type _} {Γ}
  (β : Region φ) (n) (G : Fin n → Region φ) (i : Fin n)
  : Corr.Prefunctor (BCongD P (Nat.liftBot Γ)) (BCongD P Γ) where
  obj := λr => (Region.cfg β n (Function.update G i r))
  map := BCongD.cfg_block' β n G i
