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

-- TODO: define as Subst.cons or smt...
def Term.subst₂ (a b: Term φ) : Subst φ
  | 0 => a
  | 1 => b
  | n + 2 => Term.var n

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

theorem Cong.eqv_let1 (e) {r r' : Region φ} (p : EqvGen (Cong P) r r')
  : EqvGen (Cong P) (r.let1 e) (r'.let1 e)
  := by induction p with
    | rel _ _ p => exact EqvGen.rel _ _ $ Cong.let1 _ p
    | symm _ _ _ I => exact I.symm _ _
    | refl => apply EqvGen.refl
    | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

theorem Cong.eqv_let2 (e) {r r' : Region φ} (p : EqvGen (Cong P) r r')
  : EqvGen (Cong P) (r.let2 e) (r'.let2 e)
  := by induction p with
    | rel _ _ p => exact EqvGen.rel _ _ $ Cong.let2 _ p
    | symm _ _ _ I => exact I.symm _ _
    | refl => apply EqvGen.refl
    | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

theorem Cong.eqv_case_left (e) {r r'} (p : EqvGen (Cong P) r r') (s)
  : EqvGen (Cong P) (case e r s) (case e r' s)
  := by induction p with
    | rel _ _ p => exact EqvGen.rel _ _ $ Cong.case_left _ p s
    | symm _ _ _ I => exact I.symm _ _
    | refl => apply EqvGen.refl
    | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

theorem Cong.eqv_case_right (e r) {s s'} (p : EqvGen (Cong P) s s')
  : EqvGen (Cong P) (case e r s) (case e r s')
  := by induction p with
    | rel _ _ p => exact EqvGen.rel _ _ $ Cong.case_right _ _ p
    | symm _ _ _ I => exact I.symm _ _
    | refl => apply EqvGen.refl
    | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

theorem Cong.eqv_case (e) {r r' s s'} (pr : EqvGen (Cong P) r r') (ps : EqvGen (Cong P) s s')
  : EqvGen (Cong P) (case e r s) (case e r' s')
  := EqvGen.trans _ _ _ (eqv_case_left e pr _) (eqv_case_right e _ ps)

theorem Cong.eqv_cfg_entry {r r'} (p : EqvGen (Cong P) r r') (n) (G)
  : EqvGen (Cong P) (cfg r n G) (cfg r' n G)
  := by induction p with
    | rel _ _ p => apply EqvGen.rel; apply Cong.cfg_entry; assumption
    | symm _ _ _ I => exact I.symm _ _
    | refl => apply EqvGen.refl
    | trans _ _ _ _ _ Il Ir => exact Il.trans _ _ _ Ir

theorem Cong.eqv_cfg_block (β n G i) (p : EqvGen (Cong P) (G i) g')
  : EqvGen (Cong P) (cfg β n G) (cfg β n (Function.update G i g')) := by
  generalize hg : G i = g
  rw [hg] at p
  induction p generalizing G with
  | rel _ _ p =>
    cases hg
    apply EqvGen.rel
    apply Cong.cfg_block
    assumption
  | symm x y _ I =>
    apply EqvGen.symm
    have h : β.cfg n G = β.cfg n (Function.update (Function.update G i x) i y) := by cases hg; simp
    rw [h]
    apply I
    simp
  | refl =>
    cases hg
    rw [Function.update_eq_self]
    apply EqvGen.refl
  | trans x y z _ _ Il Ir =>
    apply EqvGen.trans
    apply Il _ hg
    have h : Function.update G i z = Function.update (Function.update G i y) i z := by simp
    rw [h]
    apply Ir
    simp

-- TODO: generalize partial update lemma in Discretion.Utils
-- TODO: only need to require i < k...
theorem Cong.eqv_cfg_blocks_partial (β n) (G G' : Fin n → Region φ)
  (p : ∀i, EqvGen (Cong P) (G i) (G' i)) (k : ℕ)
  : EqvGen (Cong P) (cfg β n G) (cfg β n (λi => if i < k then G' i else G i)) := by
  induction k with
  | zero => simp only [Nat.not_lt_zero, ↓reduceIte]; apply EqvGen.refl
  | succ k I =>
    apply EqvGen.trans
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
      apply EqvGen.refl

theorem Cong.eqv_cfg_blocks (β n) (G G' : Fin n → Region φ)
  (p : ∀i, EqvGen (Cong P) (G i) (G' i))
  : EqvGen (Cong P) (cfg β n G) (cfg β n G') := by
  have h : cfg β n G' = cfg β n (λi => if i < n then G' i else G i) := by simp
  rw [h]
  apply eqv_cfg_blocks_partial
  apply p

theorem Cong.eqv_cfg
  (pβ : EqvGen (Cong P) β β) (n) {G G' : Fin n → Region φ}
  (pG : ∀i : Fin n, EqvGen (Cong P) (G i) (G' i))
  : EqvGen (Cong P) (cfg β n G) (cfg β n G') := by
  apply EqvGen.trans
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
  (toVwk : ∀ρ r r', P r r' → P (r.vwk ρ) (r'.vwk ρ)) (ρ) (p : EqvGen (Cong P) r r')
  : EqvGen (Cong P) (r.vwk ρ) (r'.vwk ρ)
  := by induction p with
  | rel => apply EqvGen.rel; apply Cong.vwk <;> assumption
  | symm => apply EqvGen.symm; assumption
  | refl => apply EqvGen.refl
  | trans => apply EqvGen.trans <;> assumption

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
  (p : EqvGen (Cong P) r r') : r.fv = r'.fv := by
  induction p with
  | rel _ _ p => exact p.fv_eq fvEq
  | symm _ _ _ I => exact I.symm
  | refl => rfl
  | trans _ _ _ _ _ Il Ir => rw [Il, Ir]

theorem Cong.eqv_fvi_eq {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (fviEq : ∀r r', P r r' → r.fvi = r'.fvi)
  (p : EqvGen (Cong P) r r') : r.fvi = r'.fvi := by
  induction p with
  | rel _ _ p => exact p.fvi_eq fviEq
  | symm _ _ _ I => exact I.symm
  | refl => rfl
  | trans _ _ _ _ _ Il Ir => rw [Il, Ir]

theorem Cong.eqv_fvs_eq {P : Region φ → Region φ → Sort _} {r r' : Region φ}
  (fvsEq : ∀r r', P r r' → r.fvs = r'.fvs)
  (p : EqvGen (Cong P) r r') : r.fvs = r'.fvs := by
  induction p with
  | rel _ _ p => exact p.fvs_eq fvsEq
  | symm _ _ _ I => exact I.symm
  | refl => rfl
  | trans _ _ _ _ _ Il Ir => rw [Il, Ir]

-- TODO: CongD is effect monotone/antitone iff underlying is
-- ==> CongD is effect preserving iff underlying is

-- TODO: make these rewrites bidirectional

inductive RewriteD : Region φ → Region φ → Type _
  | let1_op (f e r) :
    RewriteD (let1 (op f e) r) (let1 e $ let1 (op f (var 0)) $ r.vwk1)
  | let1_pair (a b r) :
    RewriteD (let1 (pair a b) r)
    (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) $ r.vwk1.vwk1)
  | let1_inl (e r) :
    RewriteD (let1 (inl e) r) (let1 e $ let1 (inl (var 0)) $ r.vwk1)
  | let1_inr (e r) :
    RewriteD (let1 (inr e) r) (let1 e $ let1 (inr (var 0)) $ r.vwk1)
  | let1_abort (e r) :
    RewriteD (let1 (abort e) r) (let1 e $ let1 (abort (var 0)) $ r.vwk1)
  | let2_op (f e r) :
    RewriteD (let2 (op f e) r) (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  | let2_pair (a b r) : RewriteD (let2 (pair a b) r) (let1 a $ let1 (b.wk Nat.succ) $ r)
  | let2_abort (e r) :
    RewriteD (let2 (abort e) r) (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  | case_op (f e r s) :
    RewriteD (case (op f e) r s)
      (let1 e $ case (op f (var 0))
      (r.vwk1)
      (s.vwk1))
  | case_abort (e r s) :
    RewriteD (case (abort e) r s)
      (let1 e $ case (abort (var 0))
      (r.vwk1)
      (s.vwk1))
  | let1_case (a b r s) :
    RewriteD (let1 a $ case (b.wk Nat.succ) r s)
    (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
  | let2_case (a b r s) :
    RewriteD (let2 a $ case (b.wk (· + 2)) r s)
    (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
  | cfg_br_lt (ℓ e n G) (h : ℓ < n) :
    RewriteD (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).let1 e) n G)
  | cfg_let1 (a β n G) :
    RewriteD (cfg (let1 a β) n G) (let1 a $ cfg β n (vwk1 ∘ G))
  | cfg_let2 (a β n G) :
    RewriteD (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk1 ∘ vwk1 ∘ G))
  | cfg_case (e r s n G) :
    RewriteD (cfg (case e r s) n G)
      (case e (cfg r n (vwk1 ∘ G)) (cfg s n (vwk1 ∘ G)))
  | cfg_cfg (β n G n' G') :
    RewriteD (cfg (cfg β n G) n' G') (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
  | cfg_zero (β G) : RewriteD (cfg β 0 G) β
  | cfg_fuse (β n G k) (ρ : Fin k → Fin n) (hρ : Function.Surjective ρ) :
    RewriteD
      (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
      (cfg β k (G ∘ ρ))
  | let2_eta (e) (r : Region φ) :
    RewriteD (let2 e (let1 ((Term.var 1).pair (Term.var 0)) r.vwk1.vwk1))
      (let1 e r)

def RewriteD.cast_src {r₀ r₀' r₁ : Region φ} (h : r₀ = r₀') (p : RewriteD r₀ r₁)
  : RewriteD r₀' r₁ := h ▸ p

def RewriteD.cast_trg {r₀ r₁ r₁' : Region φ} (p : RewriteD r₀ r₁) (h : r₁ = r₁')
  : RewriteD r₀ r₁' := h ▸ p

def RewriteD.cast {r₀ r₀' r₁ r₁' : Region φ} (h₀ : r₀ = r₀') (h₁ : r₁ = r₁')
  (p : RewriteD r₀ r₁) : RewriteD r₀' r₁' := h₁ ▸ h₀ ▸ p

theorem RewriteD.effect {Γ : ℕ → ε} {r r' : Region φ} (p : RewriteD r r') : r.effect Γ = r'.effect Γ := by
  cases p with
  | let1_op =>
    simp only [Region.effect, Term.effect, Nat.liftBot_zero, ge_iff_le, bot_le, sup_of_le_left]
    rw [<-sup_assoc]
    apply congr
    rw [sup_comm]
    rw [vwk1, effect_vwk, Nat.liftBot_comp_liftWk]
    rfl
  | let2_op =>
    simp only [Region.effect, Term.effect, Nat.liftBot, ge_iff_le, bot_le, sup_of_le_left,
      effect_liftnBot_vwk_liftnWk, Nat.liftBot_comp_succ]
    rw [<-sup_assoc]
    simp only [sup_comm]
  | let2_pair => simp [Nat.liftBot, sup_assoc, Nat.liftnBot_iterate]
  | let2_abort =>
    simp [Nat.liftnBot_iterate, Nat.liftBot, Nat.liftnWk_two,
      Region.effect_liftBot_vwk_liftWk, Nat.liftBot_comp_liftWk]
  | case_op =>
    simp only [Region.effect, Term.effect, Nat.liftBot, ge_iff_le, bot_le, sup_of_le_left,
      effect_liftBot2_vwk1]
    rw [<-sup_assoc, <-sup_assoc]
    simp only [sup_comm]
  | case_abort => simp [Nat.liftBot, effect_liftBot2_vwk1, sup_assoc]
  | let1_case a b r s =>
    simp only [Region.effect, Term.effect, Term.effect_liftBot_wk_succ]
    have h : ∀x y z w : ε, x ⊔ (y ⊔ z) ⊔ (y ⊔ w) = y ⊔ (x ⊔ z ⊔ w) := by
      intro x y z w
      rw [
        sup_assoc, sup_assoc, sup_assoc, sup_comm, sup_comm z, <-sup_assoc, <-sup_assoc, sup_idem,
        sup_assoc y, sup_assoc y]
      apply congrArg
      simp only [sup_assoc, sup_comm]
    rw [h]
  | let2_case =>
    simp only [Region.effect, Term.effect, Term.effect_liftBot_wk_succ, Term.effect_liftnBot_wk_add]
    have h : ∀x y z w : ε, x ⊔ (y ⊔ z) ⊔ (y ⊔ w) = y ⊔ (x ⊔ z ⊔ w) := by
      intro x y z w
      rw [
        sup_assoc, sup_assoc, sup_assoc, sup_comm, sup_comm z, <-sup_assoc, <-sup_assoc, sup_idem,
        sup_assoc y, sup_assoc y]
      apply congrArg
      simp only [sup_assoc, sup_comm]
    rw [h]
    simp [Nat.liftnBot_two]
  | cfg_br_lt ℓ e n G h =>
    simp only [Region.effect, Term.effect, Term.effect_liftBot_wk_succ, Term.effect_liftnBot_wk_add]
    rw [sup_assoc]
    apply congrArg
    rw [sup_of_le_right]
    exact Fin.elem_le_sup (λi => (G i).effect (Nat.liftBot Γ)) ⟨ℓ, h⟩
  | cfg_let2 =>
    simp only [Region.effect, Term.effect, Term.effect_liftBot_wk_succ, Term.effect_liftnBot_wk_add]
    rw [sup_assoc]
    apply congrArg
    apply congrArg
    apply congrArg
    funext i
    simp [Nat.liftnBot_two]
  | cfg_case => simp [sup_assoc]
  | cfg_cfg =>
    simp only [effect_cfg, sup_assoc]
    apply congrArg
    rw [Fin.comp_addCases, Fin.sup_addCases]
    apply congrArg
    apply congrArg
    funext i
    simp [Region.effect_lwk]
  | cfg_fuse β n G k ρ hρ =>
    simp only [effect_cfg, effect_lwk, <-Function.comp.assoc, effect_comp_lwk]
    apply congrArg
    rw [Fin.sup_comp_surj _ hρ]
  | let2_eta =>
    simp only [Region.effect, Term.effect, Nat.liftnBot, Nat.lt_succ_self, ↓reduceIte,
      Nat.zero_lt_succ, ge_iff_le, le_refl, sup_of_le_left, vwk1, effect_vwk, bot_le,
      sup_of_le_right]
    congr
    funext k
    cases k <;> rfl
  | _ => simp [Nat.liftBot, sup_assoc]

inductive Rewrite : Region φ → Region φ → Prop
  | let1_op (f e r) :
    Rewrite (let1 (op f e) r) (let1 e $ let1 (op f (var 0)) $ r.vwk1)
  | let1_pair (a b r) :
    Rewrite (let1 (pair a b) r)
    (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) $ r.vwk1.vwk1)
  | let1_inl (e r) :
    Rewrite (let1 (inl e) r) (let1 e $ let1 (inl (var 0)) $ r.vwk1)
  | let1_inr (e r) :
    Rewrite (let1 (inr e) r) (let1 e $ let1 (inr (var 0)) $ r.vwk1)
  | let1_abort (e r) :
    Rewrite (let1 (abort e) r) (let1 e $ let1 (abort (var 0)) $ r.vwk1)
  | let2_op (f e r) :
    Rewrite (let2 (op f e) r) (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  | let2_pair (a b r) : Rewrite (let2 (pair a b) r) (let1 a $ let1 (b.wk Nat.succ) $ r)
  | let2_abort (e r) :
    Rewrite (let2 (abort e) r) (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  | case_op (f e r s) :
    Rewrite (case (op f e) r s)
      (let1 e $ case (op f (var 0))
      (r.vwk1)
      (s.vwk1))
  | case_abort (e r s) :
    Rewrite (case (abort e) r s)
      (let1 e $ case (abort (var 0))
      (r.vwk1)
      (s.vwk1))
  | let1_case (a b r s) :
    Rewrite (let1 a $ case (b.wk Nat.succ) r s)
    (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
  | let2_case (a b r s) :
    Rewrite (let2 a $ case (b.wk (· + 2)) r s)
    (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
  | cfg_br_lt (ℓ e n G) (h : ℓ < n) :
    Rewrite (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).let1 e) n G)
  | cfg_let1 (a β n G) :
    Rewrite (cfg (let1 a β) n G) (let1 a $ cfg β n (vwk1 ∘ G))
  | cfg_let2 (a β n G) :
    Rewrite (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk1 ∘ vwk1 ∘ G))
  | cfg_case (e r s n G) :
    Rewrite (cfg (case e r s) n G)
      (case e (cfg r n (vwk1 ∘ G)) (cfg s n (vwk1 ∘ G)))
  | cfg_cfg (β n G n' G') :
    Rewrite (cfg (cfg β n G) n' G') (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
  | cfg_zero (β G) : Rewrite (cfg β 0 G) β
  | cfg_fuse (β n G k) (ρ : Fin k → Fin n) (hρ : Function.Surjective ρ) :
    Rewrite
      (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
      (cfg β k (G ∘ ρ))
  | let2_eta (e) (r : Region φ) :
    Rewrite (let2 e (let1 ((Term.var 1).pair (Term.var 0)) r.vwk1.vwk1))
      (let1 e r)

theorem RewriteD.rewrite {r r' : Region φ} (p : RewriteD r r') : Rewrite r r'
  := by cases p <;> constructor; assumption

-- TODO: make a def...
theorem Rewrite.nonempty {r r' : Region φ} (p : Rewrite r r') : Nonempty (RewriteD r r')
  := by cases p <;> constructor <;> constructor; assumption

theorem Rewrite.of_nonempty {r r' : Region φ} (p : Nonempty (RewriteD r r')) : Rewrite r r'
  := let ⟨p⟩ := p; p.rewrite

theorem Rewrite.nonempty_iff {r r' : Region φ} : Rewrite r r' ↔ Nonempty (RewriteD r r')
  := ⟨nonempty, of_nonempty⟩

theorem Rewrite.fvs_eq {r r' : Region φ} (p : Rewrite r r') : r.fvs = r'.fvs := by cases p with
  | let2_pair =>
    simp only [fvs, Term.fvs, Set.union_assoc, fvs_wk, Nat.succ_eq_add_one,
      Set.liftnFv_of_union, Set.liftnFv_map_add]
    rw [Set.liftnFv_succ]
  | let1_case a b r s =>
    simp only [fvs, fvs_wk, Nat.succ_eq_add_one, Set.liftnFv_of_union, Set.liftnFv_map_add,
      <-Set.union_assoc]
    rw [Set.union_comm a.fvs]
    simp only [Set.union_assoc (b.fvs ∪ a.fvs)]
    rw [Set.union_comm (Set.liftnFv 1 _) a.fvs]
    simp only [<-Set.union_assoc (b.fvs ∪ a.fvs)]
    rw [Set.union_assoc b.fvs a.fvs a.fvs, Set.union_self]
  | let2_case a b r s =>
    simp only [fvs, fvs_wk, Set.liftnFv_of_union, Set.liftnFv_map_add, Nat.succ_eq_add_one,
      <-Set.union_assoc]
    rw [Set.union_comm a.fvs]
    simp only [Set.union_assoc (b.fvs ∪ a.fvs)]
    rw [Set.union_comm (Set.liftnFv 1 _) a.fvs]
    simp only [<-Set.union_assoc (b.fvs ∪ a.fvs)]
    rw [Set.union_assoc b.fvs a.fvs a.fvs, Set.union_self]
    congr
    rw [Set.liftnFv_succ, Set.liftnFv_one, Set.liftnFv_succ']
    rw [Set.liftnFv_succ, Set.liftnFv_one, Set.liftnFv_succ']
  | cfg_br_lt ℓ e n G h =>
    simp only [fvs]
    rw [Set.union_assoc]
    congr
    apply Eq.symm
    apply Set.union_eq_self_of_subset_left
    apply Set.subset_iUnion_of_subset ⟨ℓ, h⟩
    rfl
  | cfg_case e r s G =>
    simp only [fvs, Set.union_assoc, Function.comp_apply, fvs_vwk1, Set.liftFv_map_liftWk,
      Nat.succ_eq_add_one, Set.map_add_liftnFv, Set.liftnFv_of_union, Set.liftnFv_iUnion,
      Set.liftnFv_of_inter, le_refl, Set.liftnFv_Ici, Set.inter_univ]
    apply congrArg
    apply congrArg
    rw [Set.union_comm (s.fvs.liftnFv 1), <-Set.union_assoc, Set.union_self]
  | cfg_cfg => simp [fvs, Set.union_assoc, Fin.comp_addCases_apply, Set.iUnion_addCases]
  | cfg_fuse β n G k ρ hρ =>
    simp only [fvs, fvs_lwk]
    rw [Set.iUnion_congr_of_surjective _ hρ]
    intro i
    simp
  | let2_eta =>
    simp only [fvs, Term.fvs, Set.union_singleton, fvs_vwk1, Set.liftFv_map_liftWk,
      Nat.succ_eq_add_one, Set.map_add_liftnFv, Set.liftnFv_of_union, Nat.ofNat_pos,
      Set.liftnFv_insert_lt, Nat.one_lt_ofNat, Set.liftnFv_singleton_lt, Set.empty_union]
    congr
    ext k
    rw [Set.mem_liftnFv, Set.mem_liftFv]
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_Ici, le_add_iff_nonneg_left, zero_le,
      and_true]
    constructor
    intro ⟨x, hx, hx'⟩
    cases x with
    | zero => cases hx'
    | succ x =>
      cases hx'
      exact hx
    intro hk
    exact ⟨k + 1, hk, rfl⟩
  | _ => simp [fvs_vwk, fvs_vwk1, Term.fvs_wk, Set.liftnFv_iUnion, Set.union_assoc]

instance instSetoid : Setoid (Region φ) := EqvGen.Setoid (Cong Rewrite)

theorem eqv_let1 (e) (p : r ≈ r') : @let1 φ e r ≈ let1 e r'
  := Cong.eqv_let1 e p

theorem eqv_let2 (e) (p : r ≈ r') : @let2 φ e r ≈ let2 e r'
  := Cong.eqv_let2 e p

theorem eqv_case_left (e) (p : r ≈ r') (s) : @case φ e r s ≈ case e r' s
  := Cong.eqv_case_left e p s

theorem eqv_case_right (e r) (p : s ≈ s') : @case φ e r s ≈ case e r s'
  := Cong.eqv_case_right e r p

theorem eqv_case (e) (pr : r ≈ r') (ps : s ≈ s') : @case φ e r s ≈ case e r' s'
  := Cong.eqv_case e pr ps

theorem eqv_cfg_entry (p : r ≈ r') (n) (G) : @cfg φ r n G ≈ cfg r' n G
  := Cong.eqv_cfg_entry p n G

theorem eqv_cfg_block (β n G i) (p : G i ≈ g')
  : @cfg φ β n G ≈ cfg β n (Function.update G i g')
  := Cong.eqv_cfg_block β n G i p

theorem eqv_cfg_blocks (β n G G') (p : G ≈ G')
  : @cfg φ β n G ≈ cfg β n G'
  := Cong.eqv_cfg_blocks β n G G' p

theorem eqv_cfg (pβ : β ≈ β) (n) {G G' : Fin n → Region φ} (pG : G ≈ G')
  : @cfg φ β n G ≈ cfg β n G'
  := Cong.eqv_cfg pβ n pG

theorem eqv_let1_op {f e r} : @let1 φ (op f e) r ≈ (let1 e $ let1 (op f (var 0)) $ r.vwk1)
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.let1_op f e r

theorem eqv_let1_pair {a b r}
  : @let1 φ (pair a b) r ≈ (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) $ r.vwk1.vwk1)
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.let1_pair a b r

theorem eqv_let1_inl {e r} : @let1 φ (inl e) r ≈ (let1 e $ let1 (inl (var 0)) $ r.vwk1)
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.let1_inl e r

theorem eqv_let1_inr {e r} : @let1 φ (inr e) r ≈ (let1 e $ let1 (inr (var 0)) $ r.vwk1)
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.let1_inr e r

theorem eqv_let1_abort {e r} : @let1 φ (abort e) r ≈ (let1 e $ let1 (abort (var 0)) $ r.vwk1)
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.let1_abort e r

theorem eqv_let2_op {f e r}
  : @let2 φ (op f e) r ≈ (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.let2_op f e r

theorem eqv_let2_pair {a b r}
  : @let2 φ (pair a b) r ≈ (let1 a $ let1 (b.wk Nat.succ) $ r)
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.let2_pair a b r

theorem eqv_let2_abort {e r}
  : @let2 φ (abort e) r ≈ (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.let2_abort e r

theorem eqv_case_op {f e r s}
  : @case φ (op f e) r s ≈ (let1 e $ case (op f (var 0)) (r.vwk1) (s.vwk1))
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.case_op f e r s

theorem eqv_case_abort {e r s}
  : @case φ (abort e) r s ≈ (let1 e $ case (abort (var 0)) (r.vwk1) (s.vwk1))
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.case_abort e r s

theorem eqv_let1_case {a b r s}
  : (@let1 φ a $ case (b.wk Nat.succ) r s)
  ≈ case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s)
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.let1_case a b r s

theorem eqv_let2_case {a b r s}
  : (@let2 φ a $ case (b.wk (· + 2)) r s)
  ≈ case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s)
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.let2_case a b r s

theorem eqv_cfg_br_lt {ℓ e n G} (h : ℓ < n)
  : @cfg φ (br ℓ e) n G ≈ cfg ((G ⟨ℓ, h⟩).let1 e) n G
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.cfg_br_lt ℓ e n G h

theorem eqv_cfg_let1 {a β n G}
  : @cfg φ (let1 a β) n G ≈ (let1 a $ cfg β n (vwk1 ∘ G))
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.cfg_let1 a β n G

theorem eqv_cfg_let2 {a β n G}
  : @cfg φ (let2 a β) n G ≈ (let2 a $ cfg β n (vwk1 ∘ vwk1 ∘ G))
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.cfg_let2 a β n G

theorem eqv_cfg_case {e r s n G}
  : @cfg φ (case e r s) n G
    ≈ case e (cfg r n (vwk1 ∘ G)) (cfg s n (vwk1 ∘ G))
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.cfg_case e r s n G

theorem eqv_cfg_cfg {β n G n' G'}
  : @cfg φ (cfg β n G) n' G' ≈ cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G'))
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.cfg_cfg β n G n' G'

theorem eqv_cfg_fuse {β n G k} (ρ : Fin k → Fin n) (hρ : Function.Surjective ρ)
  : @cfg φ (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G)
    ≈ cfg β k (G ∘ ρ)
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.cfg_fuse β n G k ρ hρ

theorem eqv_let2_eta {e} {r : Region φ}
  : @let2 φ e (let1 ((Term.var 1).pair (Term.var 0)) r.vwk1.vwk1)
    ≈ let1 e r
  := EqvGen.rel _ _ $ Cong.rel $ Rewrite.let2_eta e r

def RewriteD.vwk {r r' : Region φ} (ρ : ℕ → ℕ) (d : RewriteD r r') : RewriteD (r.vwk ρ) (r'.vwk ρ)
  := by cases d with
  | let2_pair a b r =>
    simp only [
      Region.vwk, wk, Nat.liftWk, vwk_liftWk₂_vwk1, wk_liftWk_wk_succ, Nat.liftnWk_two]
    constructor
  | cfg_cfg β n G n' G' =>
    simp only [Region.vwk, wk, Fin.comp_addCases_apply]
    rw [<-Function.comp.assoc, Region.vwk_comp_lwk, Function.comp.assoc]
    constructor
  | cfg_fuse β n G k σ hσ =>
    simp only [Region.vwk, Region.vwk_lwk, Function.comp_apply]
    constructor
    assumption
  | let2_eta e r =>
    simp only [Region.vwk, wk, Nat.liftnWk, Nat.lt_succ_self, ↓reduceIte, Nat.zero_lt_succ,
      Nat.liftWk_comm_liftnWk_apply, vwk_liftnWk₂_vwk1, vwk_liftWk₂_vwk1]
    constructor
  | _ =>
    simp only [
      Region.vwk, wk, Nat.liftWk,
      vwk_liftWk₂_vwk1, wk_liftWk_wk_succ, vwk_liftnWk₂_liftWk_vwk2, vwk_liftnWk₂_vwk1,
      wk_liftnWk_wk_add, Nat.liftWk_comm_liftnWk_apply, Function.comp_apply]
    constructor

theorem Rewrite.vwk {r r' : Region φ} (ρ : ℕ → ℕ) (p : Rewrite r r') : Rewrite (r.vwk ρ) (r'.vwk ρ)
  := let ⟨d⟩ := p.nonempty; (d.vwk ρ).rewrite

theorem eqv_vwk {r r' : Region φ} (ρ : ℕ → ℕ) (p : r ≈ r') : r.vwk ρ ≈ r'.vwk ρ
  := Cong.eqv_vwk (λρ _ _ p => p.vwk ρ) ρ p

-- That is, weakenings induce a prefunctor

-- TODO: RewriteD.lwk

-- TODO: Rewrite.lwk

-- That is, label weakenings induce a prefunctor

-- TODO: eqv_lwk

inductive ReduceD : Region φ → Region φ → Type _
  | case_inl (e r s) : ReduceD (case (inl e) r s) (let1 e r)
  | case_inr (e r s) : ReduceD (case (inr e) r s) (let1 e s)
  | wk_cfg (β n G k) (ρ : Fin k → Fin n) :
    ReduceD
      (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
      (cfg β k (G ∘ ρ))
  | dead_cfg_left (β n G m G') :
    ReduceD
      (cfg (β.lwk (· + n)) (n + m) (Fin.addCases G (lwk (· + n) ∘ G')))
      (cfg β m G')

inductive Reduce : Region φ → Region φ → Prop
  | case_inl (e r s) : Reduce (case (inl e) r s) (let1 e r)
  | case_inr (e r s) : Reduce (case (inr e) r s) (let1 e s)
  | wk_cfg (β n G k) (ρ : Fin k → Fin n) :
    Reduce
      (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
      (cfg β k (G ∘ ρ))
  | dead_cfg_left (β n G m G') :
    Reduce
      (cfg (β.lwk (· + n)) (n + m) (Fin.addCases G (lwk (· + n) ∘ G')))
      (cfg β m G')

theorem ReduceD.reduce {r r' : Region φ} (p : ReduceD r r') : Reduce r r'
  := by cases p <;> constructor

theorem Reduce.nonempty {r r' : Region φ} (p : Reduce r r') : Nonempty (ReduceD r r')
  := by cases p <;> constructor <;> constructor

theorem Reduce.of_nonempty {r r' : Region φ} (p : Nonempty (ReduceD r r')) : Reduce r r'
  := let ⟨p⟩ := p; p.reduce

theorem Reduce.nonempty_iff {r r' : Region φ} : Reduce r r' ↔ Nonempty (ReduceD r r')
  := ⟨Reduce.nonempty, Reduce.of_nonempty⟩

theorem Reduce.fvs_le {r r' : Region φ} (p : Reduce r r') : r'.fvs ⊆ r.fvs := by cases p with
  | case_inl e r s => simp
  | case_inr e r s =>
    simp only [fvs, Term.fvs, Set.union_subset_iff, Set.subset_union_right, and_true]
    rw [Set.union_assoc]
    simp
  | wk_cfg β n G k ρ =>
    simp only [fvs, Function.comp_apply, fvs_lwk, Set.union_subset_iff, Set.subset_union_left,
      Set.iUnion_subset_iff, true_and]
    intro i
    apply Set.subset_union_of_subset_right
    apply Set.subset_iUnion_of_subset (ρ i)
    rfl
  | dead_cfg_left β n G m G' =>
    simp only [fvs, fvs_lwk, Fin.comp_addCases_apply, Set.iUnion_addCases, Function.comp_apply]
    apply Set.union_subset_union_right
    apply Set.subset_union_right

def ReduceD.cast_trg {r₀ r₁ r₁' : Region φ} (p : ReduceD r₀ r₁) (h : r₁ = r₁')
  : ReduceD r₀ r₁' := h ▸ p

def ReduceD.cast_src {r₀ r₀' r₁ : Region φ} (h : r₀' = r₀) (p : ReduceD r₀ r₁)
  : ReduceD r₀' r₁ := h ▸ p

def ReduceD.cast {r₀ r₀' r₁ r₁' : Region φ} (h₀ : r₀ = r₀') (h₁ : r₁ = r₁')
  (p : ReduceD r₀ r₁) : ReduceD r₀' r₁' := h₁ ▸ h₀ ▸ p

def ReduceD.vwk {r r' : Region φ} (ρ : ℕ → ℕ) (d : ReduceD r r') : ReduceD (r.vwk ρ) (r'.vwk ρ)
  := by cases d with
  | dead_cfg_left β n G m G' =>
    simp only [Region.vwk, wk, Function.comp_apply, vwk_lwk, Fin.comp_addCases_apply]
    rw [<-Function.comp.assoc, vwk_comp_lwk, Function.comp.assoc]
    apply dead_cfg_left
  | _ =>
    simp only [Region.vwk, wk, Function.comp_apply, vwk_lwk]
    constructor

theorem Reduce.vwk {r r' : Region φ} (ρ : ℕ → ℕ) (p : Reduce r r') : Reduce (r.vwk ρ) (r'.vwk ρ)
  := let ⟨d⟩ := p.nonempty; (d.vwk ρ).reduce

inductive StepD (Γ : ℕ → ε) : Region φ → Region φ → Type _
  | let1_beta (e r) : e.effect Γ = ⊥ → StepD Γ (let1 e r) (r.vsubst e.subst0)
  | reduce {r r'} : ReduceD r r' → StepD Γ r r'
  | rw {r r'} : RewriteD r r' → StepD Γ r r'
  | rw_op {r r'} : RewriteD r r' → StepD Γ r' r

-- TODO: separate beta relation? Then step is just the inf...

inductive Step (Γ : ℕ → ε) : Region φ → Region φ → Prop
  | let1_beta (e r) : e.effect Γ = ⊥ → Step Γ (let1 e r) (r.vsubst e.subst0)
  | reduce {r r'} : Reduce r r' → Step Γ r r'
  | rw {r r'} : Rewrite r r' → Step Γ r r'
  | rw_op {r r'} : Rewrite r r' → Step Γ r' r

theorem StepD.step {Γ : ℕ → ε} {r r' : Region φ} : StepD Γ r r' → Step Γ r r'
  | let1_beta e r he => Step.let1_beta e r he
  | reduce p => Step.reduce p.reduce
  | rw p => Step.rw p.rewrite
  | rw_op p => Step.rw_op p.rewrite

theorem Step.nonempty {Γ : ℕ → ε} {r r' : Region φ} : Step Γ r r' → Nonempty (StepD Γ r r')
  | let1_beta e r he => ⟨StepD.let1_beta e r he⟩
  | reduce p => let ⟨d⟩ := p.nonempty; ⟨StepD.reduce d⟩
  | rw p => let ⟨d⟩ := p.nonempty; ⟨StepD.rw d⟩
  | rw_op p => let ⟨d⟩ := p.nonempty; ⟨StepD.rw_op d⟩

theorem Step.nonempty_iff {Γ : ℕ → ε} {r r' : Region φ} : Step Γ r r' ↔ Nonempty (StepD Γ r r')
  := ⟨Step.nonempty, λ⟨d⟩ => d.step⟩

def StepD.vwk {Γ : ℕ → ε} {r r' : Region φ} (ρ : ℕ → ℕ)
  : StepD (Γ ∘ ρ) r r' → StepD Γ (r.vwk ρ) (r'.vwk ρ)
  | let1_beta e r he => by
    simp only [Region.vwk, vsubst_subst0_vwk]
    apply let1_beta
    rw [Term.effect_wk]
    assumption
  | reduce p => reduce $ p.vwk ρ
  | rw p => rw $ p.vwk ρ
  | rw_op p => rw_op $ p.vwk ρ

theorem Step.vwk {Γ : ℕ → ε} {r r' : Region φ} (ρ : ℕ → ℕ) (p : Step (Γ ∘ ρ) r r')
  : Step Γ (r.vwk ρ) (r'.vwk ρ) := let ⟨d⟩ := p.nonempty; (d.vwk ρ).step

inductive FStepD (Γ : ℕ → ε) : Region φ → Region φ → Type _
  | let1_beta (e r) : e.effect Γ = ⊥ → FStepD Γ (let1 e r) (r.vsubst e.subst0)
  | reduce {r r'} : ReduceD r r' → FStepD Γ r r'
  | rw {r r'} : RewriteD r r' → FStepD Γ r r'

inductive FStep (Γ : ℕ → ε) : Region φ → Region φ → Prop
  | let1_beta (e r) : e.effect Γ = ⊥ → FStep Γ (let1 e r) (r.vsubst e.subst0)
  | reduce {r r'} : Reduce r r' → FStep Γ r r'
  | rw {r r'} : Rewrite r r' → FStep Γ r r'

theorem FStepD.step {Γ : ℕ → ε} {r r' : Region φ} : FStepD Γ r r' → FStep Γ r r'
  | let1_beta e r he => FStep.let1_beta e r he
  | reduce p => FStep.reduce p.reduce
  | rw p => FStep.rw p.rewrite

theorem FStep.nonempty {Γ : ℕ → ε} {r r' : Region φ} : FStep Γ r r' → Nonempty (FStepD Γ r r')
  | let1_beta e r he => ⟨FStepD.let1_beta e r he⟩
  | reduce p => let ⟨d⟩ := p.nonempty; ⟨FStepD.reduce d⟩
  | rw p => let ⟨d⟩ := p.nonempty; ⟨FStepD.rw d⟩

theorem FStep.nonempty_iff {Γ : ℕ → ε} {r r' : Region φ} : FStep Γ r r' ↔ Nonempty (FStepD Γ r r')
  := ⟨FStep.nonempty, λ⟨d⟩ => d.step⟩

theorem FStep.fvs_le {Γ : ℕ → ε} {r r' : Region φ} (p : FStep Γ r r')
  : r'.fvs ⊆ r.fvs := by cases p with
  | let1_beta e r he => apply fvs_vsubst0_le
  | reduce p => exact p.fvs_le
  | rw p => rw [p.fvs_eq]

def FStepD.vwk {Γ : ℕ → ε} {r r' : Region φ} (ρ : ℕ → ℕ)
  : FStepD (Γ ∘ ρ) r r' → FStepD Γ (r.vwk ρ) (r'.vwk ρ)
  | let1_beta e r he => by
    simp only [Region.vwk, vsubst_subst0_vwk]
    apply let1_beta
    rw [Term.effect_wk]
    assumption
  | reduce p => reduce $ p.vwk ρ
  | rw p => rw $ p.vwk ρ

theorem FStep.vwk {Γ : ℕ → ε} {r r' : Region φ} (ρ : ℕ → ℕ) (p : FStep (Γ ∘ ρ) r r')
  : FStep Γ (r.vwk ρ) (r'.vwk ρ) := let ⟨d⟩ := p.nonempty; (d.vwk ρ).step

def FStepD.wk_eff {Γ Δ : ℕ → ε} {r r' : Region φ}
  (h : ∀i ∈ r.fvs, Γ i ≤ Δ i) : FStepD Δ r r' → FStepD Γ r r'
  | let1_beta e r he => let1_beta e r (by
    have he' := e.effect_le (λi hi => h i (Or.inl hi));
    rw [he] at he'
    simp only [le_bot_iff] at he'
    exact he')
  | reduce p => reduce p
  | rw p => rw p

theorem FStep.wk_eff {Γ Δ : ℕ → ε} {r r' : Region φ}
  (h : ∀i ∈ r.fvs, Γ i ≤ Δ i) (p : FStep Δ r r') : FStep Γ r r'
  := let ⟨d⟩ := p.nonempty; (d.wk_eff h).step

@[match_pattern]
def StepD.case_inl {Γ : ℕ → ε} (e : Term φ) (r s)
  : StepD Γ (case (inl e) r s) (let1 e r)
  := StepD.reduce (ReduceD.case_inl e r s)

@[match_pattern]
def StepD.case_inr {Γ : ℕ → ε} (e : Term φ) (r s)
  : StepD Γ (case (inr e) r s) (let1 e s)
  := StepD.reduce (ReduceD.case_inr e r s)

@[match_pattern]
def StepD.wk_cfg {Γ : ℕ → ε} (β : Region φ) (n G k) (ρ : Fin k → Fin n)
  : StepD Γ (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
    (cfg β k (G ∘ ρ))
  := StepD.reduce (ReduceD.wk_cfg β n G k ρ)

@[match_pattern]
def StepD.dead_cfg_left {Γ : ℕ → ε} (β : Region φ) (n G m G')
  : StepD Γ (cfg (β.lwk (· + n)) (n + m) (Fin.addCases G (lwk (· + n) ∘ G')))
    (cfg β m G')
  := StepD.reduce (ReduceD.dead_cfg_left β n G m G')

@[match_pattern]
def StepD.let1_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : StepD Γ (let1 (op f e) r) (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := StepD.rw $ RewriteD.let1_op f e r

@[match_pattern]
def StepD.let1_op_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : StepD Γ (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (op f e) r)
  := StepD.rw_op $ RewriteD.let1_op f e r

@[match_pattern]
def StepD.let1_pair {Γ : ℕ → ε} (a b) (r : Region φ)
  : StepD Γ (let1 (pair a b) r)
    (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) r.vwk1.vwk1)
  := StepD.rw $ RewriteD.let1_pair a b r

@[match_pattern]
def StepD.let1_pair_op {Γ : ℕ → ε} (a b) (r : Region φ)
  : StepD Γ (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) r.vwk1.vwk1)
    (let1 (pair a b) r)
  := StepD.rw_op $ RewriteD.let1_pair a b r

@[match_pattern]
def StepD.let1_inl {Γ : ℕ → ε} (e) (r : Region φ)
  : StepD Γ (let1 (inl e) r) (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := StepD.rw $ RewriteD.let1_inl e r

@[match_pattern]
def StepD.let1_inl_op {Γ : ℕ → ε} (e) (r : Region φ)
  : StepD Γ (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (inl e) r)
  := StepD.rw_op $ RewriteD.let1_inl e r

@[match_pattern]
def StepD.let1_inr {Γ : ℕ → ε} (e) (r : Region φ)
  : StepD Γ (let1 (inr e) r) (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := StepD.rw $ RewriteD.let1_inr e r

@[match_pattern]
def StepD.let1_inr_op {Γ : ℕ → ε} (e) (r : Region φ)
  : StepD Γ (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (inr e) r)
  := StepD.rw_op $ RewriteD.let1_inr e r

@[match_pattern]
def StepD.let1_abort {Γ : ℕ → ε} (e) (r : Region φ)
  : StepD Γ (let1 (abort e) r) (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := StepD.rw $ RewriteD.let1_abort e r

@[match_pattern]
def StepD.let1_abort_op {Γ : ℕ → ε} (e) (r : Region φ)
  : StepD Γ (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (abort e) r)
  := StepD.rw_op $ RewriteD.let1_abort e r

@[match_pattern]
def StepD.let2_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : StepD Γ (let2 (op f e) r) (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := StepD.rw $ RewriteD.let2_op f e r

@[match_pattern]
def StepD.let2_op_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : StepD Γ (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
    (let2 (op f e) r)
  := StepD.rw_op $ RewriteD.let2_op f e r

@[match_pattern]
def StepD.let2_pair {Γ : ℕ → ε} (a b) (r : Region φ)
  : StepD Γ (let2 (pair a b) r) (let1 a $ let1 (b.wk Nat.succ) $ r)
  := StepD.rw $ RewriteD.let2_pair a b r

@[match_pattern]
def StepD.let2_pair_op {Γ : ℕ → ε} (a b) (r : Region φ)
  : StepD Γ (let1 a $ let1 (b.wk Nat.succ) $ r)
    (let2 (pair a b) r)
  := StepD.rw_op $ RewriteD.let2_pair a b r

@[match_pattern]
def StepD.let2_abort {Γ : ℕ → ε} (e) (r : Region φ)
  : StepD Γ (let2 (abort e) r) (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := StepD.rw $ RewriteD.let2_abort e r

@[match_pattern]
def StepD.let2_abort_op {Γ : ℕ → ε} (e) (r : Region φ)
  : StepD Γ (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
    (let2 (abort e) r)
  := StepD.rw_op $ RewriteD.let2_abort e r

@[match_pattern]
def StepD.case_op {Γ : ℕ → ε} (f e) (r s : Region φ)
  : StepD Γ (case (op f e) r s)
    (let1 e $ case (op f (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ))
  )
  := StepD.rw $ RewriteD.case_op f e r s

@[match_pattern]
def StepD.case_op_op {Γ : ℕ → ε} (f e) (r s : Region φ)
  : StepD Γ (let1 e $ case (op f (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ)))
    (case (op f e) r s)
  := StepD.rw_op $ RewriteD.case_op f e r s

@[match_pattern]
def StepD.case_abort {Γ : ℕ → ε} (e) (r s : Region φ)
  : StepD Γ (case (abort e) r s)
    (let1 e $ case (abort (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ))
  )
  := StepD.rw $ RewriteD.case_abort e r s

@[match_pattern]
def StepD.case_abort_op {Γ : ℕ → ε} (e) (r s : Region φ)
  : StepD Γ (let1 e $ case (abort (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ)))
    (case (abort e) r s)
  := StepD.rw_op $ RewriteD.case_abort e r s

@[match_pattern]
def StepD.let1_case {Γ : ℕ → ε} (a b) (r s : Region φ)
  : StepD Γ (let1 a $ case (b.wk Nat.succ) r s)
    (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
  := StepD.rw $ RewriteD.let1_case a b r s

@[match_pattern]
def StepD.let1_case_op {Γ : ℕ → ε} (a b) (r s : Region φ)
  : StepD Γ (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
    (let1 a $ case (b.wk Nat.succ) r s)
  := StepD.rw_op $ RewriteD.let1_case a b r s

@[match_pattern]
def StepD.let2_case {Γ : ℕ → ε} (a b) (r s : Region φ)
  : StepD Γ (let2 a $ case (b.wk (· + 2)) r s)
    (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
  := StepD.rw $ RewriteD.let2_case a b r s

@[match_pattern]
def StepD.let2_case_op {Γ : ℕ → ε} (a b) (r s : Region φ)
  : StepD Γ (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
    (let2 a $ case (b.wk (· + 2)) r s)
  := StepD.rw_op $ RewriteD.let2_case a b r s

@[match_pattern]
def StepD.cfg_br_lt {Γ : ℕ → ε} (ℓ) (e : Term φ) (n G) (h : ℓ < n)
  : StepD Γ (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).let1 e) n G)
  := StepD.rw $ RewriteD.cfg_br_lt ℓ e n G h

@[match_pattern]
def StepD.cfg_br_lt_op {Γ : ℕ → ε} (ℓ) (e : Term φ) (n G) (h : ℓ < n)
  : StepD Γ (cfg ((G ⟨ℓ, h⟩).let1 e) n G) (cfg (br ℓ e) n G)
  := StepD.rw_op $ RewriteD.cfg_br_lt ℓ e n G h

@[match_pattern]
def StepD.cfg_let1 {Γ : ℕ → ε} (a : Term φ) (β n G)
  : StepD Γ (cfg (let1 a β) n G) (let1 a $ cfg β n (vwk1 ∘ G))
  := StepD.rw $ RewriteD.cfg_let1 a β n G

@[match_pattern]
def StepD.cfg_let1_op {Γ : ℕ → ε} (a : Term φ) (β n G)
  : StepD Γ (let1 a $ cfg β n (vwk1 ∘ G))
    (cfg (let1 a β) n G)
  := StepD.rw_op $ RewriteD.cfg_let1 a β n G

@[match_pattern]
def StepD.cfg_let2 {Γ : ℕ → ε} (a : Term φ) (β n G)
  : StepD Γ (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk1 ∘ vwk1 ∘ G))
  := StepD.rw $ RewriteD.cfg_let2 a β n G

@[match_pattern]
def StepD.cfg_let2_op {Γ : ℕ → ε} (a : Term φ) (β n G)
  : StepD Γ (let2 a $ cfg β n (vwk1 ∘ vwk1 ∘ G))
    (cfg (let2 a β) n G)
  := StepD.rw_op $ RewriteD.cfg_let2 a β n G

@[match_pattern]
def StepD.cfg_case {Γ : ℕ → ε} (e : Term φ) (r s n G)
  : StepD Γ (cfg (case e r s) n G)
    (case e (cfg r n (vwk1 ∘ G)) (cfg s n (vwk1 ∘ G))
  )
  := StepD.rw $ RewriteD.cfg_case e r s n G

@[match_pattern]
def StepD.cfg_case_op {Γ : ℕ → ε} (e : Term φ) (r s n G)
  : StepD Γ (case e (cfg r n (vwk1 ∘ G)) (cfg s n (vwk1 ∘ G)))
    (cfg (case e r s) n G)
  := StepD.rw_op $ RewriteD.cfg_case e r s n G

@[match_pattern]
def StepD.cfg_cfg {Γ : ℕ → ε} (β : Region φ) (n G n' G')
  : StepD Γ (cfg (cfg β n G) n' G') (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
  := StepD.rw $ RewriteD.cfg_cfg β n G n' G'

@[match_pattern]
def StepD.cfg_cfg_op {Γ : ℕ → ε} (β : Region φ) (n G n' G')
  : StepD Γ (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
    (cfg (cfg β n G) n' G')
  := StepD.rw_op $ RewriteD.cfg_cfg β n G n' G'

@[match_pattern]
def StepD.cfg_zero {Γ : ℕ → ε} (β : Region φ) (G)
  : StepD Γ (cfg β 0 G) β := StepD.rw $ RewriteD.cfg_zero β G

@[match_pattern]
def StepD.cfg_zero_op {Γ : ℕ → ε} (β : Region φ) (G)
  : StepD Γ β (cfg β 0 G) := StepD.rw_op $ RewriteD.cfg_zero β G

@[match_pattern]
def StepD.let2_eta {Γ : ℕ → ε} (e) (r : Region φ)
  : StepD Γ (let2 e (let1 ((var 1).pair (var 0)) r.vwk1.vwk1)) (let1 e r)
  := StepD.rw $ RewriteD.let2_eta e r

@[match_pattern]
def StepD.let2_eta_op {Γ : ℕ → ε} (r : Region φ)
  : StepD Γ (let1 e r) (let2 e (let1 ((var 1).pair (var 0)) r.vwk1.vwk1))
  := StepD.rw_op $ RewriteD.let2_eta e r

-- @[match_pattern]
-- def StepD.let1_eta {Γ : ℕ → ε} (r : Region φ)
--   : StepD Γ (let1 (var 0) r.vwk1) r
--   := StepD.rw $ RewriteD.let1_eta r

-- @[match_pattern]
-- def StepD.let1_eta_op {Γ : ℕ → ε} (r : Region φ)
--   : StepD Γ r (let1 (var 0) r.vwk1)
--   := StepD.rw_op $ RewriteD.let1_eta r

def StepD.cast_trg {Γ : ℕ → ε} {r₀ r₁ r₁' : Region φ} (p : StepD Γ r₀ r₁) (h : r₁ = r₁')
  : StepD Γ r₀ r₁' := h ▸ p

def StepD.cast_src {Γ : ℕ → ε} {r₀ r₀' r₁ : Region φ} (h : r₀' = r₀) (p : StepD Γ r₀ r₁)
  : StepD Γ r₀' r₁ := h ▸ p

def StepD.cast {Γ : ℕ → ε} {r₀ r₀' r₁ r₁' : Region φ} (h₀ : r₀ = r₀') (h₁ : r₁ = r₁')
  (p : StepD Γ r₀ r₁) : StepD Γ r₀' r₁' := h₁ ▸ h₀ ▸ p

theorem ReduceD.effect_le {Γ : ℕ → ε} {r r' : Region φ} (p : ReduceD r r')
  : r'.effect Γ ≤ r.effect Γ := by
  cases p with
  | case_inl _ _ _ => simp
  | case_inr e r s =>
    simp only [effect, Term.effect]
    rw [sup_assoc, sup_comm (r.effect _), <-sup_assoc]
    simp
  | wk_cfg _ _ _ _ _ =>
    simp only [effect_cfg, effect_lwk, <-Function.comp.assoc, effect_comp_lwk]
    apply sup_le_sup_left
    apply Fin.sup_comp_le
  | dead_cfg_left _ _ _ _ =>
    simp only [effect_cfg, effect_lwk, Fin.comp_addCases, Fin.sup_addCases]
    apply sup_le_sup_left
    apply le_sup_of_le_right
    rw [<-Function.comp.assoc, effect_comp_lwk]

theorem StepD.effect_le {Γ : ℕ → ε} {r r' : Region φ} (p : StepD Γ r r')
  : r'.effect Γ ≤ r.effect Γ := by
  cases p with
  | let1_beta _ _ he =>
    apply le_of_eq
    simp only [effect_vsubst, Subst.effect, effect, he, ge_iff_le, bot_le, sup_of_le_right]
    congr
    funext k
    cases k with
    | zero => simp [he, Nat.liftBot]
    | succ k => rfl
  | reduce p => exact p.effect_le
  | rw p => rw [p.effect]
  | rw_op p => rw [p.effect]

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

abbrev RWD (P : (ℕ → ε) → Region φ → Region φ → Type _) (Γ : ℕ → ε) := Corr.Path ((BCongD P) Γ)

-- TODO: RwD is effect monotone/antitone iff underlying is
-- ==> RwD is effect preserving iff underlying is

@[match_pattern]
def RWD.refl {P} {Γ : ℕ → ε} (r : Region φ) : RWD P Γ r r := Corr.Path.nil r

@[match_pattern]
def RWD.cons {P} {Γ : ℕ → ε} {a b c : Region φ} : RWD P Γ a b → BCongD P Γ b c → RWD P Γ a c
  := Corr.Path.cons

def RWD.single {P} {Γ : ℕ → ε} {a b : Region φ} : BCongD P Γ a b → RWD P Γ a b := Corr.Path.single

def RWD.comp {P} {Γ : ℕ → ε} {a b c : Region φ} : RWD P Γ a b → RWD P Γ b c → RWD P Γ a c
  := Corr.Path.comp

def RWD.let1_beta {Γ : ℕ → ε} (e) (r : Region φ) (h : e.effect Γ = ⊥)
  : RWD StepD Γ (let1 e r) (r.vsubst e.subst0)
  := single $ BCongD.rel $ StepD.let1_beta e r h

def RWD.case_inl {Γ : ℕ → ε} (e) (r s : Region φ)
  : RWD StepD Γ (case (inl e) r s) (let1 e r)
  := single $ BCongD.rel $ StepD.case_inl e r s

def RWD.case_inr {Γ : ℕ → ε} (e) (r s : Region φ)
  : RWD StepD Γ (case (inr e) r s) (let1 e s)
  := single $ BCongD.rel $ StepD.case_inr e r s

def RWD.let1_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : RWD StepD Γ (let1 (op f e) r) (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := single $ BCongD.rel $ StepD.let1_op f e r

def RWD.let1_op_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : RWD StepD Γ (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (op f e) r)
  := single $ BCongD.rel $ StepD.let1_op_op f e r

def RWD.let1_pair {Γ : ℕ → ε} (a b) (r : Region φ)
  : RWD StepD Γ (let1 (pair a b) r)
    (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) r.vwk1.vwk1
  )
  := single $ BCongD.rel $ StepD.let1_pair a b r

def RWD.let1_pair_op {Γ : ℕ → ε} (a b) (r : Region φ)
  : RWD StepD Γ (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) r.vwk1.vwk1)
    (let1 (pair a b) r)
  := single $ BCongD.rel $ StepD.let1_pair_op a b r

def RWD.let1_inl {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 (inl e) r) (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := single $ BCongD.rel $ StepD.let1_inl e r

def RWD.let1_inl_op {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (inl e) r)
  := single $ BCongD.rel $ StepD.let1_inl_op e r

def RWD.let1_inr {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 (inr e) r) (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := single $ BCongD.rel $ StepD.let1_inr e r

def RWD.let1_inr_op {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (inr e) r)
  := single $ BCongD.rel $ StepD.let1_inr_op e r

def RWD.let1_abort {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 (abort e) r) (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := single $ BCongD.rel $ StepD.let1_abort e r

def RWD.let1_abort_op {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (abort e) r)
  := single $ BCongD.rel $ StepD.let1_abort_op e r

def RWD.let2_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : RWD StepD Γ (let2 (op f e) r) (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := single $ BCongD.rel $ StepD.let2_op f e r

def RWD.let2_op_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : RWD StepD Γ (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
    (let2 (op f e) r)
  := single $ BCongD.rel $ StepD.let2_op_op f e r

def RWD.let2_pair {Γ : ℕ → ε} (a b) (r : Region φ)
  : RWD StepD Γ (let2 (pair a b) r) (let1 a $ let1 (b.wk Nat.succ) $ r)
  := single $ BCongD.rel (StepD.let2_pair a b r)

def RWD.let2_pair_op {Γ : ℕ → ε} (a b) (r : Region φ)
  : RWD StepD Γ (let1 a $ let1 (b.wk Nat.succ) $ r)
    (let2 (pair a b) r)
  := single $ BCongD.rel $ StepD.let2_pair_op a b r

def RWD.let2_abort {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let2 (abort e) r) (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := single $ BCongD.rel $ StepD.let2_abort e r

def RWD.let2_abort_op {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
    (let2 (abort e) r)
  := single $ BCongD.rel $ StepD.let2_abort_op e r

def RWD.case_op {Γ : ℕ → ε} (f e) (r s : Region φ)
  : RWD StepD Γ (case (op f e) r s)
    (let1 e $ case (op f (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ))
  )
  := single $ BCongD.rel $ StepD.case_op f e r s

def RWD.case_op_op {Γ : ℕ → ε} (f e) (r s : Region φ)
  : RWD StepD Γ (let1 e $ case (op f (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ)))
    (case (op f e) r s)
  := single $ BCongD.rel $ StepD.case_op_op f e r s

def RWD.case_abort {Γ : ℕ → ε} (e) (r s : Region φ)
  : RWD StepD Γ (case (abort e) r s)
    (let1 e $ case (abort (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ))
  )
  := single $ BCongD.rel $ StepD.case_abort e r s

def RWD.case_abort_op {Γ : ℕ → ε} (e) (r s : Region φ)
  : RWD StepD Γ (let1 e $ case (abort (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ)))
    (case (abort e) r s)
  := single $ BCongD.rel $ StepD.case_abort_op e r s

def RWD.let1_case {Γ : ℕ → ε} (a b) (r s : Region φ)
  : RWD StepD Γ (let1 a $ case (b.wk Nat.succ) r s)
    (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
  := single $ BCongD.rel $ StepD.let1_case a b r s

def RWD.let1_case_op {Γ : ℕ → ε} (a b) (r s : Region φ)
  : RWD StepD Γ (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
    (let1 a $ case (b.wk Nat.succ) r s)
  := single $ BCongD.rel $ StepD.let1_case_op a b r s

def RWD.let2_case {Γ : ℕ → ε} (a b) (r s : Region φ)
  : RWD StepD Γ (let2 a $ case (b.wk (· + 2)) r s)
    (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
  := single $ BCongD.rel $ StepD.let2_case a b r s

def RWD.let2_case_op {Γ : ℕ → ε} (a b) (r s : Region φ)
  : RWD StepD Γ (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
    (let2 a $ case (b.wk (· + 2)) r s)
  := single $ BCongD.rel $ StepD.let2_case_op a b r s

def RWD.cfg_br_lt {Γ : ℕ → ε} (ℓ) (e : Term φ) (n G) (h : ℓ < n)
  : RWD StepD Γ (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).let1 e) n G)
  := single $ BCongD.rel $ StepD.cfg_br_lt ℓ e n G h

def RWD.cfg_br_lt_op {Γ : ℕ → ε} (ℓ) (e : Term φ) (n G) (h : ℓ < n)
  : RWD StepD Γ (cfg ((G ⟨ℓ, h⟩).let1 e) n G) (cfg (br ℓ e) n G)
  := single $ BCongD.rel $ StepD.cfg_br_lt_op ℓ e n G h

def RWD.cfg_let1 {Γ : ℕ → ε} (a : Term φ) (β n G)
  : RWD StepD Γ (cfg (let1 a β) n G) (let1 a $ cfg β n (vwk1 ∘ G))
  := single $ BCongD.rel $ StepD.cfg_let1 a β n G

def RWD.cfg_let1_op {Γ : ℕ → ε} (a : Term φ) (β n G)
  : RWD StepD Γ (let1 a $ cfg β n (vwk1 ∘ G))
    (cfg (let1 a β) n G)
  := single $ BCongD.rel $ StepD.cfg_let1_op a β n G

def RWD.cfg_let2 {Γ : ℕ → ε} (a : Term φ) (β n G)
  : RWD StepD Γ (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk1 ∘ vwk1 ∘ G))
  := single $ BCongD.rel $ StepD.cfg_let2 a β n G

def RWD.cfg_let2_op {Γ : ℕ → ε} (a : Term φ) (β n G)
  : RWD StepD Γ (let2 a $ cfg β n (vwk1 ∘ vwk1 ∘ G))
    (cfg (let2 a β) n G)
  := single $ BCongD.rel $ StepD.cfg_let2_op a β n G

def RWD.cfg_case {Γ : ℕ → ε} (e : Term φ) (r s n G)
  : RWD StepD Γ (cfg (case e r s) n G)
    (case e (cfg r n (vwk1 ∘ G)) (cfg s n (vwk1 ∘ G))
  )
  := single $ BCongD.rel $ StepD.cfg_case e r s n G

def RWD.cfg_case_op {Γ : ℕ → ε} (e : Term φ) (r s n G)
  : RWD StepD Γ (case e (cfg r n (vwk1 ∘ G)) (cfg s n (vwk1 ∘ G)))
    (cfg (case e r s) n G)
  := single $ BCongD.rel $ StepD.cfg_case_op e r s n G

def RWD.cfg_cfg {Γ : ℕ → ε} (β : Region φ) (n G n' G')
  : RWD StepD Γ (cfg (cfg β n G) n' G') (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
  := single $ BCongD.rel $ StepD.cfg_cfg β n G n' G'

def RWD.cfg_cfg_op {Γ : ℕ → ε} (β : Region φ) (n G n' G')
  : RWD StepD Γ (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
    (cfg (cfg β n G) n' G')
  := single $ BCongD.rel $ StepD.cfg_cfg_op β n G n' G'

def RWD.cfg_zero {Γ : ℕ → ε} (β : Region φ) (G)
  : RWD StepD Γ (cfg β 0 G) β := single $ BCongD.rel $ StepD.cfg_zero β G

def RWD.cfg_zero_op {Γ : ℕ → ε} (β : Region φ) (G)
  : RWD StepD Γ β (cfg β 0 G) := single $ BCongD.rel $ StepD.cfg_zero_op β G

def RWD.wk_cfg {Γ : ℕ → ε} (β : Region φ) (n G k) (ρ : Fin k → Fin n) /-(hρ : Function.Bijective ρ)-/
  : RWD StepD Γ
    (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
    (cfg β k (G ∘ ρ))
  := single $ BCongD.rel $ StepD.wk_cfg β n G k ρ

def RWD.dead_cfg_left {Γ : ℕ → ε} (β : Region φ) (n G m G')
  : RWD StepD Γ
    (cfg (β.lwk (· + n)) (n + m) (Fin.addCases G (lwk (· + n) ∘ G')))
    (cfg β m G')
  := single $ BCongD.rel $ StepD.dead_cfg_left β n G m G'

def RWD.swap_cfg' {Γ : ℕ → ε} (β : Region φ) (n G m G')
  : RWD StepD Γ
    (cfg
      (lwk (Fin.toNatWk (Fin.swapAdd n m)) β)
      (m + n) (lwk (Fin.toNatWk (Fin.swapAdd n m)) ∘ Fin.addCases G' G))
    (cfg β (n + m) (Fin.addCases G G'))
  :=
  have h : Fin.addCases G G' = Fin.addCases G' G ∘ Fin.swapAdd n m := by
    rw [Fin.addCases_comp_swapAdd]
  by
    rw [h]
    apply wk_cfg

def RWD.cast_trg {P} {Γ : ℕ → ε} {r₀ r₁ r₁' : Region φ} (h : RWD P Γ r₀ r₁) (hr₁ : r₁ = r₁')
  : RWD P Γ r₀ r₁'
  := Corr.Path.cast_trg h hr₁

def RWD.cast_src {P} {Γ : ℕ → ε} {r₀ r₀' r₁ : Region φ} (hr₀ : r₀ = r₀') (h : RWD P Γ r₀' r₁)
  : RWD P Γ r₀ r₁
  := Corr.Path.cast_src hr₀ h

def RWD.cast {P} {Γ : ℕ → ε} {r₀ r₀' r₁ r₁' : Region φ} (hr₀ : r₀ = r₀') (hr₁ : r₁ = r₁')
  (h : RWD P Γ r₀ r₁) : RWD P Γ r₀' r₁'
  := Corr.Path.cast hr₀ hr₁ h

def RWD.swap_cfg {Γ : ℕ → ε} (β : Region φ) (n G m G')
  : RWD StepD Γ
    (cfg β (n + m) (Fin.addCases G G'))
    (cfg
      (lwk (Fin.toNatWk (Fin.swapAdd n m)) β)
      (m + n) (lwk (Fin.toNatWk (Fin.swapAdd n m)) ∘ Fin.addCases G' G))
  := cast_trg (cast_src
    (by
      rw [
        <-Fin.comp_addCases,
        <-Function.comp.assoc,
        lwk_lwk, comp_lwk,
        Fin.swapAdd
      ]
      simp [<-Fin.toNatWk_comp, Fin.addCases_natAdd_castAdd_nil]
    )
    (swap_cfg'
      (β.lwk (Fin.toNatWk (Fin.addCases (Fin.natAdd m) (Fin.castAdd n))))
      m
      (lwk (Fin.toNatWk (Fin.addCases (Fin.natAdd m) (Fin.castAdd n))) ∘ G')
      n
      (lwk (Fin.toNatWk (Fin.addCases (Fin.natAdd m) (Fin.castAdd n))) ∘ G)))
    (by simp [Fin.comp_addCases, Fin.swapAdd])

def RWD.let1V0_id {Γ : ℕ → ε} (r : Region φ) (hΓ : Γ 0 = ⊥)
  : RWD StepD Γ r.let1V0 r
  := cast_trg
    (let1_beta (Term.var 0) (r.vwk (Nat.liftWk Nat.succ)) hΓ)
    (by rw [<-vsubst_fromWk_apply, vsubst_vsubst, vsubst_id']; funext i; cases i <;> rfl)

def RWD.let2_eta {Γ : ℕ → ε} (r : Region φ)
  : RWD StepD Γ
    (let2 e $
     let1 ((Term.var 1).pair (Term.var 0)) $
     r.vwk1.vwk1) (let1 e r)
  := single $ BCongD.rel $ StepD.let2_eta e r

def RWD.let2_eta_op {Γ : ℕ → ε} (r : Region φ)
  : RWD StepD Γ (let1 (Term.var 0) r)
    (let2 (Term.var 0) $
     let1 ((Term.var 1).pair (Term.var 0)) $
     r.vwk1.vwk1)
  := single $ BCongD.rel $ StepD.let2_eta_op r

-- def RWD.let1_eta {Γ : ℕ → ε} (r : Region φ)
--   : RWD StepD Γ
--     (let1 (Term.var 0) $
--      r.vwk1) r
--   := single $ BCongD.rel $ StepD.let1_eta r

-- def RWD.let1_eta_op {Γ : ℕ → ε} (r : Region φ)
--   : RWD StepD Γ r
--     (let1 (Term.var 0) $
--      r.vwk1)
--   := single $ BCongD.rel $ StepD.let1_eta_op r

instance instTransRWD
  {P : (ℕ → ε) → Region φ → Region φ → Type _} {Γ}
  : Trans (RWD P Γ) (RWD P Γ) (RWD P Γ) where
  trans := RWD.comp

infixr:10 " ⟶R " => λ{P Γ} => RWD P Γ

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

def RWD.let1 {P} {Γ : ℕ → ε} {r r'} (e : Term φ) (h : RWD P (Nat.liftBot Γ) r r')
  : RWD P Γ (let1 e r) (let1 e r')
  := (BCongD.let1_func e).mapPath h

def RWD.let2 {P} {Γ : ℕ → ε} {r r'} (e : Term φ) (h : RWD P (Nat.liftnBot 2 Γ) r r')
  : RWD P Γ (let2 e r) (let2 e r')
  := (BCongD.let2_func e).mapPath h

def RWD.case_left {P} {Γ : ℕ → ε} {r r'} (e : Term φ) (h : RWD P (Nat.liftBot Γ) r r') (s)
  : RWD P Γ (case e r s) (case e r' s)
  := (BCongD.case_left_func e s).mapPath h

def RWD.case_right {P} {Γ : ℕ → ε} (e : Term φ) (r) (h : RWD P (Nat.liftBot Γ) s s')
  : RWD P Γ (case e r s) (case e r s')
  := (BCongD.case_right_func e r).mapPath h

def RWD.cfg_entry {P} {Γ : ℕ → ε} {r r' : Region φ} (h : RWD P Γ r r') (n G)
  : RWD P Γ (cfg r n G) (cfg r' n G)
  := (BCongD.cfg_entry_func n G).mapPath h

def RWD.cfg_block' {P} {Γ : ℕ → ε} {r r' : Region φ} (β n G i) (h : RWD P (Nat.liftBot Γ) r r')
  : RWD P Γ (cfg β n (Function.update G i r)) (cfg β n (Function.update G i r'))
  := (BCongD.cfg_block_func' β n G i).mapPath h

def RWD.case {P} {Γ : ℕ → ε} {r r' : Region φ} (e : Term φ)
  (hr : RWD P (Nat.liftBot Γ) r r')
  (hs : RWD P (Nat.liftBot Γ) s s')
  : RWD P Γ (case e r s) (case e r' s')
  := (case_left e hr s).comp (case_right e r' hs)

def RWD.of_eq {P} {Γ : ℕ → ε} {r r' : Region φ} (h : r = r')
  : RWD P Γ r r' := cast_trg (refl r) h

def RWD.cfg_blocks_partial {P} {Γ : ℕ → ε} (β n) (G : Fin n → Region φ) (G': Fin n → Region φ)
  (h : ∀i, RWD P (Nat.liftBot Γ) (G i) (G' i))
  : ∀k : ℕ, RWD P Γ (Region.cfg β n G) (Region.cfg β n (λi => if i < k then G' i else G i))
  | 0 => RWD.refl _
  | k + 1 => if hk : k < n then
      RWD.comp
        (cast_trg (cfg_blocks_partial β n G G' h k)
          (by
            congr
            rw [Function.eq_update_self_iff]
            simp))
        (cast_trg (cfg_block' β n
          (λi => if i < k then G' i else G i)
          ⟨k, hk⟩ (h ⟨k, hk⟩))
          (by
            congr
            funext i
            split
            case _ h =>
              rw [Function.update_apply]
              split
              case _ h =>
                cases h
                rfl
              case _ he =>
                have h : i < k := Nat.lt_of_le_of_ne
                  (Nat.le_of_lt_succ h)
                  (Fin.vne_of_ne he)
                simp [h]
            case _ h =>
              have h := Nat.le_of_not_lt h
              rw [Function.update_noteq, ite_cond_eq_false]
              simp [Nat.le_of_succ_le h]
              apply Fin.ne_of_gt
              exact Nat.lt_of_succ_le h
            ))
    else
      cast_trg (cfg_blocks_partial β n G G' h k) (by
        have hk := Nat.le_of_not_lt hk;
        simp only [cfg.injEq, heq_eq_eq, true_and]
        funext i
        have hi := Nat.lt_of_lt_of_le i.prop hk
        simp [hi, Nat.lt_succ_of_lt hi]
      )

def RWD.cfg_blocks {P} {Γ : ℕ → ε} (β n) (G G' : Fin n → Region φ)
  (h : ∀i, RWD P (Nat.liftBot Γ) (G i) (G' i))
  : RWD P Γ (Region.cfg β n G) (Region.cfg β n G')
  := cast_trg (cfg_blocks_partial β n G G' h n) (by simp)

def RWD.dead_cfg_right {Γ : ℕ → ε} (β : Region φ) (n G m G')
  : RWD StepD Γ
    (cfg (β.lwk (n.liftnWk (· + m))) (n + m) (Fin.addCases (lwk (n.liftnWk (· + m)) ∘ G) G'))
    (cfg β n G) :=
    (cast_trg (swap_cfg (β.lwk (n.liftnWk (· + m))) n (lwk (n.liftnWk (· + m)) ∘ G) m G')
      (by rw [
        Fin.comp_addCases, lwk_lwk, <-Function.comp.assoc, comp_lwk,
        Fin.toNatWk_swapAdd_comp_liftnWk_add]
      )).comp
    (dead_cfg_left β m _ n G)

def RWD.cfg_elim {Γ : ℕ → ε} (β : Region φ) (n G)
  : RWD StepD Γ (cfg (β.lwk (· + n)) n G) β
  :=
  let s : RWD StepD Γ
    (cfg (β.lwk (· + n)) n G)
    (cfg (β.lwk (· + n)) (n + 0) (Fin.addCases G (lwk (· + n) ∘ Fin.elim0)))
    := RWD.of_eq (by simp [Fin.addCases_zero])
  (s.comp (dead_cfg_left β n G 0 Fin.elim0)).comp (RWD.cfg_zero _ _)
  -- := match β with
  -- | Region.br ℓ e => (cfg_br_ge (ℓ + n) e n G (by simp)).cast_trg (by simp)
  -- | Region.let1 a β => (cfg_let1 a (β.lwk (· + n)) n G).comp (let1 a (cfg_elim β n _))
  -- | Region.let2 a β => (cfg_let2 a (β.lwk (· + n)) n G).comp (let2 a (cfg_elim β n _))
  -- | Region.case e r s =>
  --   (cfg_case e (r.lwk (· + n)) (s.lwk (· + n)) n G).comp
  --     (case e (cfg_elim r n _) (cfg_elim s n _))
  -- | Region.cfg β n' G' => (cfg_cfg _ _ _ _ _).comp (dead_cfg_right _ _ _ _ _)

def RWD.cfg_br_ge {Γ : ℕ → ε} (ℓ) (e : Term φ) (n G) (h : n ≤ ℓ)
  : RWD StepD Γ (cfg (br ℓ e) n G) (br (ℓ - n) e)
  := cast_src (by simp [h]) (cfg_elim (br (ℓ - n) e) n G)

-- TODO: vwk, lwk lore...

end Region

end BinSyntax
