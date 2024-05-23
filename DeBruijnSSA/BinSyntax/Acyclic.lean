import DeBruijnSSA.BinSyntax.Syntax.Fv
import Discretion.Wk.Set
import Discretion.Wk.Multiset
import Discretion.Utils

namespace BinSyntax

inductive Region.SAcyclic' : Set ℕ → Set (Region φ)
  | br D ℓ e : ℓ ∉ D → SAcyclic' D (br ℓ e)
  | case e : SAcyclic' D s → SAcyclic' D t → SAcyclic' D (case e s t)
  | let1 e : SAcyclic' D s → SAcyclic' D (let1 e s)
  | let2 e : SAcyclic' D s → SAcyclic' D (let2 e s)
  | cfg : SAcyclic' ((· + n) '' D) β →
    (∀i : Fin n, SAcyclic' ((· + n) '' D ∪ Set.Iio n) (G i)) → SAcyclic' D (cfg β n G)

abbrev Region.SAcyclic : Region φ → Prop := SAcyclic' ∅

def Region.DirectJumps (G : Fin n → Region φ) (i : ℕ) : Set ℕ
  := { j | ∃h : j < n, i ∈ (G ⟨j, h⟩).fl }

theorem Region.DirectJumps.comp_vwk (ρ) : DirectJumps (vwk ρ ∘ G) = DirectJumps G := by
  funext i
  simp only [DirectJumps, Function.comp_apply, Region.fl_vwk]

theorem Region.DirectJumps.vwk (ρ)
  : @DirectJumps φ n (λi => (G i).vwk ρ) = DirectJumps G := comp_vwk ρ

def Region.JumpSet (G : Fin n → Region φ) : ℕ → Set ℕ
  := Relation.TransGen (DirectJumps G)

theorem Region.JumpSet.lt_n {G : Fin n → Region φ} (h : JumpSet G i j) : j < n := by
  cases h with
  | single hr => exact hr.1
  | tail _ hr => exact hr.1

theorem Region.JumpSet.comp_vwk (ρ) : JumpSet (vwk ρ ∘ G) = JumpSet G := by
  simp only [JumpSet, DirectJumps.comp_vwk]

theorem Region.JumpSet.vwk (ρ) : @JumpSet n φ (λi => (G i).vwk ρ) = JumpSet G := comp_vwk ρ

-- TODO: lwk lift...

def Region.ReachableSet (G : Fin n → Region φ) : ℕ → ℕ → Prop
  := Relation.ReflTransGen (DirectJumps G)

theorem Region.ReachableSet.lt_or_eq {G : Fin n → Region φ} (h : ReachableSet G i j) : j < n ∨ i = j
  := by cases h with
  | refl => right; rfl
  | tail _ hr => left; exact hr.1

theorem Region.ReachableSet.comp_vwk (ρ) : ReachableSet (vwk ρ ∘ G) = ReachableSet G := by
  simp only [ReachableSet, DirectJumps.comp_vwk]

theorem Region.ReachableSet.vwk (ρ) : @ReachableSet n φ (λi => (G i).vwk ρ) = ReachableSet G
  := comp_vwk ρ

theorem Region.JumpSet.subset_reachable : JumpSet G i ⊆ ReachableSet G i := by
  intro j h
  induction h with
  | single hr => exact Relation.ReflTransGen.refl.tail hr
  | tail _ hr I => exact I.tail hr

inductive Region.Acyclic' : Set ℕ → Set (Region φ)
  | br D ℓ e : ℓ ∉ D → Acyclic' D (br ℓ e)
  | case e : Acyclic' D s → Acyclic' D t → Acyclic' D (case e s t)
  | let1 e : Acyclic' D s → Acyclic' D (let1 e s)
  | let2 e : Acyclic' D s → Acyclic' D (let2 e s)
  | cfg : Acyclic' ((· + n) '' D) β →
    (∀i : Fin n, Acyclic' ((· + n) '' D ∪ ReachableSet G i) (G i)) → Acyclic' D (cfg β n G)

theorem Region.Acyclic'.antitone : Antitone (@Region.Acyclic' φ) := by
  intro D' D hD r h
  induction h generalizing D' with
  | br D ℓ e h => exact br D' ℓ e (λc => h (hD c))
  | case e _ _ Is It => exact case e (Is hD) (It hD)
  | let1 e _ Ir => exact let1 e (Ir hD)
  | let2 e _ Ir => exact let2 e (Ir hD)
  | cfg _ _ Iβ IG =>
    exact cfg
      (Iβ (Set.image_subset _ hD))
      λi => IG i $ Set.union_subset_union_left _ (Set.image_subset _ hD)

theorem Region.SAcyclic'.acyclic' (h : SAcyclic' D r) : Acyclic' D r := by
  induction h with
  | br D ℓ e h => exact Acyclic'.br _ _ _ h
  | case e _ _ Is It => exact Acyclic'.case e Is It
  | let1 e _ Is => exact Acyclic'.let1 e Is
  | let2 e _ Is => exact Acyclic'.let2 e Is
  | cfg _ _ Iβ IG =>
    apply Acyclic'.cfg Iβ
    intro i
    apply Acyclic'.antitone _ (IG i)
    apply Set.union_subset_iff.mpr
    constructor
    . simp
    . intro x hx'
      right
      cases hx'.lt_or_eq with
      | inl h => exact lt_of_lt_of_le h (le_refl _)
      | inr h => exact lt_of_lt_of_le (h ▸ i.prop) (le_refl _)

theorem Region.Acyclic'.not_mem_fl (h : Acyclic' D r) : ∀i ∈ D, i ∉ r.fl := by
  intro i hi
  induction h generalizing i with
  | br D ℓ e h =>
    intro hi
    cases Multiset.mem_singleton.mp hi
    contradiction
  | case e _ _ Is It =>
    rw [Region.fl, Multiset.mem_add, not_or]
    exact ⟨Is _ hi, It _ hi⟩
  | let1 _ _ Ir => exact Ir i hi
  | let2 _ _ Ir => exact Ir i hi
  | cfg _ _ Iβ IG =>
    rw [Region.fl, Multiset.mem_add, not_or]
    constructor
    rw [Multiset.mem_liftnFv]
    exact Iβ _ ⟨i, hi, rfl⟩
    rw [Multiset.not_mem_finsum_univ]
    intro k
    rw [Multiset.mem_liftnFv]
    apply IG
    simp [hi]

theorem Region.Acyclic'.mem_fl (h : Acyclic' D r) : ∀i ∈ r.fl, i ∉ D
  := λi hi hd => h.not_mem_fl i hd hi

theorem Region.SAcyclic'.not_mem_fl (h : SAcyclic' D r) : ∀i ∈ D, i ∉ r.fl := h.acyclic'.not_mem_fl

theorem Region.SAcyclic'.mem_fl (h : SAcyclic' D r) : ∀i ∈ r.fl, i ∉ D := h.acyclic'.mem_fl

theorem Region.Acyclic'.vwk (ρ) (h : Acyclic' D r) : Acyclic' D (vwk ρ r) := by
  induction h generalizing ρ with
  | cfg _ _ Iβ IG =>
    apply Acyclic'.cfg (Iβ _)
    intro i
    rw [ReachableSet.vwk]
    apply IG
  | _ => constructor <;> apply_assumption

inductive Region.Acyclic : Set (Region φ)
  | br ℓ e : Acyclic (br ℓ e)
  | case e : Acyclic s → Acyclic t → Acyclic (case e s t)
  | let1 e : Acyclic s → Acyclic (let1 e s)
  | let2 e : Acyclic s → Acyclic (let2 e s)
  | cfg : Acyclic β →
    (∀i : Fin n, Acyclic (G i)) →
    (∀i : Fin n, ↑i ∉ JumpSet G i) → Acyclic (cfg β n G)

-- theorem Region.Acyclic.acyclic_iff (r : Region φ) : Acyclic r ↔ Acyclic' ∅ r := by
--   sorry

-- theorem Region.Acyclic.eq_acyclic : @Acyclic φ = Acyclic' ∅ := Set.ext acyclic_iff

-- theorem Region.Acyclic.subset_acyclic' : @Acyclic φ ⊆ Acyclic' D := sorry

-- TODO: acyclicity is preserved by acyclic substitution

-- TODO: strict acyclicity is preserved by strict acyclic substitution
