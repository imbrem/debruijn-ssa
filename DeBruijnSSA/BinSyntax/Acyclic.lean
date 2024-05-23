import DeBruijnSSA.BinSyntax.Syntax.Fv
import Discretion.Wk.Set
import Discretion.Wk.Multiset
import Discretion.Utils

namespace BinSyntax

namespace Region

inductive SAcyclic' : Set ℕ → Set (Region φ)
  | br {D ℓ} (h : ℓ ∉ D) e : SAcyclic' D (br ℓ e)
  | case e : SAcyclic' D s → SAcyclic' D t → SAcyclic' D (case e s t)
  | let1 e : SAcyclic' D s → SAcyclic' D (let1 e s)
  | let2 e : SAcyclic' D s → SAcyclic' D (let2 e s)
  | cfg : SAcyclic' ((· + n) '' D) β →
    (∀i : Fin n, SAcyclic' ((· + n) '' D ∪ Set.Iio n) (G i)) → SAcyclic' D (cfg β n G)

def Predecessors (G : Fin n → Region φ) (i : ℕ) : Set ℕ
  := { j | ∃h : j < n, i ∈ (G ⟨j, h⟩).fl }

theorem Predecessors.mem_fl {G : Fin n → Region φ} {i j} (h : j ∈ Predecessors G i)
  : i ∈ (G ⟨j, h.1⟩).fl := h.2

theorem Predecessors.comp_vwk (ρ) : Predecessors (vwk ρ ∘ G) = Predecessors G := by
  funext i
  simp only [Predecessors, Function.comp_apply, fl_vwk]

theorem Predecessors.vwk (ρ)
  : @Predecessors φ n (λi => (G i).vwk ρ) = Predecessors G := comp_vwk ρ

def Successors (G : Fin n → Region φ) (i : ℕ) : Set ℕ
  := if h : i < n then { j | j ∈ (G ⟨i, h⟩).fl } else ∅

theorem Successors.comp_vwk (ρ) : Successors (vwk ρ ∘ G) = Successors G := by
  funext i
  simp only [Successors, Function.comp_apply, fl_vwk]

theorem Successors.vwk (ρ) : @Successors n φ (λi => (G i).vwk ρ) = Successors G := comp_vwk ρ

def Ancestors (G : Fin n → Region φ) : ℕ → Set ℕ
  := Relation.TransGen (Predecessors G)

theorem Ancestors.lt {G : Fin n → Region φ} (h : Ancestors G i j) : j < n := by
  cases h with
  | single hr => exact hr.1
  | tail _ hr => exact hr.1

theorem Ancestors.of_mem_fl {G : Fin n → Region φ} (h : i ∈ (G j).fl)
  : ↑j ∈ Ancestors G i := Relation.TransGen.single ⟨j.prop, h⟩

theorem Ancestors.comp_vwk (ρ) : Ancestors (vwk ρ ∘ G) = Ancestors G := by
  simp only [Ancestors, Predecessors.comp_vwk]

theorem Ancestors.vwk (ρ) : @Ancestors n φ (λi => (G i).vwk ρ) = Ancestors G := comp_vwk ρ

-- TODO: lwk lift...

def SelfAncestors (G : Fin n → Region φ) : ℕ → Set ℕ
  := Relation.ReflTransGen (Predecessors G)

theorem SelfAncestors.eq_mem {G : Fin n → Region φ} {i j} (p : i = j)
  : i ∈ SelfAncestors G j := p ▸ Relation.ReflTransGen.refl

@[simp]
theorem SelfAncestors.self_mem {G : Fin n → Region φ} (i) : i ∈ SelfAncestors G i
  := Relation.ReflTransGen.refl

theorem SelfAncestors.ancestor_or_eq {G : Fin n → Region φ}
  (h : SelfAncestors G i j) : j ∈ Ancestors G i ∨ j = i
  := by induction h with
  | refl => right; rfl
  | tail _ hr Ir => left; cases Ir with
    | inl h => exact h.tail hr
    | inr h => cases h; exact Relation.TransGen.single hr

theorem Ancestors.subset_self_ancestors : Ancestors G i ⊆ SelfAncestors G i := by
  intro j h
  induction h with
  | single hr => exact Relation.ReflTransGen.refl.tail hr
  | tail _ hr I => exact I.tail hr

theorem SelfAncestors.of_ancestor {G : Fin n → Region φ} (h : Ancestors G i j)
  : j ∈ SelfAncestors G i := Ancestors.subset_self_ancestors h

theorem Ancestors.union_singleton_self {G : Fin n → Region φ} (i) :
  Ancestors G i ∪ {i} = SelfAncestors G i := Set.ext λ_ => ⟨
    λh => h.elim SelfAncestors.of_ancestor SelfAncestors.eq_mem,
    λh => h.ancestor_or_eq⟩

theorem SelfAncestors.lt_or_eq {G : Fin n → Region φ} (h : SelfAncestors G i j) : j < n ∨ j = i
  := by cases h with
  | refl => right; rfl
  | tail _ hr => left; exact hr.1

theorem SelfAncestors.comp_vwk (ρ) : SelfAncestors (vwk ρ ∘ G) = SelfAncestors G := by
  simp only [SelfAncestors, Predecessors.comp_vwk]

theorem SelfAncestors.vwk (ρ) : @SelfAncestors n φ (λi => (G i).vwk ρ) = SelfAncestors G
  := comp_vwk ρ

theorem Ancestors.split {G : Fin n → Region φ} (h : Ancestors G i j)
  : ∃k, i ∈ (G k).fl ∧ j ∈ SelfAncestors G k := by
  induction h with
  | single hr => exact ⟨⟨_, hr.1⟩, hr.2, SelfAncestors.self_mem _⟩
  | tail _ hr I =>
    have ⟨k, hki, hkj⟩ := I
    exact ⟨k, hki, hkj.tail hr⟩

theorem Ancestors.of_split {G : Fin n → Region φ} {k}
  (hki : i ∈ (G k).fl) (hkj : j ∈ SelfAncestors G k)
  : Ancestors G i j := by
  induction hkj with
  | refl => exact Relation.TransGen.single ⟨k.prop, hki⟩
  | tail _ hr I => exact I.tail hr

theorem Ancestors.split_iff (G : Fin n → Region φ) (i j)
  : Ancestors G i j ↔ ∃k, i ∈ (G k).fl ∧ j ∈ SelfAncestors G k
  := ⟨Ancestors.split, λ⟨_, hki, hkj⟩ => Ancestors.of_split hki hkj⟩

inductive Acyclic' : Set ℕ → Set (Region φ)
  | br {D ℓ} (h : ℓ ∉ D) e : Acyclic' D (br ℓ e)
  | case e : Acyclic' D s → Acyclic' D t → Acyclic' D (case e s t)
  | let1 e : Acyclic' D s → Acyclic' D (let1 e s)
  | let2 e : Acyclic' D s → Acyclic' D (let2 e s)
  | cfg : Acyclic' ((· + n) '' D) β →
    (∀i : Fin n, Acyclic' ((· + n) '' D ∪ SelfAncestors G i) (G i)) → Acyclic' D (cfg β n G)

@[simp]
theorem Acyclic'.br_iff (D ℓ e) : @Acyclic' φ D (Region.br ℓ e) ↔ ℓ ∉ D
  := ⟨λh => by cases h; assumption, λh => br h _⟩

@[simp]
theorem Acyclic'.case_iff (D e s t) :
  @Acyclic' φ D (Region.case e s t) ↔ Acyclic' D s ∧ Acyclic' D t
  := ⟨λh => by cases h; constructor <;> assumption, λ⟨hs, ht⟩ => case e hs ht⟩

@[simp]
theorem Acyclic'.let1_iff (D e s) : @Acyclic' φ D (Region.let1 e s) ↔ Acyclic' D s
  := ⟨λh => by cases h; assumption, λh => let1 _ h⟩

@[simp]
theorem Acyclic'.let2_iff (D e s) : @Acyclic' φ D (Region.let2 e s) ↔ Acyclic' D s
  := ⟨λh => by cases h; assumption, λh => let2 _ h⟩

@[simp]
theorem Acyclic'.cfg_iff (D β n G) :
  @Acyclic' φ D (Region.cfg β n G) ↔
  Acyclic' ((· + n) '' D) β ∧ (∀i : Fin n, Acyclic' ((· + n) '' D ∪ SelfAncestors G i) (G i))
  := ⟨λh => by cases h; constructor <;> assumption, λ⟨hβ, hG⟩ => cfg hβ hG⟩

theorem Acyclic'.antitone : Antitone (@Acyclic' φ) := by
  intro D' D hD r h
  induction h generalizing D' with
  | br h e => exact br (λc => h (hD c)) e
  | case e _ _ Is It => exact case e (Is hD) (It hD)
  | let1 e _ Ir => exact let1 e (Ir hD)
  | let2 e _ Ir => exact let2 e (Ir hD)
  | cfg _ _ Iβ IG =>
    exact cfg
      (Iβ (Set.image_subset _ hD))
      λi => IG i $ Set.union_subset_union_left _ (Set.image_subset _ hD)

theorem SAcyclic'.acyclic' (h : SAcyclic' D r) : Acyclic' D r := by
  induction h with
  | br h _ => exact Acyclic'.br h _
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
      | inr h => exact h ▸ i.prop

theorem Acyclic'.not_mem_fl (h : Acyclic' D r) : ∀i ∈ D, i ∉ r.fl := by
  intro i hi
  induction h generalizing i with
  | br h _ =>
    intro hi
    cases Multiset.mem_singleton.mp hi
    contradiction
  | case e _ _ Is It =>
    rw [fl, Multiset.mem_add, not_or]
    exact ⟨Is _ hi, It _ hi⟩
  | let1 _ _ Ir => exact Ir i hi
  | let2 _ _ Ir => exact Ir i hi
  | cfg _ _ Iβ IG =>
    rw [fl, Multiset.mem_add, not_or]
    constructor
    rw [Multiset.mem_liftnFv]
    exact Iβ _ ⟨i, hi, rfl⟩
    rw [Multiset.not_mem_finsum_univ]
    intro k
    rw [Multiset.mem_liftnFv]
    apply IG
    simp [hi]

theorem Acyclic'.mem_fl (h : Acyclic' D r) : ∀i ∈ r.fl, i ∉ D
  := λi hi hd => h.not_mem_fl i hd hi

theorem SAcyclic'.not_mem_fl (h : SAcyclic' D r) : ∀i ∈ D, i ∉ r.fl := h.acyclic'.not_mem_fl

theorem SAcyclic'.mem_fl (h : SAcyclic' D r) : ∀i ∈ r.fl, i ∉ D := h.acyclic'.mem_fl

theorem Acyclic'.vwk (ρ) (h : Acyclic' D r) : Acyclic' D (vwk ρ r) := by
  induction h generalizing ρ with
  | cfg _ _ Iβ IG =>
    apply Acyclic'.cfg (Iβ _)
    intro i
    rw [SelfAncestors.vwk]
    apply IG
  | _ => constructor <;> apply_assumption

inductive SAcyclic : Set (Region φ)
  | br ℓ e : SAcyclic (br ℓ e)
  | case e : SAcyclic s → SAcyclic t → SAcyclic (case e s t)
  | let1 e : SAcyclic s → SAcyclic (let1 e s)
  | let2 e : SAcyclic s → SAcyclic (let2 e s)
  | cfg : SAcyclic β →
    (∀i : Fin n, SAcyclic (G i)) →
    (∀i : Fin n, ∀j ∈ Ancestors G i, n ≤ j) → SAcyclic (cfg β n G)

-- TODO: relationship between SAcyclic and SACyclic'

inductive Acyclic : Set (Region φ)
  | br ℓ e : Acyclic (br ℓ e)
  | case e : Acyclic s → Acyclic t → Acyclic (case e s t)
  | let1 e : Acyclic s → Acyclic (let1 e s)
  | let2 e : Acyclic s → Acyclic (let2 e s)
  | cfg : Acyclic β →
    (∀i : Fin n, Acyclic (G i)) →
    (∀i : Fin n, ↑i ∉ Ancestors G i) → Acyclic (cfg β n G)

@[simp]
theorem Acyclic.br_iff (ℓ e) : @Acyclic φ (Region.br ℓ e) ↔ True
  := ⟨λ_ => trivial, λ_ => Acyclic.br ℓ e⟩

@[simp]
theorem Acyclic.case_iff (e s t) : @Acyclic φ (Region.case e s t) ↔ Acyclic s ∧ Acyclic t
  := ⟨λh => by cases h; constructor <;> assumption, λ⟨hs, ht⟩ => case e hs ht⟩

@[simp]
theorem Acyclic.let1_iff (e s) : @Acyclic φ (Region.let1 e s) ↔ Acyclic s
  := ⟨λh => by cases h; assumption, λh => let1 _ h⟩

@[simp]
theorem Acyclic.let2_iff (e s) : @Acyclic φ (Region.let2 e s) ↔ Acyclic s
  := ⟨λh => by cases h; assumption, λh => let2 _ h⟩

theorem Acyclic.not_mem_ancestors' (h : @Acyclic φ (Region.cfg β n G)) :
  ∀i : Fin n, ↑i ∉ Ancestors G i := by cases h; assumption

theorem Acyclic.not_mem_ancestors (h : @Acyclic φ (Region.cfg β n G)) : ∀i, i ∉ Ancestors G i
  := λi hi => h.not_mem_ancestors' ⟨i, hi.lt⟩ hi

@[simp]
theorem Acyclic.cfg_iff (β n G) :
  @Acyclic φ (Region.cfg β n G) ↔
  Acyclic β ∧ (∀i : Fin n, Acyclic (G i)) ∧ (∀i : Fin n, ↑i ∉ Ancestors G i)
  := ⟨λh => by cases h; repeat first | constructor | assumption, λ⟨hβ, hG, hJ⟩ => cfg hβ hG hJ⟩

theorem Acyclic'.acyclic (h : Acyclic' D r) : Acyclic r := by
  induction h with
  | @cfg n _ _ _ _ hG Iβ IG =>
    apply Acyclic.cfg Iβ IG
    intro i hi
    have ⟨k, hik, hki⟩ := hi.split
    apply (hG k).mem_fl _ hik
    simp [hki]
  | _ => constructor <;> assumption

theorem Acyclic'.of_acyclic {r : Region φ} (h : Acyclic r) (hD : ∀x ∈ r.fl, x ∉ D) : Acyclic' D r
  := by
  induction h generalizing D with
  | br => exact Acyclic'.br (hD _ (by simp)) _
  | case e _ _ Is It =>
    exact Acyclic'.case e
      (Is (λi hi => hD i (by simp [hi])))
      (It (λi hi => hD i (by simp [hi])))
  | let1 e _ Is => exact Acyclic'.let1 e (Is (λi hi => hD i (by simp [hi])))
  | let2 e _ Is => exact Acyclic'.let2 e (Is (λi hi => hD i (by simp [hi])))
  | cfg _ _ hG Iβ IG =>
    apply Acyclic'.cfg
    . apply Iβ
      intro i hi
      simp only [Set.mem_image, not_exists, not_and]
      intro j hj hj'
      cases hj'
      apply hD j
      simp [Multiset.mem_liftnFv, hi]
      exact hj
    . intro i
      apply IG
      intro j hj
      simp only [Set.mem_union, Set.mem_image, not_or, not_exists, not_and]
      constructor
      . intro x hx c
        cases c
        apply hD x
        simp only [fl, Multiset.mem_add, Multiset.mem_liftnFv]
        right
        apply (Multiset.mem_finsum _ _ _).mpr
        simp only [Finset.mem_univ, Multiset.mem_liftnFv, true_and]
        exact ⟨_, hj⟩
        exact hx
      . intro c
        have c' := Ancestors.of_split hj c
        apply hG ⟨j, c'.lt⟩ c'

theorem Acyclic'.acyclic_iff (r : Region φ) : Acyclic' D r ↔ Acyclic r ∧ ∀x ∈ r.fl, x ∉ D :=
  ⟨λh => ⟨h.acyclic, h.mem_fl⟩, λ⟨h, h'⟩ => of_acyclic h h'⟩

theorem Acyclic.acyclic_iff (r : Region φ) : Acyclic r ↔ Acyclic' ∅ r := by
  simp [Acyclic'.acyclic_iff]

theorem Acyclic.eq_acyclic : @Acyclic φ = Acyclic' ∅ := Set.ext acyclic_iff

-- TODO: acyclicity is preserved by weakening

-- TODO: acyclicity is preserved by acyclic substitution

-- TODO: strict acyclicity is preserved by weakening

-- TODO: strict acyclicity is preserved by strict acyclic substitution

end Region
