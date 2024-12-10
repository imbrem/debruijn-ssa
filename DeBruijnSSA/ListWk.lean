import Discretion.Wk.List

/-- The function `ρ` sends `Γ` to `Δ` -/
def List.NEWkn (Γ Δ : List α) (ρ : ℕ → ℕ) : Prop
  := ∀n, (hΔ : n < Δ.length) → ∃hΓ : ρ n < Γ.length, Γ[ρ n] = Δ[n]

theorem List.NEWkn.bounded {ρ : ℕ → ℕ} (h : List.NEWkn Γ Δ ρ) (n : ℕ) (hΔ : n < Δ.length)
  : ρ n < Γ.length := match h n hΔ with | ⟨hΓ, _⟩ => hΓ

def List.NEWkn.toFinWk {ρ : ℕ → ℕ} (h : List.NEWkn Γ Δ ρ) : Fin (Δ.length) → Fin (Γ.length)
  := Fin.wkOfBounded ρ h.bounded

-- theorem List.NEWkn.toIsFWk (Γ Δ : List α) (ρ : ℕ → ℕ)
--   (h : List.NEWkn Γ Δ ρ) : List.IsFWk Γ Δ (List.NEWkn.toFinWk h)
--   := funext λ⟨i, hi⟩ => have ⟨_, h⟩ := h i hi; h

-- ... TODO: NEWkns

@[simp]
theorem List.NEWkn.id (Γ : List α) : List.NEWkn Γ Γ id
  := λ_ hΓ => ⟨hΓ, rfl⟩

-- ... TODO: len_le

@[simp]
theorem List.NEWkn.drop_all (Γ : List α) (ρ) : List.NEWkn Γ [] ρ
  := λi h => by cases h

theorem List.NEWkn.comp {ρ : ℕ → ℕ} {σ : ℕ → ℕ} (hρ : List.NEWkn Γ Δ ρ) (hσ : List.NEWkn Δ Ξ σ)
  : List.NEWkn Γ Ξ (ρ ∘ σ) := λn hΞ =>
    have ⟨hΔ, hσ⟩ := hσ n hΞ;
    have ⟨hΓ, hρ⟩ := hρ _ hΔ;
    ⟨hΓ, hρ ▸ hσ⟩

theorem List.NEWkn.lift {ρ : ℕ → ℕ} (hρ : List.NEWkn Γ Δ ρ)
  : List.NEWkn (A :: Γ) (A :: Δ) (Nat.liftWk ρ) := λn hΔ => match n with
  | 0 => ⟨Nat.zero_lt_succ _, rfl⟩
  | n+1 => have ⟨hΔ, hρ⟩ := hρ n (Nat.lt_of_succ_lt_succ hΔ); ⟨Nat.succ_lt_succ hΔ, hρ⟩

theorem List.NEWkn.lift_tail {ρ : ℕ → ℕ} (h : List.NEWkn (A :: Γ) (B :: Δ) (Nat.liftWk ρ))
    : List.NEWkn Γ Δ ρ
  := λi hΔ => have ⟨hΔ, hρ⟩ := h i.succ (Nat.succ_lt_succ hΔ); ⟨Nat.lt_of_succ_lt_succ hΔ, hρ⟩

theorem List.NEWkn.lift_head {ρ : ℕ → ℕ} (h : List.NEWkn (A :: Γ) (B :: Δ) (Nat.liftWk ρ)) : A = B
  := (h 0 (Nat.zero_lt_succ _)).2

theorem List.NEWkn.lift_iff (A B) (Γ Δ : List α) (ρ : ℕ → ℕ)
  : List.NEWkn (A :: Γ) (B :: Δ) (Nat.liftWk ρ) ↔ A = B ∧ List.NEWkn Γ Δ ρ
  := ⟨
    λh => ⟨h.lift_head, List.NEWkn.lift_tail h⟩,
    λ⟨rfl, hρ⟩ => List.NEWkn.lift hρ
  ⟩

theorem List.NEWkn.lift_id (hρ : List.NEWkn Γ Δ _root_.id)
  : List.NEWkn (A :: Γ) (A :: Δ) _root_.id := Nat.liftWk_id ▸ hρ.lift

theorem List.NEWkn.lift_id_tail (h : List.NEWkn (left :: Γ) (right :: Δ) _root_.id)
    : List.NEWkn Γ Δ _root_.id
  := (Nat.liftWk_id ▸ h).lift_tail

theorem List.NEWkn.lift_id_head (h : List.NEWkn (left :: Γ) (right :: Δ) _root_.id)
  : left = right
  := (Nat.liftWk_id ▸ h).lift_head

theorem List.NEWkn.lift_id_iff (h : List.NEWkn (left :: Γ) (right :: Δ) _root_.id)
  : left = right ∧ List.NEWkn Γ Δ _root_.id
  := ⟨h.lift_id_head, h.lift_id_tail⟩

theorem List.NEWkn.lift₂ {ρ : ℕ → ℕ} (hρ : List.NEWkn Γ Δ ρ)
    : List.NEWkn (A₁ :: A₂ :: Γ) (A₁ :: A₂ :: Δ) (Nat.liftWk (Nat.liftWk ρ))
  := hρ.lift.lift

theorem List.NEWkn.liftn₂ {ρ : ℕ → ℕ} (hρ : List.NEWkn Γ Δ ρ)
    : List.NEWkn (A₁ :: A₂ :: Γ) (A₁ :: A₂ :: Δ) (Nat.liftnWk 2 ρ)
  := by rw [Nat.liftnWk_two]; exact hρ.lift₂

theorem List.NEWkn.liftn_append {ρ : ℕ → ℕ} (Ξ : List α) (hρ : List.NEWkn Γ Δ ρ)
    : List.NEWkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk Ξ.length ρ) := by
  induction Ξ with
  | nil => exact hρ
  | cons A Ξ I =>
    rw [List.length, Nat.liftnWk_succ']
    exact I.lift

theorem List.NEWkn.liftn_append' {ρ : ℕ → ℕ} (Ξ : List α) (hΞ : Ξ.length = n)
  (hρ : List.NEWkn Γ Δ ρ) : List.NEWkn (Ξ ++ Γ) (Ξ ++ Δ) (Nat.liftnWk n ρ) := hΞ ▸ hρ.liftn_append Ξ

theorem List.NEWkn.step {ρ : ℕ → ℕ} (A : α) (hρ : List.NEWkn Γ Δ ρ)
    : List.NEWkn (A :: Γ) Δ (Nat.succ ∘ ρ)
  := λn hΔ => have ⟨hΔ, hρ⟩ := hρ n hΔ; ⟨Nat.succ_lt_succ hΔ, hρ⟩

@[simp]
theorem List.NEWkn.succ (A : α) : List.NEWkn (A :: Γ) Γ .succ := step (ρ := _root_.id) A (id _)

theorem List.NEWkn.step_tail {ρ : ℕ → ℕ} (h : List.NEWkn (A :: Γ) Δ (Nat.succ ∘ ρ)) : List.NEWkn Γ Δ ρ
  := λi hΔ => have ⟨hΔ, hρ⟩ := h i hΔ; ⟨Nat.lt_of_succ_lt_succ hΔ, hρ⟩

theorem List.NEWkn.step_iff (A) (Γ Δ : List α) (ρ : ℕ → ℕ)
  : List.NEWkn (A :: Γ) Δ (Nat.succ ∘ ρ) ↔ List.NEWkn Γ Δ ρ
  := ⟨
    List.NEWkn.step_tail,
    List.NEWkn.step A
  ⟩

theorem List.NEWkn.stepn_append {ρ : ℕ → ℕ} (Ξ : List α) (hρ : List.NEWkn Γ Δ ρ)
    : List.NEWkn (Ξ ++ Γ) Δ (Nat.stepnWk Ξ.length ρ)
  := by induction Ξ with
    | nil => exact hρ
    | cons A Ξ I =>
      rw [List.length, Nat.stepnWk_succ']
      exact I.step _

theorem List.NEWkn.stepn_append' {ρ : ℕ → ℕ} (Ξ : List α) (hΞ : Ξ.length = n)
  (hρ : List.NEWkn Γ Δ ρ) : List.NEWkn (Ξ ++ Γ) Δ (Nat.stepnWk n ρ) := hΞ ▸ hρ.stepn_append Ξ

theorem List.NEWkn.toNWkn [PartialOrder α] (Γ Δ : List α) (ρ : ℕ → ℕ)
  (h : List.NEWkn Γ Δ ρ) : List.NWkn Γ Δ ρ
  := λn hΔ => match h n hΔ with | ⟨hΓ, h⟩ => ⟨hΓ, le_of_eq h⟩
