import Discretion.Wk.List
import Discretion.Basic
import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Fv.Basic
import DeBruijnSSA.BinSyntax.Syntax.Effect.Definitions
import DeBruijnSSA.BinSyntax.Typing.Ty

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]

abbrev LCtx (α) := List (Ty α)

structure LCtx.Trg (L : LCtx α) (n : ℕ) (A : Ty α) : Prop where
  length : n < L.length
  getElem : A ≤ L[n]

def LCtx.Trg.get (L : LCtx α) {n A} (h : L.Trg n A) : A ≤ L.get ⟨n, h.length⟩ := h.getElem

instance : Append (LCtx α) := (inferInstance : Append (List (Ty α)))

instance : Membership (Ty α) (LCtx α) := (inferInstance : Membership (Ty α) (List (Ty α)))

def LCtx.IsInitial (L : LCtx α) : Prop := ∀A ∈ L, Ty.IsInitial A

@[simp]
theorem LCtx.IsInitial.append (L K : LCtx α) : (L ++ K).IsInitial ↔ L.IsInitial ∧ K.IsInitial
  := ⟨
    λh => ⟨λV hV => h V (List.mem_append_left _ hV), λV hV => h V (List.mem_append_right _ hV)⟩,
    λ⟨h, h'⟩ V hV => (List.mem_append.mp hV).elim (h V) (h' V)⟩

def LCtx.take (n : ℕ) (L : LCtx α) : LCtx α := List.take n L

def LCtx.drop (n : ℕ) (L : LCtx α) : LCtx α := List.drop n L

def FLCtx (α) := Σn, Fin n → Ty α

-- TODO: FLCtx append

variable {L K : LCtx α}

def LCtx.Wkn (L K : LCtx α) (ρ : ℕ → ℕ) : Prop -- TODO: fin argument as defeq?
  := ∀i, (h : i < L.length) → K.Trg (ρ i) L[i]

def LCtx.InS (L K : LCtx α) : Type _ := {ρ : ℕ → ℕ | L.Wkn K ρ}

instance LCtx.inSCoe : CoeOut (LCtx.InS L K) (ℕ → ℕ)
  := ⟨λt => t.val⟩

instance LCtx.InS.instSetoid : Setoid (LCtx.InS L K) where
  r ρ σ := ∀i, i < L.length → (ρ : ℕ → ℕ) i = (σ : ℕ → ℕ) i
  iseqv := {
    refl := (λ_ _ _ => rfl)
    symm := (λh i hi => (h i hi).symm)
    trans := (λh h' i hi => (h i hi).trans (h' i hi))
  }

def LCtx.InS.cast {L L' K K' : LCtx α} (hL : L = L') (hK : K = K') (ρ : L.InS K) : L'.InS K'
  := ⟨ρ, hL ▸ hK ▸ ρ.2⟩

theorem LCtx.Wkn.id (L : LCtx α) : L.Wkn L id := λ_ hi => ⟨hi, le_refl _⟩

def LCtx.InS.id (L : LCtx α) : InS L L := ⟨_root_.id, Wkn.id _⟩

theorem LCtx.Wkn_def (L K : LCtx α) (ρ : ℕ → ℕ) : L.Wkn K ρ ↔
  ∀i, (h : i < L.length) → K.Trg (ρ i) L[i] := Iff.rfl

theorem LCtx.Wkn_def' (L K : LCtx α) (ρ : ℕ → ℕ) : L.Wkn K ρ ↔
  ∀i : Fin L.length, K.Trg (ρ i) L[i] := ⟨λh ⟨i, hi⟩ => h i hi, λh i hi => h ⟨i, hi⟩⟩

theorem LCtx.Wkn_iff (L K : LCtx α) (ρ : ℕ → ℕ) : L.Wkn K ρ ↔ @List.NWkn (Ty α)ᵒᵈ _ K L ρ
  := ⟨λh i hi => have h' := h i hi; ⟨h'.length, h'.get⟩, λh i hi => have h' := h i hi; ⟨h'.1, h'.2⟩⟩

theorem LCtx.Wkn.step {A : Ty α} (h : L.Wkn K ρ) : Wkn L (A::K) (Nat.stepWk ρ)
  := (Wkn_iff _ _ _).mpr (((Wkn_iff _ _ _).mp h).step _)

theorem LCtx.Wkn.liftn_append {L K : LCtx α} {ρ : ℕ → ℕ} (R : LCtx α) (h : L.Wkn K ρ)
  : (R ++ L).Wkn (R ++ K) (Nat.liftnWk R.length ρ) := by
  rw [LCtx.Wkn_iff]
  apply List.NWkn.liftn_append
  rw [<-LCtx.Wkn_iff]
  exact h

theorem LCtx.Wkn.comp {L K J : LCtx α} {ρ σ}
  : K.Wkn J ρ → L.Wkn K σ → L.Wkn J (ρ ∘ σ)
  := by
  simp only [LCtx.Wkn_iff]
  apply List.NWkn.comp

def LCtx.InS.comp {L K J : LCtx α} (ρ : LCtx.InS K J) (σ : LCtx.InS L K) : LCtx.InS L J
  := ⟨(ρ : ℕ → ℕ) ∘ (σ : ℕ → ℕ), ρ.2.comp σ.2⟩

@[simp]
theorem LCtx.InS.coe_comp {L K J : LCtx α} (ρ : LCtx.InS K J) (σ : LCtx.InS L K)
  : (ρ.comp σ : ℕ → ℕ) = (ρ : ℕ → ℕ) ∘ (σ : ℕ → ℕ)
  := rfl

theorem LCtx.Wkn.add_left_append (original added : LCtx α)
  : original.Wkn (added ++ original) (· + added.length)
  := λi hi => ⟨
    by rw [List.length_append]; simp [i.add_comm, hi],
    by rw [List.getElem_append_right] <;> simp [hi]⟩

def LCtx.InS.add_left_append (original added : LCtx α) : InS original (added ++ original)
  := ⟨(· + added.length), Wkn.add_left_append original added⟩

theorem LCtx.Trg.wk (h : L.Wkn K ρ) (hK : L.Trg n A) : K.Trg (ρ n) A where
  length := (h n hK.length).1
  getElem := le_trans hK.get (h n hK.length).2

theorem LCtx.Wkn.toFinWk_append {L L' R S : LCtx α} {ρ : Fin R.length → Fin S.length}
  (hρ : (R ++ L).Wkn (S ++ L') (Fin.toNatWk ρ)) (i : Fin R.length)
  : R[i] ≤ S[ρ i] := by
  have hρ := hρ i (Nat.lt_of_lt_of_le i.prop (by simp));
  rw [List.getElem_append _ (by simp), Fin.toNatWk_coe] at hρ
  have hρ := hρ.getElem
  rw [List.getElem_append _ (by simp)] at hρ
  simp [hρ]
