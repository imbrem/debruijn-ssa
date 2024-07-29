import Discretion.Wk.List
import Discretion.Basic
import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Fv.Basic
import DeBruijnSSA.BinSyntax.Syntax.Effect.Definitions
import DeBruijnSSA.BinSyntax.Typing.Ty
import DeBruijnSSA.BinSyntax.Typing.Ctx

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]

abbrev LCtx (α) := List (Ty α)

namespace LCtx

structure Trg (L : LCtx α) (n : ℕ) (A : Ty α) : Prop where
  length : n < L.length
  getElem : A ≤ L[n]

theorem Trg.get (L : LCtx α) {n A} (h : L.Trg n A) : A ≤ L.get ⟨n, h.length⟩ := h.getElem

theorem Trg.get0 (L : LCtx α) {lo hi} (h : LCtx.Trg (hi::L) 0 lo) : lo ≤ hi := h.getElem

instance : Append (LCtx α) := (inferInstance : Append (List (Ty α)))

instance : Membership (Ty α) (LCtx α) := (inferInstance : Membership (Ty α) (List (Ty α)))

def IsInitial (L : LCtx α) : Prop := ∀A ∈ L, Ty.IsInitial A

@[simp]
theorem IsInitial.append (L K : LCtx α) : (L ++ K).IsInitial ↔ L.IsInitial ∧ K.IsInitial
  := ⟨
    λh => ⟨λV hV => h V (List.mem_append_left _ hV), λV hV => h V (List.mem_append_right _ hV)⟩,
    λ⟨h, h'⟩ V hV => (List.mem_append.mp hV).elim (h V) (h' V)⟩

def take (n : ℕ) (L : LCtx α) : LCtx α := List.take n L

def drop (n : ℕ) (L : LCtx α) : LCtx α := List.drop n L

def FLCtx (α) := Σn, Fin n → Ty α

-- TODO: FLCtx append

variable {L K : LCtx α}

def Wkn (L K : LCtx α) (ρ : ℕ → ℕ) : Prop -- TODO: fin argument as defeq?
  := ∀i, (h : i < L.length) → K.Trg (ρ i) L[i]

def InS (L K : LCtx α) : Type _ := {ρ : ℕ → ℕ | L.Wkn K ρ}

instance inSCoe : CoeOut (InS L K) (ℕ → ℕ)
  := ⟨λt => t.val⟩

instance InS.instSetoid : Setoid (InS L K) where
  r ρ σ := ∀i, i < L.length → (ρ : ℕ → ℕ) i = (σ : ℕ → ℕ) i
  iseqv := {
    refl := (λ_ _ _ => rfl)
    symm := (λh i hi => (h i hi).symm)
    trans := (λh h' i hi => (h i hi).trans (h' i hi))
  }

def InS.cast {L L' K K' : LCtx α} (hL : L = L') (hK : K = K') (ρ : L.InS K) : L'.InS K'
  := ⟨ρ, hL ▸ hK ▸ ρ.2⟩

theorem Wkn.id (L : LCtx α) : L.Wkn L id := λ_ hi => ⟨hi, le_refl _⟩

def InS.id (L : LCtx α) : InS L L := ⟨_root_.id, Wkn.id _⟩

@[simp]
theorem InS.coe_id (L : LCtx α) : (InS.id L : ℕ → ℕ) = _root_.id := rfl

theorem Wkn_def : L.Wkn K ρ ↔
  ∀i, (h : i < L.length) → K.Trg (ρ i) L[i] := Iff.rfl

theorem Wkn_def' : L.Wkn K ρ ↔
  ∀i : Fin L.length, K.Trg (ρ i) L[i] := ⟨λh ⟨i, hi⟩ => h i hi, λh i hi => h ⟨i, hi⟩⟩

theorem Wkn_iff : L.Wkn K ρ ↔ @List.NWkn (Ty α)ᵒᵈ _ K L ρ
  := ⟨λh i hi => have h' := h i hi; ⟨h'.length, h'.get⟩, λh i hi => have h' := h i hi; ⟨h'.1, h'.2⟩⟩

theorem Wkn.lift {lo hi : Ty α} (h : lo ≤ hi) (hρ : Wkn L K ρ)
  : Wkn (lo::L) (hi::K) (Nat.liftWk ρ)
  := Wkn_iff.mpr ((Wkn_iff.mp hρ).lift h)

def InS.lift {lo hi : Ty α} (h : lo ≤ hi) (ρ : L.InS K) : InS (lo::L) (hi::K)
  := ⟨Nat.liftWk ρ, ρ.prop.lift h⟩

@[simp]
theorem InS.coe_lift {lo hi : Ty α} (h : lo ≤ hi) (ρ : L.InS K)
  : (ρ.lift h : ℕ → ℕ) = Nat.liftWk ρ := rfl

theorem Wkn.slift {head : Ty α} (hρ : Wkn L K ρ) : Wkn (head::L) (head::K) (Nat.liftWk ρ)
  := hρ.lift (le_refl head)

def InS.slift {head : Ty α} (ρ : L.InS K) : InS (head::L) (head::K)
  := ρ.lift (le_refl head)

@[simp]
theorem InS.coe_slift {head : Ty α} (ρ : L.InS K)
  : (ρ.slift (head := head) : ℕ → ℕ) = Nat.liftWk ρ := rfl

theorem Wkn.step {head : Ty α} (h : L.Wkn K ρ) : Wkn L (head::K) (Nat.stepWk ρ)
  := Wkn_iff.mpr ((Wkn_iff.mp h).step _)

theorem Wkn.liftn_append {L K : LCtx α} {ρ : ℕ → ℕ} (R : LCtx α) (h : L.Wkn K ρ)
  : (R ++ L).Wkn (R ++ K) (Nat.liftnWk R.length ρ) := by
  rw [Wkn_iff]
  apply List.NWkn.liftn_append
  rw [<-Wkn_iff]
  exact h

def InS.liftn_append {L K : LCtx α} (R : LCtx α) : InS L K → InS (R ++ L) (R ++ K)
  := λρ => ⟨Nat.liftnWk R.length ρ, ρ.2.liftn_append R⟩

@[simp]
theorem InS.coe_liftn_append {L K : LCtx α} (R : LCtx α) (ρ : L.InS K)
  : (ρ.liftn_append R : ℕ → ℕ) = Nat.liftnWk R.length ρ := rfl

theorem Wkn.comp {L K J : LCtx α} {ρ σ}
  : K.Wkn J ρ → L.Wkn K σ → L.Wkn J (ρ ∘ σ)
  := by
  simp only [Wkn_iff]
  apply List.NWkn.comp

@[simp]
theorem Wkn.succ {head} {L : LCtx α}
  : Wkn L (head::L) Nat.succ
  := step (head := head) (id (L := L))

def InS.wk0 {head : Ty α} {L : LCtx α} : InS L (head::L)
  := ⟨Nat.succ, Wkn.succ⟩

@[simp]
theorem InS.coe_wk0 {head : Ty α} {L : LCtx α}
  : (InS.wk0 (head := head) (L := L) : ℕ → ℕ) = Nat.succ := rfl

theorem Wkn.wk1 {head inserted : Ty α} {L : LCtx α}
  : Wkn (head::L) (head::inserted::L) (Nat.liftWk Nat.succ)
  := succ.slift

def InS.wk1 {head inserted : Ty α} {L : LCtx α} : InS (head::L) (head::inserted::L)
  := ⟨Nat.liftWk Nat.succ, Wkn.wk1⟩

@[simp]
theorem InS.coe_wk1 {head inserted : Ty α} {L : LCtx α}
  : (InS.wk1 (head := head) (inserted := inserted) (L := L) : ℕ → ℕ) = Nat.liftWk Nat.succ := rfl

def InS.comp {L K J : LCtx α} (ρ : InS K J) (σ : InS L K) : InS L J
  := ⟨(ρ : ℕ → ℕ) ∘ (σ : ℕ → ℕ), ρ.2.comp σ.2⟩

@[simp]
theorem InS.coe_comp {L K J : LCtx α} (ρ : InS K J) (σ : InS L K)
  : (ρ.comp σ : ℕ → ℕ) = (ρ : ℕ → ℕ) ∘ (σ : ℕ → ℕ)
  := rfl

theorem Wkn.add_left_append (original added : LCtx α)
  : original.Wkn (added ++ original) (· + added.length)
  := λi hi => ⟨
    by rw [List.length_append]; simp [i.add_comm, hi],
    by rw [List.getElem_append_right] <;> simp [hi]⟩

def InS.add_left_append (original added : LCtx α) : InS original (added ++ original)
  := ⟨(· + added.length), Wkn.add_left_append original added⟩

@[simp]
theorem InS.coe_add_left_append (original added : LCtx α)
  : (InS.add_left_append original added : ℕ → ℕ) = (· + added.length) := rfl

theorem Trg.wk (h : L.Wkn K ρ) (hK : L.Trg n A) : K.Trg (ρ n) A where
  length := (h n hK.length).1
  getElem := le_trans hK.get (h n hK.length).2

theorem Wkn.toFinWk_append {L L' R S : LCtx α} {ρ : Fin R.length → Fin S.length}
  (hρ : (R ++ L).Wkn (S ++ L') (Fin.toNatWk ρ)) (i : Fin R.length)
  : R[i] ≤ S[ρ i] := by
  have hρ := hρ i (Nat.lt_of_lt_of_le i.prop (by simp));
  rw [List.getElem_append _ (by simp), Fin.toNatWk_coe] at hρ
  have hρ := hρ.getElem
  rw [List.getElem_append _ (by simp)] at hρ
  simp [hρ]

theorem Trg.head (h : A' ≤ A) (L : LCtx α) : Trg (A::L) 0 A' where
  length := by simp
  getElem := h

@[simp]
theorem Trg.head_iff {A A' : Ty α} {L : LCtx α} : Trg (A::L) 0 A' ↔ A' ≤ A
  := ⟨λh => h.getElem, λh => Trg.head h L⟩

theorem Trg.shead {head} : Trg (head::L) 0 head := Trg.head (le_refl _) L

theorem Trg.step {n} {A : Ty α} (h : L.Trg n A) : Trg (B::L) (n + 1) A
  := ⟨by simp [h.length], h.getElem⟩

theorem Trg.tail {n} {A : Ty α} (h : Trg (B::L) (n + 1) A) : Trg L n A
  := ⟨Nat.lt_of_succ_lt_succ h.length, h.getElem⟩

theorem Trg.of_add {n} {A : Ty α} (h : Trg (R ++ L) (n + R.length) A) : Trg L n A
  := by induction R with
  | nil => exact h
  | cons A R ih => exact ih h.tail

theorem Trg.of_ge {n} {A : Ty α} (h : Trg (R ++ L) n A) (hn : R.length ≤ n) : Trg L (n - R.length) A
  := have hn' : n = (n - R.length) + R.length := by omega;
  (hn' ▸ h).of_add

@[simp]
theorem Trg.of_le_getElem {n} {L : LCtx α} (hn : n < L.length) (hn' : A ≤ L[n]) : Trg L n A
  := ⟨hn, hn'⟩

@[simp]
theorem Trg.of_getElem {n} {L : LCtx α} (hn : n < L.length) : Trg L n L[n]
  := ⟨hn, le_refl _⟩

@[simp]
theorem Trg.step_iff {n} {A : Ty α} {L : LCtx α} : Trg (B::L) (n + 1) A ↔ Trg L n A
  := ⟨λh => h.tail, λh => h.step⟩

theorem Trg.rec_to_wkn_id {L R : LCtx α} {ℓ} {A : Ty α} (h : Trg (R ++ L) ℓ A) (hℓ : ℓ < R.length)
  {Γ : Ctx α ε} : Ctx.Wkn ((A, ⊥)::Γ) ((R.get ⟨ℓ, hℓ⟩, ⊥)::Γ) _root_.id
  := Ctx.Wkn.id.lift_id ⟨by
    have h' := h.getElem;
    rw [List.getElem_append_left] at h';
    exact h', le_refl _⟩

def shf_first (R : LCtx α) (Y : Ty α) (L : LCtx α) : Ty α
  := (R ++ (Y::L))[0]

def shf_rest (R : LCtx α) (Y : Ty α) (L : LCtx α) : LCtx α
  := (R ++ (Y::L)).drop 1

theorem shf_eq {R : LCtx α} {Y : Ty α} {L : LCtx α}
  : (R ++ (Y::L)) = (shf_first R Y L)::(shf_rest R Y L)
  := by cases R <;> rfl

@[simp]
theorem length_shf_rest {R : LCtx α} {Y : Ty α} {L : LCtx α}
  : (shf_rest R Y L).length = R.length + L.length
  := by simp [shf_rest, drop, List.length_drop]

@[simp]
theorem getElem_shf_rest_add {R : LCtx α} {Y : Ty α} {L : LCtx α} {n}
  {hn : n + R.length < (shf_rest R Y L).length}
  : (shf_rest R Y L)[n + R.length] = L[n]'(by simp at hn; omega)
  := by cases R with
  | nil => rfl
  | cons X R =>
    simp only [shf_rest, drop, List.cons_append, List.drop_succ_cons, List.drop_zero,
      List.length_cons, Nat.add_comm R.length 1, <-Nat.add_assoc]
    rw [List.getElem_append_right]
    simp only [Nat.add_sub_cancel]
    simp
    omega
    simp at hn
    simp only [add_tsub_cancel_right, List.length_cons, add_lt_add_iff_right]
    omega

theorem Wkn.shf {R : LCtx α} {Y : Ty α} {L : LCtx α}
  : LCtx.Wkn L (shf_rest R Y L) (· + R.length)
  := λi hi => ⟨by simp only [length_shf_rest]; omega, by simp⟩

def InS.shf {R : LCtx α} {Y : Ty α} {L : LCtx α} : L.InS (shf_rest R Y L)
  := ⟨(· + R.length), Wkn.shf⟩

@[simp]
theorem InS.coe_shf {R : LCtx α} {Y : Ty α} {L : LCtx α}
  : (InS.shf (R := R) (Y := Y) (L := L) : ℕ → ℕ) = (· + R.length) := rfl
