import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.CategoryTheory.PathCategory

import Discretion.Correspondence.Definitions

import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Effect.Subst

namespace BinSyntax

variable {φ : Type u} {ε : Type v} [Φ: EffectSet φ ε] [SemilatticeSup ε] [OrderBot ε]

-- TODO: define as Subst.cons or smt...
def Term.subst₂ (a b: Term φ) : Subst φ
  | 0 => a
  | 1 => b
  | n + 2 => Term.var n

namespace Region

open Term

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
    RewriteD (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk (· + 2) ∘ G))
  | cfg_case (e r s n G) :
    RewriteD (cfg (case e r s) n G)
      (case e (cfg r n (vwk Nat.succ ∘ G)) (cfg s n (vwk Nat.succ ∘ G)))
  | cfg_cfg (β n G n' G') :
    RewriteD (cfg (cfg β n G) n' G') (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
  | cfg_zero (β G) : RewriteD (cfg β 0 G) β
  | cfg_fuse (β n G k) (ρ : Fin k → Fin n) (hρ : Function.Surjective ρ) :
    RewriteD
      (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
      (cfg β k (G ∘ ρ))
  | let2_eta (r : Region φ) :
    RewriteD (let2 (Term.var 0) (let1 ((Term.var 1).pair (Term.var 0)) r.vwk1.vwk1))
      (let1 (Term.var 0) r)
  -- | let1_eta r :
  --   RewriteD (let1 (Term.var 0) r.vwk1) r

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
    rw [
      Nat.liftnBot_two_apply, <-Nat.liftnBot_two_apply, Function.comp_apply, effect_liftnBot_vwk_add
    ]
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

def ReduceD.cast_trg {r₀ r₁ r₁' : Region φ} (p : ReduceD r₀ r₁) (h : r₁ = r₁')
  : ReduceD r₀ r₁' := h ▸ p

def ReduceD.cast_src {r₀ r₀' r₁ : Region φ} (h : r₀' = r₀) (p : ReduceD r₀ r₁)
  : ReduceD r₀' r₁ := h ▸ p

def ReduceD.cast {r₀ r₀' r₁ r₁' : Region φ} (h₀ : r₀ = r₀') (h₁ : r₁ = r₁')
  (p : ReduceD r₀ r₁) : ReduceD r₀' r₁' := h₁ ▸ h₀ ▸ p

inductive StepD (Γ : ℕ → ε) : Region φ → Region φ → Type _
  | let1_beta (e r) : e.effect Γ = ⊥ → StepD Γ (let1 e r) (r.vsubst e.subst0)
  | reduce {r r'} : ReduceD r r' → StepD Γ r r'
  | rw {r r'} : RewriteD r r' → StepD Γ r r'
  | rw_op {r r'} : RewriteD r r' → StepD Γ r' r

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
  : StepD Γ (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk (· + 2) ∘ G))
  := StepD.rw $ RewriteD.cfg_let2 a β n G

@[match_pattern]
def StepD.cfg_let2_op {Γ : ℕ → ε} (a : Term φ) (β n G)
  : StepD Γ (let2 a $ cfg β n (vwk (· + 2) ∘ G))
    (cfg (let2 a β) n G)
  := StepD.rw_op $ RewriteD.cfg_let2 a β n G

@[match_pattern]
def StepD.cfg_case {Γ : ℕ → ε} (e : Term φ) (r s n G)
  : StepD Γ (cfg (case e r s) n G)
    (case e (cfg r n (vwk Nat.succ ∘ G)) (cfg s n (vwk Nat.succ ∘ G))
  )
  := StepD.rw $ RewriteD.cfg_case e r s n G

@[match_pattern]
def StepD.cfg_case_op {Γ : ℕ → ε} (e : Term φ) (r s n G)
  : StepD Γ (case e (cfg r n (vwk Nat.succ ∘ G)) (cfg s n (vwk Nat.succ ∘ G)))
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
def StepD.let2_eta {Γ : ℕ → ε} (r : Region φ)
  : StepD Γ (let2 (var 0) (let1 ((var 1).pair (var 0)) r.vwk1.vwk1)) (let1 (var 0) r)
  := StepD.rw $ RewriteD.let2_eta r

@[match_pattern]
def StepD.let2_eta_op {Γ : ℕ → ε} (r : Region φ)
  : StepD Γ (let1 (var 0) r) (let2 (var 0) (let1 ((var 1).pair (var 0)) r.vwk1.vwk1))
  := StepD.rw_op $ RewriteD.let2_eta r

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

-- TODO: StepD is effect monotonic

inductive SCongD (P : Region φ → Region φ → Type _) : Region φ → Region φ → Type _
  | step : P r r' → SCongD P r r'
  | let1 (e) : SCongD P r r' → SCongD P (let1 e r) (let1 e r')
  | let2 (e) : SCongD P r r' → SCongD P (let2 e r) (let2 e r')
  | case_left (e) : SCongD P r r' → (s : Region φ)
    → SCongD P (case e r s) (case e r' s)
  | case_right (e r) : SCongD P s s' → SCongD P (case e r s) (case e r s')
  | cfg_entry
    : SCongD P r r' → (n : _) → (G : _) → SCongD P (cfg r n G) (cfg r' n G)
  | cfg_block (β n G i) : SCongD P (G i) g' →
    SCongD P (cfg β n G) (cfg β n (Function.update G i g'))

def SCongD.cast_trg {P : Region φ → Region φ → Type _}
  {r₀ r₁ r₁' : Region φ} (p : SCongD P r₀ r₁) (h : r₁ = r₁')
  : SCongD P r₀ r₁' := h ▸ p

def SCongD.cast_src {P : Region φ → Region φ → Type _}
  {r₀ r₀' r₁ : Region φ} (h : r₀' = r₀) (p : SCongD P r₀ r₁)
  : SCongD P r₀' r₁ := h ▸ p

def SCongD.cast {P : Region φ → Region φ → Type _}
  {r₀ r₀' r₁ r₁' : Region φ} (h₀ : r₀ = r₀') (h₁ : r₁ = r₁')
  (p : SCongD P r₀ r₁) : SCongD P r₀' r₁' := h₁ ▸ h₀ ▸ p

def SCongD.cfg_block' {P : Region φ → Region φ → Type _}
  (β n G i) (p : SCongD P g g')
  : SCongD P (cfg β n (Function.update G i g)) (cfg β n (Function.update G i g'))
  := (SCongD.cfg_block β n (Function.update G i g) i (by simp only [Function.update_same]; exact p)
    ).cast_trg (by simp)

-- TODO: SCongD is effect monotone/antitone iff underlying is
-- ==> SCongD is effect preserving iff underlying is

inductive BCongD (P : (ℕ → ε) → Region φ → Region φ → Type _)
  : (ℕ → ε) → Region φ → Region φ → Type _
  | step : P Γ r r' → BCongD P Γ r r'
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
  := single $ BCongD.step $ StepD.let1_beta e r h

def RWD.case_inl {Γ : ℕ → ε} (e) (r s : Region φ)
  : RWD StepD Γ (case (inl e) r s) (let1 e r)
  := single $ BCongD.step $ StepD.case_inl e r s

def RWD.case_inr {Γ : ℕ → ε} (e) (r s : Region φ)
  : RWD StepD Γ (case (inr e) r s) (let1 e s)
  := single $ BCongD.step $ StepD.case_inr e r s

def RWD.let1_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : RWD StepD Γ (let1 (op f e) r) (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := single $ BCongD.step $ StepD.let1_op f e r

def RWD.let1_op_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : RWD StepD Γ (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (op f e) r)
  := single $ BCongD.step $ StepD.let1_op_op f e r

def RWD.let1_pair {Γ : ℕ → ε} (a b) (r : Region φ)
  : RWD StepD Γ (let1 (pair a b) r)
    (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) r.vwk1.vwk1
  )
  := single $ BCongD.step $ StepD.let1_pair a b r

def RWD.let1_pair_op {Γ : ℕ → ε} (a b) (r : Region φ)
  : RWD StepD Γ (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) r.vwk1.vwk1)
    (let1 (pair a b) r)
  := single $ BCongD.step $ StepD.let1_pair_op a b r

def RWD.let1_inl {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 (inl e) r) (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := single $ BCongD.step $ StepD.let1_inl e r

def RWD.let1_inl_op {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (inl e) r)
  := single $ BCongD.step $ StepD.let1_inl_op e r

def RWD.let1_inr {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 (inr e) r) (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := single $ BCongD.step $ StepD.let1_inr e r

def RWD.let1_inr_op {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (inr e) r)
  := single $ BCongD.step $ StepD.let1_inr_op e r

def RWD.let1_abort {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 (abort e) r) (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := single $ BCongD.step $ StepD.let1_abort e r

def RWD.let1_abort_op {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (abort e) r)
  := single $ BCongD.step $ StepD.let1_abort_op e r

def RWD.let2_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : RWD StepD Γ (let2 (op f e) r) (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := single $ BCongD.step $ StepD.let2_op f e r

def RWD.let2_op_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : RWD StepD Γ (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
    (let2 (op f e) r)
  := single $ BCongD.step $ StepD.let2_op_op f e r

def RWD.let2_pair {Γ : ℕ → ε} (a b) (r : Region φ)
  : RWD StepD Γ (let2 (pair a b) r) (let1 a $ let1 (b.wk Nat.succ) $ r)
  := single $ BCongD.step (StepD.let2_pair a b r)

def RWD.let2_pair_op {Γ : ℕ → ε} (a b) (r : Region φ)
  : RWD StepD Γ (let1 a $ let1 (b.wk Nat.succ) $ r)
    (let2 (pair a b) r)
  := single $ BCongD.step $ StepD.let2_pair_op a b r

def RWD.let2_abort {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let2 (abort e) r) (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := single $ BCongD.step $ StepD.let2_abort e r

def RWD.let2_abort_op {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
    (let2 (abort e) r)
  := single $ BCongD.step $ StepD.let2_abort_op e r

def RWD.case_op {Γ : ℕ → ε} (f e) (r s : Region φ)
  : RWD StepD Γ (case (op f e) r s)
    (let1 e $ case (op f (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ))
  )
  := single $ BCongD.step $ StepD.case_op f e r s

def RWD.case_op_op {Γ : ℕ → ε} (f e) (r s : Region φ)
  : RWD StepD Γ (let1 e $ case (op f (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ)))
    (case (op f e) r s)
  := single $ BCongD.step $ StepD.case_op_op f e r s

def RWD.case_abort {Γ : ℕ → ε} (e) (r s : Region φ)
  : RWD StepD Γ (case (abort e) r s)
    (let1 e $ case (abort (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ))
  )
  := single $ BCongD.step $ StepD.case_abort e r s

def RWD.case_abort_op {Γ : ℕ → ε} (e) (r s : Region φ)
  : RWD StepD Γ (let1 e $ case (abort (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ)))
    (case (abort e) r s)
  := single $ BCongD.step $ StepD.case_abort_op e r s

def RWD.let1_case {Γ : ℕ → ε} (a b) (r s : Region φ)
  : RWD StepD Γ (let1 a $ case (b.wk Nat.succ) r s)
    (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
  := single $ BCongD.step $ StepD.let1_case a b r s

def RWD.let1_case_op {Γ : ℕ → ε} (a b) (r s : Region φ)
  : RWD StepD Γ (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
    (let1 a $ case (b.wk Nat.succ) r s)
  := single $ BCongD.step $ StepD.let1_case_op a b r s

def RWD.let2_case {Γ : ℕ → ε} (a b) (r s : Region φ)
  : RWD StepD Γ (let2 a $ case (b.wk (· + 2)) r s)
    (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
  := single $ BCongD.step $ StepD.let2_case a b r s

def RWD.let2_case_op {Γ : ℕ → ε} (a b) (r s : Region φ)
  : RWD StepD Γ (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
    (let2 a $ case (b.wk (· + 2)) r s)
  := single $ BCongD.step $ StepD.let2_case_op a b r s

def RWD.cfg_br_lt {Γ : ℕ → ε} (ℓ) (e : Term φ) (n G) (h : ℓ < n)
  : RWD StepD Γ (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).let1 e) n G)
  := single $ BCongD.step $ StepD.cfg_br_lt ℓ e n G h

def RWD.cfg_br_lt_op {Γ : ℕ → ε} (ℓ) (e : Term φ) (n G) (h : ℓ < n)
  : RWD StepD Γ (cfg ((G ⟨ℓ, h⟩).let1 e) n G) (cfg (br ℓ e) n G)
  := single $ BCongD.step $ StepD.cfg_br_lt_op ℓ e n G h

def RWD.cfg_let1 {Γ : ℕ → ε} (a : Term φ) (β n G)
  : RWD StepD Γ (cfg (let1 a β) n G) (let1 a $ cfg β n (vwk1 ∘ G))
  := single $ BCongD.step $ StepD.cfg_let1 a β n G

def RWD.cfg_let1_op {Γ : ℕ → ε} (a : Term φ) (β n G)
  : RWD StepD Γ (let1 a $ cfg β n (vwk1 ∘ G))
    (cfg (let1 a β) n G)
  := single $ BCongD.step $ StepD.cfg_let1_op a β n G

def RWD.cfg_let2 {Γ : ℕ → ε} (a : Term φ) (β n G)
  : RWD StepD Γ (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk (· + 2) ∘ G))
  := single $ BCongD.step $ StepD.cfg_let2 a β n G

def RWD.cfg_let2_op {Γ : ℕ → ε} (a : Term φ) (β n G)
  : RWD StepD Γ (let2 a $ cfg β n (vwk (· + 2) ∘ G))
    (cfg (let2 a β) n G)
  := single $ BCongD.step $ StepD.cfg_let2_op a β n G

def RWD.cfg_case {Γ : ℕ → ε} (e : Term φ) (r s n G)
  : RWD StepD Γ (cfg (case e r s) n G)
    (case e (cfg r n (vwk Nat.succ ∘ G)) (cfg s n (vwk Nat.succ ∘ G))
  )
  := single $ BCongD.step $ StepD.cfg_case e r s n G

def RWD.cfg_case_op {Γ : ℕ → ε} (e : Term φ) (r s n G)
  : RWD StepD Γ (case e (cfg r n (vwk Nat.succ ∘ G)) (cfg s n (vwk Nat.succ ∘ G)))
    (cfg (case e r s) n G)
  := single $ BCongD.step $ StepD.cfg_case_op e r s n G

def RWD.cfg_cfg {Γ : ℕ → ε} (β : Region φ) (n G n' G')
  : RWD StepD Γ (cfg (cfg β n G) n' G') (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
  := single $ BCongD.step $ StepD.cfg_cfg β n G n' G'

def RWD.cfg_cfg_op {Γ : ℕ → ε} (β : Region φ) (n G n' G')
  : RWD StepD Γ (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
    (cfg (cfg β n G) n' G')
  := single $ BCongD.step $ StepD.cfg_cfg_op β n G n' G'

def RWD.cfg_zero {Γ : ℕ → ε} (β : Region φ) (G)
  : RWD StepD Γ (cfg β 0 G) β := single $ BCongD.step $ StepD.cfg_zero β G

def RWD.cfg_zero_op {Γ : ℕ → ε} (β : Region φ) (G)
  : RWD StepD Γ β (cfg β 0 G) := single $ BCongD.step $ StepD.cfg_zero_op β G

def RWD.wk_cfg {Γ : ℕ → ε} (β : Region φ) (n G k) (ρ : Fin k → Fin n) /-(hρ : Function.Bijective ρ)-/
  : RWD StepD Γ
    (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
    (cfg β k (G ∘ ρ))
  := single $ BCongD.step $ StepD.wk_cfg β n G k ρ

def RWD.dead_cfg_left {Γ : ℕ → ε} (β : Region φ) (n G m G')
  : RWD StepD Γ
    (cfg (β.lwk (· + n)) (n + m) (Fin.addCases G (lwk (· + n) ∘ G')))
    (cfg β m G')
  := single $ BCongD.step $ StepD.dead_cfg_left β n G m G'

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
    (let2 (Term.var 0) $
     let1 ((Term.var 1).pair (Term.var 0)) $
     r.vwk1.vwk1) (let1 (Term.var 0) r)
  := single $ BCongD.step $ StepD.let2_eta r

def RWD.let2_eta_op {Γ : ℕ → ε} (r : Region φ)
  : RWD StepD Γ (let1 (Term.var 0) r)
    (let2 (Term.var 0) $
     let1 ((Term.var 1).pair (Term.var 0)) $
     r.vwk1.vwk1)
  := single $ BCongD.step $ StepD.let2_eta_op r

-- def RWD.let1_eta {Γ : ℕ → ε} (r : Region φ)
--   : RWD StepD Γ
--     (let1 (Term.var 0) $
--      r.vwk1) r
--   := single $ BCongD.step $ StepD.let1_eta r

-- def RWD.let1_eta_op {Γ : ℕ → ε} (r : Region φ)
--   : RWD StepD Γ r
--     (let1 (Term.var 0) $
--      r.vwk1)
--   := single $ BCongD.step $ StepD.let1_eta_op r

instance instTransRWD
  {P : (ℕ → ε) → Region φ → Region φ → Type _} {Γ}
  : Trans (RWD P Γ) (RWD P Γ) (RWD P Γ) where
  trans := RWD.comp

infixr:10 " ⟶R " => λ{P Γ} => RWD P Γ

-- TODO: prefunctor lore

def SCongD.let1_func {P : Region φ → Region φ → Type _} (e : Term φ)
  : Corr.Prefunctor (SCongD P) (SCongD P) where
  obj := Region.let1 e
  map := SCongD.let1 e

def SCongD.let2_func {P : Region φ → Region φ → Type _} (e : Term φ)
  : Corr.Prefunctor (SCongD P) (SCongD P) where
  obj := Region.let2 e
  map := SCongD.let2 e

def SCongD.case_left_func {P : Region φ → Region φ → Type _} (e : Term φ) (s : Region φ)
  : Corr.Prefunctor (SCongD P) (SCongD P) where
  obj := (Region.case e · s)
  map := (SCongD.case_left e · s)

def SCongD.case_right_func {P : Region φ → Region φ → Type _} (e : Term φ) (r : Region φ)
  : Corr.Prefunctor (SCongD P) (SCongD P) where
  obj := Region.case e r
  map := SCongD.case_right e r

def SCongD.cfg_entry_func {P : Region φ → Region φ → Type _} (n) (G : Fin n → Region φ)
  : Corr.Prefunctor (SCongD P) (SCongD P) where
  obj := (Region.cfg · n G)
  map := (SCongD.cfg_entry · n G)

def SCongD.cfg_block_func' {P : Region φ → Region φ → Type _}
  (β : Region φ) (n) (G : Fin n → Region φ) (i : Fin n)
  : Corr.Prefunctor (SCongD P) (SCongD P) where
  obj := λr => (Region.cfg β n (Function.update G i r))
  map := SCongD.cfg_block' β n G i

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
