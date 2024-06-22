import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.CategoryTheory.PathCategory

import Discretion.Correspondence.Definitions

import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Effect.Subst

namespace BinSyntax

variable [Φ: EffectSet φ ε] [SemilatticeSup ε] [OrderBot ε]

-- TODO: define as Subst.cons or smt...
def Term.subst₂ (a b: Term φ) : Subst φ
  | 0 => a
  | 1 => b
  | n + 2 => Term.var n

namespace Region

inductive PureBeta (Γ : ℕ → ε) : Region φ → Region φ → Prop
  | let1 (e : Term φ) (r : Region φ)
    : e.effect Γ = ⊥ → PureBeta Γ (r.let1 e) (r.vsubst e.subst0)

theorem PureBeta.let1_pure {Γ : ℕ → ε} {e} {r r' : Region φ}
  (h : PureBeta Γ (r.let1 e) r') : e.effect Γ = ⊥ := by cases h; assumption

theorem PureBeta.let1_trg {Γ : ℕ → ε} {e} {r r' : Region φ}
  (h : PureBeta Γ (r.let1 e) r') : r' = r.vsubst e.subst0 := by cases h; rfl

inductive Reduce : Region φ → Region φ → Prop
  | let2_pair (a b r) : Reduce (let2 (Term.pair a b) r) (let1 a $ let1 (b.wk Nat.succ) $ r)
  | case_inl (e r s) : Reduce (case (Term.inl e) r s) (let1 e r)
  | case_inr (e r s) : Reduce (case (Term.inr e) r s) (let1 e s)

theorem Reduce.let2_pair_trg {a b} {r r' : Region φ}
  (h : Reduce (let2 (Term.pair a b) r) r')
  : r' = (let1 a $ let1 (b.wk Nat.succ) $ r) := by cases h; rfl

theorem Reduce.case_inl_trg {e} {r s r' : Region φ}
  (h : Reduce (case (Term.inl e) r s) r')
  : r' = (let1 e r) := by cases h; rfl

theorem Reduce.case_inr_trg {e} {r s s' : Region φ}
  (h : Reduce (case (Term.inr e) r s) s')
  : s' = (let1 e s) := by cases h; rfl

inductive TermEta1 : Region φ → Region φ → Prop
  | let1_op (f e r) : TermEta1 (let1 (Term.op f e) r)
    (let1 e
      $ let1 (Term.op f (Term.var 0))
      $ r.vwk (Nat.liftWk Nat.succ))
  | let1_pair (a b r) : TermEta1 (let1 (Term.pair a b) r)
    (let1 a
      $ let1 (b.wk Nat.succ)
      $ let1 (Term.pair (Term.var 1) (Term.var 0))
      $ r.vwk (Nat.liftWk (· + 2))
    )
  | let1_inl (e r) : TermEta1 (let1 (Term.inl e) r)
    (let1 e
      $ let1 (Term.inl (Term.var 0))
      $ r.vwk (Nat.liftWk Nat.succ))
  | let1_inr (e r) : TermEta1 (let1 (Term.inr e) r)
    (let1 e
      $ let1 (Term.inr (Term.var 0))
      $ r.vwk (Nat.liftWk Nat.succ))
  | let1_abort (e r) : TermEta1 (let1 (Term.abort e) r)
    (let1 e
      $ let1 (Term.abort (Term.var 0))
      $ r.vwk (Nat.liftWk Nat.succ))

theorem TermEta1.let1_op_trg {f e} {r r' : Region φ}
  (h : TermEta1 (let1 (Term.op f e) r) r')
  : r' = (let1 e $ let1 (Term.op f (Term.var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := by cases h; rfl

theorem TermEta1.let1_pair_trg {a b} {r r' : Region φ}
  (h : TermEta1 (let1 (Term.pair a b) r) r')
  : r' = (let1 a
    $ let1 (b.wk Nat.succ)
    $ let1 (Term.pair (Term.var 1) (Term.var 0))
    $ r.vwk (Nat.liftWk (· + 2)))
  := by cases h; rfl

theorem TermEta1.let1_inl_trg {e} {r r' : Region φ}
  (h : TermEta1 (let1 (Term.inl e) r) r')
  : r' = (let1 e $ let1 (Term.inl (Term.var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := by cases h; rfl

theorem TermEta1.let1_inr_trg {e} {r r' : Region φ}
  (h : TermEta1 (let1 (Term.inr e) r) r')
  : r' = (let1 e $ let1 (Term.inr (Term.var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := by cases h; rfl

theorem TermEta1.let1_abort_trg {e} {r r' : Region φ}
  (h : TermEta1 (let1 (Term.abort e) r) r')
  : r' = (let1 e $ let1 (Term.abort (Term.var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := by cases h; rfl

inductive TermEta2 : Region φ → Region φ → Prop
  | let2_op (f e r) : TermEta2 (let2 (Term.op f e) r) (let1 e
      $ let2 (Term.op f (Term.var 0))
      $ r.vwk (Nat.liftnWk 2 Nat.succ))
  | let2_abort (e r) : TermEta2 (let2 (Term.abort e) r) (let1 e
      $ let2 (Term.abort (Term.var 0))
      $ r.vwk (Nat.liftnWk 2 Nat.succ))

inductive Eta : Region φ → Region φ → Prop
  | let1_case (a b r s) : Eta
    (let1 a $ case (b.wk Nat.succ) r s)
    (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
  | let2_case (a b r s) : Eta
    (let2 a $ case (b.wk (· + 2)) r s)
    (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
  | cfg_br_lt (ℓ e n G) (h : ℓ < n) : Eta
    (cfg (br ℓ e) n G)
    (cfg ((G ⟨ℓ, h⟩).vsubst e.subst0) n G)
  | cfg_br_ge (ℓ e n G) (h : n ≤ ℓ) : Eta
    (cfg (br ℓ e) n G)
    (br (ℓ - n) e)
  | cfg_let1 (a β n G) : Eta
    (cfg (let1 a β) n G)
    (let1 a $ cfg β n (vwk Nat.succ ∘ G))
  | cfg_let2 (a β n G) : Eta
    (cfg (let2 a β) n G)
    (let2 a $ cfg β n (vwk (· + 2) ∘ G))
  | cfg_case (e r s n G) : Eta
    (cfg (case e r s) n G)
    (case e (cfg r n (vwk Nat.succ ∘ G)) (cfg s n (vwk Nat.succ ∘ G)))
  | cfg_cfg (β n G n' G') : Eta
    (cfg (cfg β n G) n' G')
    (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))

inductive SimpleCongruence (P : Region φ → Region φ → Prop) : Region φ → Region φ → Prop
  | step (r r') : P r r' → SimpleCongruence P r r'
  | let1 (e r r') : SimpleCongruence P r r' → SimpleCongruence P (let1 e r) (let1 e r')
  | let2 (e r r') : SimpleCongruence P r r' → SimpleCongruence P (let2 e r) (let2 e r')
  | case_left (e r s r') : SimpleCongruence P r r' → SimpleCongruence P (case e r s) (case e r' s)
  | case_right (e r s s') : SimpleCongruence P s s' → SimpleCongruence P (case e r s) (case e r s')
  | cfg_entry (r r' n G) : SimpleCongruence P r r' → SimpleCongruence P (cfg r n G) (cfg r' n G)
  | cfg_block (r r' n G i G') : SimpleCongruence P r r' → G' = Function.update G i r' →
    SimpleCongruence P (cfg β n G) (cfg β n G')

theorem SimpleCongruence.refl (hP : IsRefl _ P) (r : Region φ) : SimpleCongruence P r r :=
  step _ _ (hP.refl r)

open Term

-- TODO: make these rewrites bidirectional

inductive PRwD : Region φ → Region φ → Type _
  | let1_op (f e r) :
    PRwD (let1 (op f e) r) (let1 e $ let1 (op f (var 0)) $ r.vwk1)
  | let1_pair (a b r) :
    PRwD (let1 (pair a b) r)
    (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) $ r.vwk1.vwk1)
  | let1_inl (e r) :
    PRwD (let1 (inl e) r) (let1 e $ let1 (inl (var 0)) $ r.vwk1)
  | let1_inr (e r) :
    PRwD (let1 (inr e) r) (let1 e $ let1 (inr (var 0)) $ r.vwk1)
  | let1_abort (e r) :
    PRwD (let1 (abort e) r) (let1 e $ let1 (abort (var 0)) $ r.vwk1)
  | let2_op (f e r) :
    PRwD (let2 (op f e) r) (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  | let2_pair (a b r) : PRwD (let2 (pair a b) r) (let1 a $ let1 (b.wk Nat.succ) $ r)
  | let2_abort (e r) :
    PRwD (let2 (abort e) r) (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  | case_op (f e r s) :
    PRwD (case (op f e) r s)
      (let1 e $ case (op f (var 0))
      (r.vwk1)
      (s.vwk1))
  | case_abort (e r s) :
    PRwD (case (abort e) r s)
      (let1 e $ case (abort (var 0))
      (r.vwk1)
      (s.vwk1))
  | let1_case (a b r s) :
    PRwD (let1 a $ case (b.wk Nat.succ) r s)
    (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
  | let2_case (a b r s) :
    PRwD (let2 a $ case (b.wk (· + 2)) r s)
    (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
  | cfg_br_lt (ℓ e n G) (h : ℓ < n) :
    PRwD (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).let1 e) n G)
  | cfg_let1 (a β n G) :
    PRwD (cfg (let1 a β) n G) (let1 a $ cfg β n (vwk1 ∘ G))
  | cfg_let2 (a β n G) :
    PRwD (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk (· + 2) ∘ G))
  | cfg_case (e r s n G) :
    PRwD (cfg (case e r s) n G)
      (case e (cfg r n (vwk Nat.succ ∘ G)) (cfg s n (vwk Nat.succ ∘ G)))
  | cfg_cfg (β n G n' G') :
    PRwD (cfg (cfg β n G) n' G') (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
  | cfg_zero (β G) : PRwD (cfg β 0 G) β
  | cfg_fuse (β n G k) (ρ : Fin k → Fin n) (hρ : Function.Surjective ρ) :
    PRwD
      (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
      (cfg β k (G ∘ ρ))
  | let2_eta r :
    PRwD (let2 (Term.var 0) (let1 ((Term.var 1).pair (Term.var 0)) r.vwk1.vwk1)) r

def PRwD.cast_src {r₀ r₀' r₁ : Region φ} (h : r₀ = r₀') (p : PRwD r₀ r₁)
  : PRwD r₀' r₁ := h ▸ p

def PRwD.cast_trg {r₀ r₁ r₁' : Region φ} (p : PRwD r₀ r₁) (h : r₁ = r₁')
  : PRwD r₀ r₁' := h ▸ p

def PRwD.cast {r₀ r₀' r₁ r₁' : Region φ} (h₀ : r₀ = r₀') (h₁ : r₁ = r₁')
  (p : PRwD r₀ r₁) : PRwD r₀' r₁' := h₁ ▸ h₀ ▸ p

theorem PRwD.effect {Γ : ℕ → ε} {r r' : Region φ} (p : PRwD r r') : r.effect Γ = r'.effect Γ := by
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
  | let2_eta => sorry--simp [Nat.liftBot, sup_assoc]
  | _ => simp [Nat.liftBot, sup_assoc]

-- TODO: PRwD WfD iff?

inductive PStepD (Γ : ℕ → ε) : Region φ → Region φ → Type _
  | rw {r r'} : PRwD r r' → PStepD Γ r r'
  | rw_symm {r r'} : PRwD r r' → PStepD Γ r' r
  | let1_beta (e r) : e.effect Γ = ⊥ → PStepD Γ (let1 e r) (r.vsubst e.subst0)
  | case_inl (e r s) : PStepD Γ (case (inl e) r s) (let1 e r)
  | case_inr (e r s) : PStepD Γ (case (inr e) r s) (let1 e s)
  -- | cfg_br_ge (ℓ e n G) (h : n ≤ ℓ) : PStepD Γ (cfg (br ℓ e) n G) (br (ℓ - n) e)
  | wk_cfg (β n G k) (ρ : Fin k → Fin n) /-(hρ : Function.Bijective ρ)-/ :
    PStepD Γ
      (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
      (cfg β k (G ∘ ρ))
  -- Note: this adds a tiny bit of power to wk_cfg, which otherwise could only detect G is dead code if it never
  -- recursively called itself, i.e. if it could be written as G = (lwk (· + n) ∘ Gn)
  | dead_cfg_left (β n G m G') :
    PStepD Γ
      (cfg (β.lwk (· + n)) (n + m) (Fin.addCases G (lwk (· + n) ∘ G')))
      (cfg β m G')

@[match_pattern]
def PStepD.let1_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : PStepD Γ (let1 (op f e) r) (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := PStepD.rw $ PRwD.let1_op f e r

@[match_pattern]
def PStepD.let1_op_inv {Γ : ℕ → ε} (f e) (r : Region φ)
  : PStepD Γ (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (op f e) r)
  := PStepD.rw_symm $ PRwD.let1_op f e r

@[match_pattern]
def PStepD.let1_pair {Γ : ℕ → ε} (a b) (r : Region φ)
  : PStepD Γ (let1 (pair a b) r)
    (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) r.vwk1.vwk1)
  := PStepD.rw $ PRwD.let1_pair a b r

@[match_pattern]
def PStepD.let1_pair_inv {Γ : ℕ → ε} (a b) (r : Region φ)
  : PStepD Γ (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) r.vwk1.vwk1)
    (let1 (pair a b) r)
  := PStepD.rw_symm $ PRwD.let1_pair a b r

@[match_pattern]
def PStepD.let1_inl {Γ : ℕ → ε} (e) (r : Region φ)
  : PStepD Γ (let1 (inl e) r) (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := PStepD.rw $ PRwD.let1_inl e r

@[match_pattern]
def PStepD.let1_inl_inv {Γ : ℕ → ε} (e) (r : Region φ)
  : PStepD Γ (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (inl e) r)
  := PStepD.rw_symm $ PRwD.let1_inl e r

@[match_pattern]
def PStepD.let1_inr {Γ : ℕ → ε} (e) (r : Region φ)
  : PStepD Γ (let1 (inr e) r) (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := PStepD.rw $ PRwD.let1_inr e r

@[match_pattern]
def PStepD.let1_inr_inv {Γ : ℕ → ε} (e) (r : Region φ)
  : PStepD Γ (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (inr e) r)
  := PStepD.rw_symm $ PRwD.let1_inr e r

@[match_pattern]
def PStepD.let1_abort {Γ : ℕ → ε} (e) (r : Region φ)
  : PStepD Γ (let1 (abort e) r) (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := PStepD.rw $ PRwD.let1_abort e r

@[match_pattern]
def PStepD.let1_abort_inv {Γ : ℕ → ε} (e) (r : Region φ)
  : PStepD Γ (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (abort e) r)
  := PStepD.rw_symm $ PRwD.let1_abort e r

@[match_pattern]
def PStepD.let2_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : PStepD Γ (let2 (op f e) r) (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := PStepD.rw $ PRwD.let2_op f e r

@[match_pattern]
def PStepD.let2_op_inv {Γ : ℕ → ε} (f e) (r : Region φ)
  : PStepD Γ (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
    (let2 (op f e) r)
  := PStepD.rw_symm $ PRwD.let2_op f e r

@[match_pattern]
def PStepD.let2_pair {Γ : ℕ → ε} (a b) (r : Region φ)
  : PStepD Γ (let2 (pair a b) r) (let1 a $ let1 (b.wk Nat.succ) $ r)
  := PStepD.rw $ PRwD.let2_pair a b r

@[match_pattern]
def PStepD.let2_pair_inv {Γ : ℕ → ε} (a b) (r : Region φ)
  : PStepD Γ (let1 a $ let1 (b.wk Nat.succ) $ r)
    (let2 (pair a b) r)
  := PStepD.rw_symm $ PRwD.let2_pair a b r

@[match_pattern]
def PStepD.let2_abort {Γ : ℕ → ε} (e) (r : Region φ)
  : PStepD Γ (let2 (abort e) r) (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := PStepD.rw $ PRwD.let2_abort e r

@[match_pattern]
def PStepD.let2_abort_inv {Γ : ℕ → ε} (e) (r : Region φ)
  : PStepD Γ (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
    (let2 (abort e) r)
  := PStepD.rw_symm $ PRwD.let2_abort e r

@[match_pattern]
def PStepD.case_op {Γ : ℕ → ε} (f e) (r s : Region φ)
  : PStepD Γ (case (op f e) r s)
    (let1 e $ case (op f (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ))
  )
  := PStepD.rw $ PRwD.case_op f e r s

@[match_pattern]
def PStepD.case_op_inv {Γ : ℕ → ε} (f e) (r s : Region φ)
  : PStepD Γ (let1 e $ case (op f (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ)))
    (case (op f e) r s)
  := PStepD.rw_symm $ PRwD.case_op f e r s

@[match_pattern]
def PStepD.case_abort {Γ : ℕ → ε} (e) (r s : Region φ)
  : PStepD Γ (case (abort e) r s)
    (let1 e $ case (abort (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ))
  )
  := PStepD.rw $ PRwD.case_abort e r s

@[match_pattern]
def PStepD.case_abort_inv {Γ : ℕ → ε} (e) (r s : Region φ)
  : PStepD Γ (let1 e $ case (abort (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ)))
    (case (abort e) r s)
  := PStepD.rw_symm $ PRwD.case_abort e r s

@[match_pattern]
def PStepD.let1_case {Γ : ℕ → ε} (a b) (r s : Region φ)
  : PStepD Γ (let1 a $ case (b.wk Nat.succ) r s)
    (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
  := PStepD.rw $ PRwD.let1_case a b r s

@[match_pattern]
def PStepD.let1_case_inv {Γ : ℕ → ε} (a b) (r s : Region φ)
  : PStepD Γ (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
    (let1 a $ case (b.wk Nat.succ) r s)
  := PStepD.rw_symm $ PRwD.let1_case a b r s

@[match_pattern]
def PStepD.let2_case {Γ : ℕ → ε} (a b) (r s : Region φ)
  : PStepD Γ (let2 a $ case (b.wk (· + 2)) r s)
    (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
  := PStepD.rw $ PRwD.let2_case a b r s

@[match_pattern]
def PStepD.let2_case_inv {Γ : ℕ → ε} (a b) (r s : Region φ)
  : PStepD Γ (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
    (let2 a $ case (b.wk (· + 2)) r s)
  := PStepD.rw_symm $ PRwD.let2_case a b r s

@[match_pattern]
def PStepD.cfg_br_lt {Γ : ℕ → ε} (ℓ) (e : Term φ) (n G) (h : ℓ < n)
  : PStepD Γ (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).let1 e) n G)
  := PStepD.rw $ PRwD.cfg_br_lt ℓ e n G h

@[match_pattern]
def PStepD.cfg_br_lt_inv {Γ : ℕ → ε} (ℓ) (e : Term φ) (n G) (h : ℓ < n)
  : PStepD Γ (cfg ((G ⟨ℓ, h⟩).let1 e) n G) (cfg (br ℓ e) n G)
  := PStepD.rw_symm $ PRwD.cfg_br_lt ℓ e n G h

@[match_pattern]
def PStepD.cfg_let1 {Γ : ℕ → ε} (a : Term φ) (β n G)
  : PStepD Γ (cfg (let1 a β) n G) (let1 a $ cfg β n (vwk1 ∘ G))
  := PStepD.rw $ PRwD.cfg_let1 a β n G

@[match_pattern]
def PStepD.cfg_let1_inv {Γ : ℕ → ε} (a : Term φ) (β n G)
  : PStepD Γ (let1 a $ cfg β n (vwk1 ∘ G))
    (cfg (let1 a β) n G)
  := PStepD.rw_symm $ PRwD.cfg_let1 a β n G

@[match_pattern]
def PStepD.cfg_let2 {Γ : ℕ → ε} (a : Term φ) (β n G)
  : PStepD Γ (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk (· + 2) ∘ G))
  := PStepD.rw $ PRwD.cfg_let2 a β n G

@[match_pattern]
def PStepD.cfg_let2_inv {Γ : ℕ → ε} (a : Term φ) (β n G)
  : PStepD Γ (let2 a $ cfg β n (vwk (· + 2) ∘ G))
    (cfg (let2 a β) n G)
  := PStepD.rw_symm $ PRwD.cfg_let2 a β n G

@[match_pattern]
def PStepD.cfg_case {Γ : ℕ → ε} (e : Term φ) (r s n G)
  : PStepD Γ (cfg (case e r s) n G)
    (case e (cfg r n (vwk Nat.succ ∘ G)) (cfg s n (vwk Nat.succ ∘ G))
  )
  := PStepD.rw $ PRwD.cfg_case e r s n G

@[match_pattern]
def PStepD.cfg_case_inv {Γ : ℕ → ε} (e : Term φ) (r s n G)
  : PStepD Γ (case e (cfg r n (vwk Nat.succ ∘ G)) (cfg s n (vwk Nat.succ ∘ G)))
    (cfg (case e r s) n G)
  := PStepD.rw_symm $ PRwD.cfg_case e r s n G

@[match_pattern]
def PStepD.cfg_cfg {Γ : ℕ → ε} (β : Region φ) (n G n' G')
  : PStepD Γ (cfg (cfg β n G) n' G') (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
  := PStepD.rw $ PRwD.cfg_cfg β n G n' G'

@[match_pattern]
def PStepD.cfg_cfg_inv {Γ : ℕ → ε} (β : Region φ) (n G n' G')
  : PStepD Γ (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
    (cfg (cfg β n G) n' G')
  := PStepD.rw_symm $ PRwD.cfg_cfg β n G n' G'

@[match_pattern]
def PStepD.cfg_zero {Γ : ℕ → ε} (β : Region φ) (G)
  : PStepD Γ (cfg β 0 G) β := PStepD.rw $ PRwD.cfg_zero β G

@[match_pattern]
def PStepD.cfg_zero_inv {Γ : ℕ → ε} (β : Region φ) (G)
  : PStepD Γ β (cfg β 0 G) := PStepD.rw_symm $ PRwD.cfg_zero β G

@[match_pattern]
def PStepD.let2_eta {Γ : ℕ → ε} (r : Region φ)
  : PStepD Γ (let2 (var 0) (let1 ((var 1).pair (var 0)) r.vwk1.vwk1)) r
  := PStepD.rw $ PRwD.let2_eta r

@[match_pattern]
def PStepD.let2_eta_inv {Γ : ℕ → ε} (r : Region φ)
  : PStepD Γ r (let2 (var 0) (let1 ((var 1).pair (var 0)) r.vwk1.vwk1))
  := PStepD.rw_symm $ PRwD.let2_eta r

def PStepD.cast_trg {Γ : ℕ → ε} {r₀ r₁ r₁' : Region φ} (p : PStepD Γ r₀ r₁) (h : r₁ = r₁')
  : PStepD Γ r₀ r₁' := h ▸ p

def PStepD.cast_src {Γ : ℕ → ε} {r₀ r₀' r₁ : Region φ} (h : r₀' = r₀) (p : PStepD Γ r₀ r₁)
  : PStepD Γ r₀' r₁ := h ▸ p

def PStepD.cast {Γ : ℕ → ε} {r₀ r₀' r₁ r₁' : Region φ} (h₀ : r₀ = r₀') (h₁ : r₁ = r₁')
  (p : PStepD Γ r₀ r₁) : PStepD Γ r₀' r₁' := h₁ ▸ h₀ ▸ p

theorem PStepD.effect_le {Γ : ℕ → ε} {r r' : Region φ} (p : PStepD Γ r r')
  : r'.effect Γ ≤ r.effect Γ := by
  cases p with
  | rw p => rw [p.effect]
  | rw_symm p => rw [p.effect]
  | let1_beta _ _ he =>
    apply le_of_eq
    simp only [effect_vsubst, Subst.effect, effect, he, ge_iff_le, bot_le, sup_of_le_right]
    congr
    funext k
    cases k with
    | zero => simp [he, Nat.liftBot]
    | succ k => rfl
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

-- TODO: PStepD is effect monotonic

inductive SCongD (P : Region φ → Region φ → Type u) : Region φ → Region φ → Type u
  | step : P r r' → SCongD P r r'
  | let1 (e) : SCongD P r r' → SCongD P (let1 e r) (let1 e r')
  | let2 (e) : SCongD P r r' → SCongD P (let2 e r) (let2 e r')
  | case_left (e) : SCongD P r r' → (s : Region φ)
    → SCongD P (case e r s) (case e r' s)
  | case_right (e r) : SCongD P s s' → SCongD P (case e r s) (case e r s')
  | cfg_entry
    : SCongD P r r' → (n : _) → (G : _) → SCongD P (cfg r n G) (cfg r' n G)
  | cfg_block (β n G i) : SCongD P r r' →
    SCongD P (cfg β n (Function.update G i r)) (cfg β n (Function.update G i r'))

-- TODO: SCongD is effect monotone/antitone iff underlying is
-- ==> SCongD is effect preserving iff underlying is

inductive BCongD (P : (ℕ → ε) → Region φ → Region φ → Type u)
  : (ℕ → ε) → Region φ → Region φ → Type u
  | step : P Γ r r' → BCongD P Γ r r'
  | let1 (e) : BCongD P (Nat.liftBot Γ) r r' → BCongD P Γ (let1 e r) (let1 e r')
  | let2 (e) : BCongD P (Nat.liftnBot 2 Γ) r r' → BCongD P Γ (let2 e r) (let2 e r')
  | case_left (e) : BCongD P (Nat.liftBot Γ) r r' → (s : Region φ)
    → BCongD P Γ (case e r s) (case e r' s)
  | case_right (e r) : BCongD P (Nat.liftBot Γ) s s' → BCongD P Γ (case e r s) (case e r s')
  | cfg_entry
    : BCongD P Γ r r' → (n : _) → (G : _) → BCongD P Γ (cfg r n G) (cfg r' n G)
  | cfg_block (β n G i) : BCongD P (Nat.liftBot Γ) r r' →
    BCongD P Γ (cfg β n (Function.update G i r)) (cfg β n (Function.update G i r'))

abbrev RWD (P : (ℕ → ε) → Region φ → Region φ → Type u) (Γ : ℕ → ε) := Corr.Path ((BCongD P) Γ)

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
  : RWD PStepD Γ (let1 e r) (r.vsubst e.subst0)
  := single $ BCongD.step $ PStepD.let1_beta e r h

def RWD.case_inl {Γ : ℕ → ε} (e) (r s : Region φ)
  : RWD PStepD Γ (case (inl e) r s) (let1 e r)
  := single $ BCongD.step $ PStepD.case_inl e r s

def RWD.case_inr {Γ : ℕ → ε} (e) (r s : Region φ)
  : RWD PStepD Γ (case (inr e) r s) (let1 e s)
  := single $ BCongD.step $ PStepD.case_inr e r s

def RWD.let1_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : RWD PStepD Γ (let1 (op f e) r) (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := single $ BCongD.step $ PStepD.let1_op f e r

def RWD.let1_op_inv {Γ : ℕ → ε} (f e) (r : Region φ)
  : RWD PStepD Γ (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (op f e) r)
  := single $ BCongD.step $ PStepD.let1_op_inv f e r

def RWD.let1_pair {Γ : ℕ → ε} (a b) (r : Region φ)
  : RWD PStepD Γ (let1 (pair a b) r)
    (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) r.vwk1.vwk1
  )
  := single $ BCongD.step $ PStepD.let1_pair a b r

def RWD.let1_pair_inv {Γ : ℕ → ε} (a b) (r : Region φ)
  : RWD PStepD Γ (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) r.vwk1.vwk1)
    (let1 (pair a b) r)
  := single $ BCongD.step $ PStepD.let1_pair_inv a b r

def RWD.let1_inl {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD PStepD Γ (let1 (inl e) r) (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := single $ BCongD.step $ PStepD.let1_inl e r

def RWD.let1_inl_inv {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD PStepD Γ (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (inl e) r)
  := single $ BCongD.step $ PStepD.let1_inl_inv e r

def RWD.let1_inr {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD PStepD Γ (let1 (inr e) r) (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := single $ BCongD.step $ PStepD.let1_inr e r

def RWD.let1_inr_inv {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD PStepD Γ (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (inr e) r)
  := single $ BCongD.step $ PStepD.let1_inr_inv e r

def RWD.let1_abort {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD PStepD Γ (let1 (abort e) r) (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := single $ BCongD.step $ PStepD.let1_abort e r

def RWD.let1_abort_inv {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD PStepD Γ (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (abort e) r)
  := single $ BCongD.step $ PStepD.let1_abort_inv e r

def RWD.let2_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : RWD PStepD Γ (let2 (op f e) r) (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := single $ BCongD.step $ PStepD.let2_op f e r

def RWD.let2_op_inv {Γ : ℕ → ε} (f e) (r : Region φ)
  : RWD PStepD Γ (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
    (let2 (op f e) r)
  := single $ BCongD.step $ PStepD.let2_op_inv f e r

def RWD.let2_pair {Γ : ℕ → ε} (a b) (r : Region φ)
  : RWD PStepD Γ (let2 (pair a b) r) (let1 a $ let1 (b.wk Nat.succ) $ r)
  := single $ BCongD.step (PStepD.let2_pair a b r)

def RWD.let2_pair_inv {Γ : ℕ → ε} (a b) (r : Region φ)
  : RWD PStepD Γ (let1 a $ let1 (b.wk Nat.succ) $ r)
    (let2 (pair a b) r)
  := single $ BCongD.step $ PStepD.let2_pair_inv a b r

def RWD.let2_abort {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD PStepD Γ (let2 (abort e) r) (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := single $ BCongD.step $ PStepD.let2_abort e r

def RWD.let2_abort_inv {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD PStepD Γ (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
    (let2 (abort e) r)
  := single $ BCongD.step $ PStepD.let2_abort_inv e r

def RWD.case_op {Γ : ℕ → ε} (f e) (r s : Region φ)
  : RWD PStepD Γ (case (op f e) r s)
    (let1 e $ case (op f (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ))
  )
  := single $ BCongD.step $ PStepD.case_op f e r s

def RWD.case_op_inv {Γ : ℕ → ε} (f e) (r s : Region φ)
  : RWD PStepD Γ (let1 e $ case (op f (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ)))
    (case (op f e) r s)
  := single $ BCongD.step $ PStepD.case_op_inv f e r s

def RWD.case_abort {Γ : ℕ → ε} (e) (r s : Region φ)
  : RWD PStepD Γ (case (abort e) r s)
    (let1 e $ case (abort (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ))
  )
  := single $ BCongD.step $ PStepD.case_abort e r s

def RWD.case_abort_inv {Γ : ℕ → ε} (e) (r s : Region φ)
  : RWD PStepD Γ (let1 e $ case (abort (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ)))
    (case (abort e) r s)
  := single $ BCongD.step $ PStepD.case_abort_inv e r s

def RWD.let1_case {Γ : ℕ → ε} (a b) (r s : Region φ)
  : RWD PStepD Γ (let1 a $ case (b.wk Nat.succ) r s)
    (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
  := single $ BCongD.step $ PStepD.let1_case a b r s

def RWD.let1_case_inv {Γ : ℕ → ε} (a b) (r s : Region φ)
  : RWD PStepD Γ (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
    (let1 a $ case (b.wk Nat.succ) r s)
  := single $ BCongD.step $ PStepD.let1_case_inv a b r s

def RWD.let2_case {Γ : ℕ → ε} (a b) (r s : Region φ)
  : RWD PStepD Γ (let2 a $ case (b.wk (· + 2)) r s)
    (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
  := single $ BCongD.step $ PStepD.let2_case a b r s

def RWD.let2_case_inv {Γ : ℕ → ε} (a b) (r s : Region φ)
  : RWD PStepD Γ (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
    (let2 a $ case (b.wk (· + 2)) r s)
  := single $ BCongD.step $ PStepD.let2_case_inv a b r s

def RWD.cfg_br_lt {Γ : ℕ → ε} (ℓ) (e : Term φ) (n G) (h : ℓ < n)
  : RWD PStepD Γ (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).let1 e) n G)
  := single $ BCongD.step $ PStepD.cfg_br_lt ℓ e n G h

def RWD.cfg_br_lt_inv {Γ : ℕ → ε} (ℓ) (e : Term φ) (n G) (h : ℓ < n)
  : RWD PStepD Γ (cfg ((G ⟨ℓ, h⟩).let1 e) n G) (cfg (br ℓ e) n G)
  := single $ BCongD.step $ PStepD.cfg_br_lt_inv ℓ e n G h

def RWD.cfg_let1 {Γ : ℕ → ε} (a : Term φ) (β n G)
  : RWD PStepD Γ (cfg (let1 a β) n G) (let1 a $ cfg β n (vwk1 ∘ G))
  := single $ BCongD.step $ PStepD.cfg_let1 a β n G

def RWD.cfg_let1_inv {Γ : ℕ → ε} (a : Term φ) (β n G)
  : RWD PStepD Γ (let1 a $ cfg β n (vwk1 ∘ G))
    (cfg (let1 a β) n G)
  := single $ BCongD.step $ PStepD.cfg_let1_inv a β n G

def RWD.cfg_let2 {Γ : ℕ → ε} (a : Term φ) (β n G)
  : RWD PStepD Γ (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk (· + 2) ∘ G))
  := single $ BCongD.step $ PStepD.cfg_let2 a β n G

def RWD.cfg_let2_inv {Γ : ℕ → ε} (a : Term φ) (β n G)
  : RWD PStepD Γ (let2 a $ cfg β n (vwk (· + 2) ∘ G))
    (cfg (let2 a β) n G)
  := single $ BCongD.step $ PStepD.cfg_let2_inv a β n G

def RWD.cfg_case {Γ : ℕ → ε} (e : Term φ) (r s n G)
  : RWD PStepD Γ (cfg (case e r s) n G)
    (case e (cfg r n (vwk Nat.succ ∘ G)) (cfg s n (vwk Nat.succ ∘ G))
  )
  := single $ BCongD.step $ PStepD.cfg_case e r s n G

def RWD.cfg_case_inv {Γ : ℕ → ε} (e : Term φ) (r s n G)
  : RWD PStepD Γ (case e (cfg r n (vwk Nat.succ ∘ G)) (cfg s n (vwk Nat.succ ∘ G)))
    (cfg (case e r s) n G)
  := single $ BCongD.step $ PStepD.cfg_case_inv e r s n G

def RWD.cfg_cfg {Γ : ℕ → ε} (β : Region φ) (n G n' G')
  : RWD PStepD Γ (cfg (cfg β n G) n' G') (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
  := single $ BCongD.step $ PStepD.cfg_cfg β n G n' G'

def RWD.cfg_cfg_inv {Γ : ℕ → ε} (β : Region φ) (n G n' G')
  : RWD PStepD Γ (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
    (cfg (cfg β n G) n' G')
  := single $ BCongD.step $ PStepD.cfg_cfg_inv β n G n' G'

def RWD.cfg_zero {Γ : ℕ → ε} (β : Region φ) (G)
  : RWD PStepD Γ (cfg β 0 G) β := single $ BCongD.step $ PStepD.cfg_zero β G

def RWD.cfg_zero_inv {Γ : ℕ → ε} (β : Region φ) (G)
  : RWD PStepD Γ β (cfg β 0 G) := single $ BCongD.step $ PStepD.cfg_zero_inv β G

def RWD.wk_cfg {Γ : ℕ → ε} (β : Region φ) (n G k) (ρ : Fin k → Fin n) /-(hρ : Function.Bijective ρ)-/
  : RWD PStepD Γ
    (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
    (cfg β k (G ∘ ρ))
  := single $ BCongD.step $ PStepD.wk_cfg β n G k ρ

def RWD.dead_cfg_left {Γ : ℕ → ε} (β : Region φ) (n G m G')
  : RWD PStepD Γ
    (cfg (β.lwk (· + n)) (n + m) (Fin.addCases G (lwk (· + n) ∘ G')))
    (cfg β m G')
  := single $ BCongD.step $ PStepD.dead_cfg_left β n G m G'

def RWD.swap_cfg' {Γ : ℕ → ε} (β : Region φ) (n G m G')
  : RWD PStepD Γ
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
  : RWD PStepD Γ
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
  : RWD PStepD Γ r.let1V0 r
  := cast_trg
    (let1_beta (Term.var 0) (r.vwk (Nat.liftWk Nat.succ)) hΓ)
    (by rw [<-vsubst_fromWk_apply, vsubst_vsubst, vsubst_id']; funext i; cases i <;> rfl)

def RWD.let2_eta {Γ : ℕ → ε} (r : Region φ)
  : RWD PStepD Γ
    (let2 (Term.var 0) $
     let1 ((Term.var 1).pair (Term.var 0)) $
     r.vwk1.vwk1) r
  := single $ BCongD.step $ PStepD.let2_eta r

def RWD.let2_eta_inv {Γ : ℕ → ε} (r : Region φ)
  : RWD PStepD Γ r
    (let2 (Term.var 0) $
     let1 ((Term.var 1).pair (Term.var 0)) $
     r.vwk1.vwk1)
  := single $ BCongD.step $ PStepD.let2_eta_inv r

-- def RWD.let2_eta2 {Γ : ℕ → ε} (r : Region φ)
--   : RWD PStepD Γ
--     (let2 (Term.var 0) $
--      let2 ((Term.var 1).pair (Term.var 0)) $
--      r.vwk1.vwk1) r
--   := sorry

instance RWD.instTrans {P : (ℕ → ε) → Region φ → Region φ → Type u} {Γ : ℕ → ε}
  : Trans (RWD P Γ) (RWD P Γ) (RWD P Γ) where
  trans := RWD.comp

infixr:10 " ⟶R " => λ{P} => RWD P

-- TODO: prefunctor lore

def SCongD.let1_func {P : Region φ → Region φ → Type u} (e : Term φ)
  : Corr.Prefunctor (SCongD P) (SCongD P) where
  obj := Region.let1 e
  map := SCongD.let1 e

def SCongD.let2_func {P : Region φ → Region φ → Type u} (e : Term φ)
  : Corr.Prefunctor (SCongD P) (SCongD P) where
  obj := Region.let2 e
  map := SCongD.let2 e

def SCongD.case_left_func {P : Region φ → Region φ → Type u} (e : Term φ) (s : Region φ)
  : Corr.Prefunctor (SCongD P) (SCongD P) where
  obj := (Region.case e · s)
  map := (SCongD.case_left e · s)

def SCongD.case_right_func {P : Region φ → Region φ → Type u} (e : Term φ) (r : Region φ)
  : Corr.Prefunctor (SCongD P) (SCongD P) where
  obj := Region.case e r
  map := SCongD.case_right e r

def SCongD.cfg_entry_func {P : Region φ → Region φ → Type u} (n) (G : Fin n → Region φ)
  : Corr.Prefunctor (SCongD P) (SCongD P) where
  obj := (Region.cfg · n G)
  map := (SCongD.cfg_entry · n G)

def SCongD.cfg_block_func {P : Region φ → Region φ → Type u}
  (β : Region φ) (n) (G : Fin n → Region φ) (i : Fin n)
  : Corr.Prefunctor (SCongD P) (SCongD P) where
  obj := λr => (Region.cfg β n (Function.update G i r))
  map := SCongD.cfg_block β n G i

def BCongD.let1_func {P : (ℕ → ε) → Region φ → Region φ → Type u} {Γ} (e : Term φ)
  : Corr.Prefunctor (BCongD P (Nat.liftBot Γ)) (BCongD P Γ) where
  obj := Region.let1 e
  map := BCongD.let1 e

def BCongD.let2_func {P : (ℕ → ε) → Region φ → Region φ → Type u} {Γ} (e : Term φ)
  : Corr.Prefunctor (BCongD P (Nat.liftnBot 2 Γ)) (BCongD P Γ) where
  obj := Region.let2 e
  map := BCongD.let2 e

def BCongD.case_left_func
  {P : (ℕ → ε) → Region φ → Region φ → Type u} {Γ} (e : Term φ) (s : Region φ)
  : Corr.Prefunctor (BCongD P (Nat.liftBot Γ)) (BCongD P Γ) where
  obj := (Region.case e · s)
  map := (BCongD.case_left e · s)

def BCongD.case_right_func {P : (ℕ → ε) → Region φ → Region φ → Type u} {Γ}
  (e : Term φ) (r : Region φ)
  : Corr.Prefunctor (BCongD P (Nat.liftBot Γ)) (BCongD P Γ) where
  obj := Region.case e r
  map := BCongD.case_right e r

def BCongD.cfg_entry_func {P : (ℕ → ε) → Region φ → Region φ → Type u} {Γ}
  (n) (G : Fin n → Region φ)
  : Corr.Prefunctor (BCongD P Γ) (BCongD P Γ) where
  obj := (Region.cfg · n G)
  map := (BCongD.cfg_entry · n G)

def BCongD.cfg_block_func {P : (ℕ → ε) → Region φ → Region φ → Type u} {Γ}
  (β : Region φ) (n) (G : Fin n → Region φ) (i : Fin n)
  : Corr.Prefunctor (BCongD P (Nat.liftBot Γ)) (BCongD P Γ) where
  obj := λr => (Region.cfg β n (Function.update G i r))
  map := BCongD.cfg_block β n G i

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

def RWD.cfg_block {P} {Γ : ℕ → ε} {r r' : Region φ} (β n G i) (h : RWD P (Nat.liftBot Γ) r r')
  : RWD P Γ (cfg β n (Function.update G i r)) (cfg β n (Function.update G i r'))
  := (BCongD.cfg_block_func β n G i).mapPath h

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
        (cast_trg (cfg_block β n
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
  : RWD PStepD Γ
    (cfg (β.lwk (n.liftnWk (· + m))) (n + m) (Fin.addCases (lwk (n.liftnWk (· + m)) ∘ G) G'))
    (cfg β n G) :=
    (cast_trg (swap_cfg (β.lwk (n.liftnWk (· + m))) n (lwk (n.liftnWk (· + m)) ∘ G) m G')
      (by rw [
        Fin.comp_addCases, lwk_lwk, <-Function.comp.assoc, comp_lwk,
        Fin.toNatWk_swapAdd_comp_liftnWk_add]
      )).comp
    (dead_cfg_left β m _ n G)

def RWD.cfg_elim {Γ : ℕ → ε} (β : Region φ) (n G)
  : RWD PStepD Γ (cfg (β.lwk (· + n)) n G) β
  :=
  let s : RWD PStepD Γ
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
  : RWD PStepD Γ (cfg (br ℓ e) n G) (br (ℓ - n) e)
  := cast_src (by simp [h]) (cfg_elim (br (ℓ - n) e) n G)

-- TODO: vwk, lwk lore...

inductive SCongD.SubstCong (P : Region φ → Region φ → Type _) : Subst φ → Subst φ → Type _
  | step (n) : SCongD P r r' → SubstCong P (Function.update σ n r) (Function.update σ' n r')

inductive BCongD.SubstCong (P : (ℕ → ε) → Region φ → Region φ → Type _)
  : (ℕ → ε) → Subst φ → Subst φ → Type _
  | step (n) : BCongD P Γ r r' → SubstCong P Γ (Function.update σ n r) (Function.update σ' n r')

def RWD.Subst (P : (ℕ → ε) →  Region φ → Region φ → Type _) (Γ : ℕ → ε) (σ σ' : Subst φ)
  := ∀n, RWD P Γ (σ n) (σ' n)

-- TODO: RwD.Subst is effect monotone/antitone iff underlying is
-- ==> RwD.Subst is effect preserving iff underlying is

def RWD.Subst.refl {P} {Γ : ℕ → ε} (σ : Region.Subst φ) : RWD.Subst P Γ σ σ := λ_ => RWD.refl _

def RWD.Subst.comp {P} {Γ : ℕ → ε} {σ σ' σ'' : Region.Subst φ}
  (h : RWD.Subst P Γ σ σ') (h' : RWD.Subst P Γ σ' σ'')
  : RWD.Subst P Γ σ σ''
  := λn => (h n).comp (h' n)

-- TODO: lift, liftn, lwk, vwk lore

-- TODO: Path SubstCong ==> RWD, RWD ∩ FiniteDiff ==> Path SubstCong, "adjunction"

end Region

end BinSyntax
