import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.CategoryTheory.PathCategory

import Discretion.Correspondence.Definitions

import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Effect

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

inductive PRwD (Γ : ℕ → ε) : Region φ → Region φ → Type
  | let1_op (f e r) :
    PRwD Γ (let1 (op f e) r) (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  | let1_pair (a b r) :
    PRwD Γ (let1 (pair a b) r)
    (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) $ r.vwk (Nat.liftWk (· + 2))
  )
  | let1_inl (e r) :
    PRwD Γ (let1 (inl e) r) (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  | let1_inr (e r) :
    PRwD Γ (let1 (inr e) r) (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  | let1_abort (e r) :
    PRwD Γ (let1 (abort e) r) (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  | let2_op (f e r) :
    PRwD Γ (let2 (op f e) r) (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  | let2_pair (a b r) : PRwD Γ (let2 (pair a b) r) (let1 a $ let1 (b.wk Nat.succ) $ r)
  | let2_abort (e r) :
    PRwD Γ (let2 (abort e) r) (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  | let1_case (a b r s) :
    PRwD Γ (let1 a $ case (b.wk Nat.succ) r s)
    (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
  | let2_case (a b r s) :
    PRwD Γ (let2 a $ case (b.wk (· + 2)) r s)
    (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
  | case_op (f e r s) :
    PRwD Γ (case (op f e) r s)
      (let1 e $ case (op f (var 0))
      (r.vwk (Nat.liftWk Nat.succ))
      (s.vwk (Nat.liftWk Nat.succ)))
  | case_abort (e r s) :
    PRwD Γ (case (abort e) r s)
      (let1 e $ case (abort (var 0))
      (r.vwk (Nat.liftWk Nat.succ))
      (s.vwk (Nat.liftWk Nat.succ)))
  | cfg_br_lt (ℓ e n G) (h : ℓ < n) :
    PRwD Γ (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).let1 e) n G)
  | cfg_let1 (a β n G) :
    PRwD Γ (cfg (let1 a β) n G) (let1 a $ cfg β n (vwk Nat.succ ∘ G))
  | cfg_let2 (a β n G) :
    PRwD Γ (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk (· + 2) ∘ G))
  | cfg_case (e r s n G) :
    PRwD Γ (cfg (case e r s) n G)
      (case e (cfg r n (vwk Nat.succ ∘ G)) (cfg s n (vwk Nat.succ ∘ G)))
  | cfg_cfg (β n G n' G') :
    PRwD Γ (cfg (cfg β n G) n' G') (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))

inductive PStepD (Γ : ℕ → ε) : Region φ → Region φ → Type
  | let1_beta (e r) : e.effect Γ = ⊥ → PStepD Γ (let1 e r) (r.vsubst e.subst0)
  | case_inl (e r s) : PStepD Γ (case (inl e) r s) (let1 e r)
  | case_inr (e r s) : PStepD Γ (case (inr e) r s) (let1 e s)
  | let1_op (f e r) :
    PStepD Γ (let1 (op f e) r) (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  | let1_pair (a b r) :
    PStepD Γ (let1 (pair a b) r)
    (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) $ r.vwk (Nat.liftWk (· + 2))
  )
  | let1_inl (e r) :
    PStepD Γ (let1 (inl e) r) (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  | let1_inr (e r) :
    PStepD Γ (let1 (inr e) r) (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  | let1_abort (e r) :
    PStepD Γ (let1 (abort e) r) (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  | let2_op (f e r) :
    PStepD Γ (let2 (op f e) r) (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  | let2_pair (a b r) : PStepD Γ (let2 (pair a b) r) (let1 a $ let1 (b.wk Nat.succ) $ r)
  | let2_abort (e r) :
    PStepD Γ (let2 (abort e) r) (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  | case_op (f e r s) :
    PStepD Γ (case (op f e) r s)
      (let1 e $ case (op f (var 0))
      (r.vwk (Nat.liftWk Nat.succ))
      (s.vwk (Nat.liftWk Nat.succ)))
  | case_abort (e r s) :
    PStepD Γ (case (abort e) r s)
      (let1 e $ case (abort (var 0))
      (r.vwk (Nat.liftWk Nat.succ))
      (s.vwk (Nat.liftWk Nat.succ)))
  | let1_case (a b r s) :
    PStepD Γ (let1 a $ case (b.wk Nat.succ) r s)
    (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
  | let2_case (a b r s) :
    PStepD Γ (let2 a $ case (b.wk (· + 2)) r s)
    (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
  | cfg_br_lt (ℓ e n G) (h : ℓ < n) :
    PStepD Γ (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).let1 e) n G)
  | cfg_br_ge (ℓ e n G) (h : n ≤ ℓ) :
    PStepD Γ (cfg (br ℓ e) n G) (br (ℓ - n) e)
  | cfg_let1 (a β n G) :
    PStepD Γ (cfg (let1 a β) n G) (let1 a $ cfg β n (vwk Nat.succ ∘ G))
  | cfg_let2 (a β n G) :
    PStepD Γ (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk (· + 2) ∘ G))
  | cfg_case (e r s n G) :
    PStepD Γ (cfg (case e r s) n G)
      (case e (cfg r n (vwk Nat.succ ∘ G)) (cfg s n (vwk Nat.succ ∘ G)))
  | cfg_cfg (β n G n' G') :
    PStepD Γ (cfg (cfg β n G) n' G') (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
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

abbrev RWD (P : Region φ → Region φ → Type u) := Corr.Path (SCongD P)

def RWD.refl {P} (r : Region φ) : RWD P r r := Corr.Path.nil r

def RWD.comp {P} {a b c : Region φ} : RWD P a b → RWD P b c → RWD P a c := Corr.Path.comp

def RWD.let1_beta (Γ : ℕ → ε) (e) (r : Region φ) (h : e.effect Γ = ⊥)
  : RWD (PStepD Γ) (let1 e r) (r.vsubst e.subst0)
  := Corr.Path.single $ SCongD.step $ PStepD.let1_beta e r h

def RWD.case_inl (Γ : ℕ → ε) (e) (r s : Region φ)
  : RWD (PStepD Γ) (case (inl e) r s) (let1 e r)
  := Corr.Path.single $ SCongD.step $ PStepD.case_inl e r s

def RWD.case_inr (Γ : ℕ → ε) (e) (r s : Region φ)
  : RWD (PStepD Γ) (case (inr e) r s) (let1 e s)
  := Corr.Path.single $ SCongD.step $ PStepD.case_inr e r s

def RWD.let1_op (Γ : ℕ → ε) (f e) (r : Region φ)
  : RWD (PStepD Γ) (let1 (op f e) r) (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := Corr.Path.single $ SCongD.step $ PStepD.let1_op f e r

def RWD.let1_pair (Γ : ℕ → ε) (a b) (r : Region φ)
  : RWD (PStepD Γ) (let1 (pair a b) r)
    (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) $ r.vwk (Nat.liftWk (· + 2))
  )
  := Corr.Path.single $ SCongD.step $ PStepD.let1_pair a b r

def RWD.let1_inl (Γ : ℕ → ε) (e) (r : Region φ)
  : RWD (PStepD Γ) (let1 (inl e) r) (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := Corr.Path.single $ SCongD.step $ PStepD.let1_inl e r

def RWD.let1_inr (Γ : ℕ → ε) (e) (r : Region φ)
  : RWD (PStepD Γ) (let1 (inr e) r) (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := Corr.Path.single $ SCongD.step $ PStepD.let1_inr e r

def RWD.let1_abort (Γ : ℕ → ε) (e) (r : Region φ)
  : RWD (PStepD Γ) (let1 (abort e) r) (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := Corr.Path.single $ SCongD.step $ PStepD.let1_abort e r

def RWD.let2_op (Γ : ℕ → ε) (f e) (r : Region φ)
  : RWD (PStepD Γ) (let2 (op f e) r) (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := Corr.Path.single $ SCongD.step $ PStepD.let2_op f e r

def RWD.let2_pair (Γ : ℕ → ε) (a b) (r : Region φ)
  : RWD (PStepD Γ) (let2 (pair a b) r) (let1 a $ let1 (b.wk Nat.succ) $ r)
  := Corr.Path.single $ SCongD.step (PStepD.let2_pair a b r)

def RWD.let2_abort (Γ : ℕ → ε) (e) (r : Region φ)
  : RWD (PStepD Γ) (let2 (abort e) r) (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := Corr.Path.single $ SCongD.step $ PStepD.let2_abort e r

def RWD.case_op (Γ : ℕ → ε) (f e) (r s : Region φ)
  : RWD (PStepD Γ) (case (op f e) r s)
    (let1 e $ case (op f (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ))
  )
  := Corr.Path.single $ SCongD.step $ PStepD.case_op f e r s

def RWD.case_abort (Γ : ℕ → ε) (e) (r s : Region φ)
  : RWD (PStepD Γ) (case (abort e) r s)
    (let1 e $ case (abort (var 0)) (r.vwk (Nat.liftWk Nat.succ)) (s.vwk (Nat.liftWk Nat.succ))
  )
  := Corr.Path.single $ SCongD.step $ PStepD.case_abort e r s

def RWD.let1_case (Γ : ℕ → ε) (a b) (r s : Region φ)
  : RWD (PStepD Γ) (let1 a $ case (b.wk Nat.succ) r s)
    (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
  := Corr.Path.single $ SCongD.step $ PStepD.let1_case a b r s

def RWD.let2_case (Γ : ℕ → ε) (a b) (r s : Region φ)
  : RWD (PStepD Γ) (let2 a $ case (b.wk (· + 2)) r s)
    (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
  := Corr.Path.single $ SCongD.step $ PStepD.let2_case a b r s

def RWD.cfg_br_lt (Γ : ℕ → ε) (ℓ) (e : Term φ) (n G) (h : ℓ < n)
  : RWD (PStepD Γ) (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).let1 e) n G)
  := Corr.Path.single $ SCongD.step $ PStepD.cfg_br_lt ℓ e n G h

def RWD.cfg_br_ge (Γ : ℕ → ε) (ℓ) (e : Term φ) (n G) (h : n ≤ ℓ)
  : RWD (PStepD Γ) (cfg (br ℓ e) n G) (br (ℓ - n) e)
  := Corr.Path.single $ SCongD.step $ PStepD.cfg_br_ge ℓ e n G h

def RWD.cfg_let1 (Γ : ℕ → ε) (a : Term φ) (β n G)
  : RWD (PStepD Γ) (cfg (let1 a β) n G) (let1 a $ cfg β n (vwk Nat.succ ∘ G))
  := Corr.Path.single $ SCongD.step $ PStepD.cfg_let1 a β n G

def RWD.cfg_let2 (Γ : ℕ → ε) (a : Term φ) (β n G)
  : RWD (PStepD Γ) (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk (· + 2) ∘ G))
  := Corr.Path.single $ SCongD.step $ PStepD.cfg_let2 a β n G

def RWD.cfg_case (Γ : ℕ → ε) (e : Term φ) (r s n G)
  : RWD (PStepD Γ) (cfg (case e r s) n G)
    (case e (cfg r n (vwk Nat.succ ∘ G)) (cfg s n (vwk Nat.succ ∘ G))
  )
  := Corr.Path.single $ SCongD.step $ PStepD.cfg_case e r s n G

def RWD.cfg_cfg (Γ : ℕ → ε) (β : Region φ) (n G n' G')
  : RWD (PStepD Γ) (cfg (cfg β n G) n' G') (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
  := Corr.Path.single $ SCongD.step $ PStepD.cfg_cfg β n G n' G'

def RWD.wk_cfg (Γ : ℕ → ε) (β : Region φ) (n G k) (ρ : Fin k → Fin n) /-(hρ : Function.Bijective ρ)-/
  : RWD (PStepD Γ)
    (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
    (cfg β k (G ∘ ρ))
  := Corr.Path.single $ SCongD.step $ PStepD.wk_cfg β n G k ρ

def RWD.dead_cfg_left (Γ : ℕ → ε) (β : Region φ) (n G m G')
  : RWD (PStepD Γ)
    (cfg (β.lwk (· + n)) (n + m) (Fin.addCases G (lwk (· + n) ∘ G')))
    (cfg β m G')
  := Corr.Path.single $ SCongD.step $ PStepD.dead_cfg_left β n G m G'

def RWD.swap_cfg' (Γ : ℕ → ε) (β : Region φ) (n G m G')
  : RWD (PStepD Γ)
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

def RWD.cast_trg {P} {r₀ r₁ r₁' : Region φ} (h : RWD P r₀ r₁) (hr₁ : r₁ = r₁')
  : RWD P r₀ r₁'
  := Corr.Path.cast_trg h hr₁

def RWD.cast_src {P} {r₀ r₀' r₁ : Region φ} (hr₀ : r₀ = r₀') (h : RWD P r₀' r₁)
  : RWD P r₀ r₁
  := Corr.Path.cast_src hr₀ h

def RWD.cast {P} {r₀ r₀' r₁ r₁' : Region φ} (hr₀ : r₀ = r₀') (hr₁ : r₁ = r₁') (h : RWD P r₀ r₁)
  : RWD P r₀' r₁'
  := Corr.Path.cast hr₀ hr₁ h

def RWD.swap_cfg (Γ : ℕ → ε) (β : Region φ) (n G m G')
  : RWD (PStepD Γ)
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
    (swap_cfg' Γ
      (β.lwk (Fin.toNatWk (Fin.addCases (Fin.natAdd m) (Fin.castAdd n))))
      m
      (lwk (Fin.toNatWk (Fin.addCases (Fin.natAdd m) (Fin.castAdd n))) ∘ G')
      n
      (lwk (Fin.toNatWk (Fin.addCases (Fin.natAdd m) (Fin.castAdd n))) ∘ G)))
    (by simp [Fin.comp_addCases, Fin.swapAdd])

def RWD.let1V0_id (Γ : ℕ → ε) (r : Region φ) (hΓ : Γ 0 = ⊥)
  : RWD (PStepD Γ) r.let1V0 r
  := cast_trg
    (let1_beta Γ (Term.var 0) (r.vwk (Nat.liftWk Nat.succ)) hΓ)
    (by rw [<-vsubst_fromWk_apply, vsubst_vsubst, vsubst_id']; funext i; cases i <;> rfl)

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

def RWD.let1 {P r r'} (e : Term φ) (h : RWD P r r')
  : RWD P (let1 e r) (let1 e r')
  := (SCongD.let1_func e).mapPath h

def RWD.let2 {P r r'} (e : Term φ) (h : RWD P r r')
  : RWD P (let2 e r) (let2 e r')
  := (SCongD.let2_func e).mapPath h

def RWD.case_left {P r r'} (e : Term φ) (h : RWD P r r') (s)
  : RWD P (case e r s) (case e r' s)
  := (SCongD.case_left_func e s).mapPath h

def RWD.case_right {P} (e : Term φ) (r) (h : RWD P s s')
  : RWD P (case e r s) (case e r s')
  := (SCongD.case_right_func e r).mapPath h

def RWD.cfg_entry {P} {r r' : Region φ} (h : RWD P r r') (n G)
  : RWD P (cfg r n G) (cfg r' n G)
  := (SCongD.cfg_entry_func n G).mapPath h

def RWD.cfg_block {P} {r r' : Region φ} (β n G i) (h : RWD P r r')
  : RWD P (cfg β n (Function.update G i r)) (cfg β n (Function.update G i r'))
  := (SCongD.cfg_block_func β n G i).mapPath h

def RWD.case {P r r'} (e : Term φ) (hr : RWD P r r') (hs : RWD P s s')
  : RWD P (case e r s) (case e r' s')
  := (case_left e hr s).comp (case_right e r' hs)

def RWD.of_eq {P} {r r' : Region φ} (h : r = r')
  : RWD P r r' := cast_trg (refl r) h

def RWD.cfg_blocks_partial (β n) (G : Fin n → Region φ) (G': Fin n → Region φ)
  (h : ∀i, RWD P (G i) (G' i))
  : ∀k : ℕ, RWD P (Region.cfg β n G) (Region.cfg β n (λi => if i < k then G' i else G i))
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

def RWD.cfg_blocks (β n) (G G' : Fin n → Region φ)
  (h : ∀i, RWD P (G i) (G' i))
  : RWD P (Region.cfg β n G) (Region.cfg β n G')
  := cast_trg (cfg_blocks_partial β n G G' h n) (by simp)

def RWD.dead_cfg_right (Γ : ℕ → ε) (β : Region φ) (n G m G')
  : RWD (PStepD Γ)
    (cfg (β.lwk (n.liftnWk (· + m))) (n + m) (Fin.addCases (lwk (n.liftnWk (· + m)) ∘ G) G'))
    (cfg β n G) :=
    (cast_trg (swap_cfg Γ (β.lwk (n.liftnWk (· + m))) n (lwk (n.liftnWk (· + m)) ∘ G) m G')
      (by
        rw [Fin.comp_addCases, lwk_lwk, <-Function.comp.assoc, comp_lwk, Fin.toNatWk_swapAdd_comp_liftnWk_add]
      )).comp
    (dead_cfg_left Γ β m _ n G)

def RWD.cfg_elim {Γ : ℕ → ε} (β : Region φ) (n G)
  : RWD (PStepD Γ) (cfg (β.lwk (· + n)) n G) β
  := match β with
  | Region.br ℓ e => (cfg_br_ge Γ (ℓ + n) e n G (by simp)).cast_trg (by simp)
  | Region.let1 a β => (cfg_let1 Γ a (β.lwk (· + n)) n G).comp (let1 a (cfg_elim β n _))
  | Region.let2 a β => (cfg_let2 Γ a (β.lwk (· + n)) n G).comp (let2 a (cfg_elim β n _))
  | Region.case e r s =>
    (cfg_case Γ e (r.lwk (· + n)) (s.lwk (· + n)) n G).comp
      (case e (cfg_elim r n _) (cfg_elim s n _))
  | Region.cfg β n' G' => (cfg_cfg Γ _ _ _ _ _).comp (dead_cfg_right Γ _ _ _ _ _)

end Region

end BinSyntax
