import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.CategoryTheory.PathCategory

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

inductive WkCfg : Region φ → Region φ → Prop
  | cfg (β n G k) (ρ : Fin k → Fin n)
    : WkCfg (cfg (β.lwk (Fin.toNatWk ρ)) n G) (cfg β k (G ∘ ρ))

theorem WkCfg.trans {r r' r'' : Region φ}
  (h : WkCfg r r') (h' : WkCfg r' r'') : WkCfg r r'' :=
  by cases h; cases h'; rw [lwk_lwk, <-Fin.toNatWk_comp]; constructor

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

inductive PStepD (Γ : ℕ → ε) : Region φ → Region φ → Type
  | let1_beta (e r) : e.effect Γ = ⊥ → PStepD Γ (let1 e r) (r.vsubst e.subst0)
  | let2_pair (a b r) : PStepD Γ (let2 (pair a b) r) (let1 a $ let1 (b.wk Nat.succ) $ r)
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
  | let2_abort (e r) :
    PStepD Γ (let2 (abort e) r) (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
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
  | wk_cfg (β n G k) (ρ : Fin k → Fin n) :
    PStepD Γ
      (cfg (β.lwk (Fin.toNatWk ρ)) n G)
      (cfg β k ((lwk (Fin.toNatWk ρ)) ∘ G ∘ ρ))

inductive SimpleCongruenceD (P : Region φ → Region φ → Type u) : Region φ → Region φ → Type u
  | step : P r r' → SimpleCongruenceD P r r'
  | let1 (e) : SimpleCongruenceD P r r' → SimpleCongruenceD P (let1 e r) (let1 e r')
  | let2 (e) : SimpleCongruenceD P r r' → SimpleCongruenceD P (let2 e r) (let2 e r')
  | case_left (e) : SimpleCongruenceD P r r' → (s : Region φ)
    → SimpleCongruenceD P (case e r s) (case e r' s)
  | case_right (e r) : SimpleCongruenceD P s s' → SimpleCongruenceD P (case e r s) (case e r s')
  | cfg_entry
    : SimpleCongruenceD P r r' → (n : _) → (G : _) → SimpleCongruenceD P (cfg r n G) (cfg r' n G)
  | cfg_block (β n G i) : SimpleCongruenceD P r r' →
    SimpleCongruenceD P (cfg β n (Function.update G i r)) (cfg β n (Function.update G i r'))

def PSD (Γ : ℕ → ε) : Region φ → Region φ → Type
  := SimpleCongruenceD (PStepD Γ)

def StepD.toPSD {Γ : ℕ → ε} {r r' : Region φ} (h : PStepD Γ r r')
  : PSD Γ r r' := SimpleCongruenceD.step h

def pSDQuiver (Γ : ℕ → ε) : Quiver (Region φ) where
  Hom := PSD Γ

def EStep (φ) (_ : ℕ → ε) := Region φ

def toEStep (Γ : ℕ → ε) (r : Region φ) : EStep φ Γ := r

instance eStepQuiver {Γ : ℕ → ε} : Quiver (EStep φ Γ) where
  Hom := PSD Γ

def EStep.let1_beta (Γ : ℕ → ε) (e r) (h : e.effect Γ = ⊥)
  : @toEStep φ _ Γ (let1 e r) ⟶ toEStep Γ (r.vsubst e.subst0)
  := SimpleCongruenceD.step (PStepD.let1_beta e r h)

def EStep.let2_pair (Γ : ℕ → ε) (a b r)
  : @toEStep φ _ Γ (let2 (pair a b) r) ⟶ toEStep Γ (let1 a $ let1 (b.wk Nat.succ) $ r)
  := SimpleCongruenceD.step (PStepD.let2_pair a b r)

def EStep.case_inl (Γ : ℕ → ε) (e r s)
  : @toEStep φ _ Γ (case (inl e) r s) ⟶ toEStep Γ (let1 e r)
  := SimpleCongruenceD.step (PStepD.case_inl e r s)

def EStep.case_inr (Γ : ℕ → ε) (e r s)
  : @toEStep φ _ Γ (case (inr e) r s) ⟶ toEStep Γ (let1 e s)
  := SimpleCongruenceD.step (PStepD.case_inr e r s)

def EStep.let1_op (Γ : ℕ → ε) (f e r)
  : @toEStep φ _ Γ (let1 (op f e) r) ⟶ toEStep Γ (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := SimpleCongruenceD.step (PStepD.let1_op f e r)

def EStep.let1_pair (Γ : ℕ → ε) (a b r)
  : @toEStep φ _ Γ (let1 (pair a b) r)
    ⟶ toEStep Γ (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) $ r.vwk (Nat.liftWk (· + 2))
  )
  := SimpleCongruenceD.step (PStepD.let1_pair a b r)

def EStep.let1_inl (Γ : ℕ → ε) (e r)
  : @toEStep φ _ Γ (let1 (inl e) r) ⟶ toEStep Γ (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := SimpleCongruenceD.step (PStepD.let1_inl e r)

def EStep.let1_inr (Γ : ℕ → ε) (e r)
  : @toEStep φ _ Γ (let1 (inr e) r) ⟶ toEStep Γ (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := SimpleCongruenceD.step (PStepD.let1_inr e r)

def EStep.let1_abort (Γ : ℕ → ε) (e r)
  : @toEStep φ _ Γ (let1 (abort e) r) ⟶ toEStep Γ (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := SimpleCongruenceD.step (PStepD.let1_abort e r)

def EStep.let2_op (Γ : ℕ → ε) (f e r)
  : @toEStep φ _ Γ (let2 (op f e) r) ⟶ toEStep Γ (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := SimpleCongruenceD.step (PStepD.let2_op f e r)

def EStep.let2_abort (Γ : ℕ → ε) (e r)
  : @toEStep φ _ Γ (let2 (abort e) r) ⟶ toEStep Γ (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := SimpleCongruenceD.step (PStepD.let2_abort e r)

def EStep.let1_case (Γ : ℕ → ε) (a b r s)
  : @toEStep φ _ Γ (let1 a $ case (b.wk Nat.succ) r s)
    ⟶ toEStep Γ (case b (let1 (a.wk Nat.succ) r) (let1 (a.wk Nat.succ) s))
  := SimpleCongruenceD.step (PStepD.let1_case a b r s)

def EStep.let2_case (Γ : ℕ → ε) (a b r s)
  : @toEStep φ _ Γ (let2 a $ case (b.wk (· + 2)) r s)
    ⟶ toEStep Γ (case b (let2 (a.wk Nat.succ) r) (let2 (a.wk Nat.succ) s))
  := SimpleCongruenceD.step (PStepD.let2_case a b r s)

def EStep.cfg_br_lt (Γ : ℕ → ε) (ℓ e n G) (h : ℓ < n)
  : @toEStep φ _ Γ (cfg (br ℓ e) n G) ⟶ toEStep Γ (cfg ((G ⟨ℓ, h⟩).let1 e) n G)
  := SimpleCongruenceD.step (PStepD.cfg_br_lt ℓ e n G h)

def EStep.cfg_br_ge (Γ : ℕ → ε) (ℓ e n G) (h : n ≤ ℓ)
  : @toEStep φ _ Γ (cfg (br ℓ e) n G) ⟶ toEStep Γ (br (ℓ - n) e)
  := SimpleCongruenceD.step (PStepD.cfg_br_ge ℓ e n G h)

def EStep.cfg_let1 (Γ : ℕ → ε) (a β n G)
  : @toEStep φ _ Γ (cfg (let1 a β) n G) ⟶ toEStep Γ (let1 a $ cfg β n (vwk Nat.succ ∘ G))
  := SimpleCongruenceD.step (PStepD.cfg_let1 a β n G)

def EStep.cfg_let2 (Γ : ℕ → ε) (a β n G)
  : @toEStep φ _ Γ (cfg (let2 a β) n G) ⟶ toEStep Γ (let2 a $ cfg β n (vwk (· + 2) ∘ G))
  := SimpleCongruenceD.step (PStepD.cfg_let2 a β n G)

def EStep.cfg_case (Γ : ℕ → ε) (e r s n G)
  : @toEStep φ _ Γ (cfg (case e r s) n G)
    ⟶ toEStep Γ (case e (cfg r n (vwk Nat.succ ∘ G)) (cfg s n (vwk Nat.succ ∘ G))
  )
  := SimpleCongruenceD.step (PStepD.cfg_case e r s n G)

def EStep.cfg_cfg (Γ : ℕ → ε) (β n G n' G')
  : @toEStep φ _ Γ (cfg (cfg β n G) n' G')
    ⟶ toEStep Γ (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
  := SimpleCongruenceD.step (PStepD.cfg_cfg β n G n' G')

def EStep.wk_cfg (Γ : ℕ → ε) (β n G k) (ρ : Fin k → Fin n)
  : @toEStep φ _ Γ (cfg (β.lwk (Fin.toNatWk ρ)) n G)
    ⟶ toEStep Γ (cfg β k ((lwk (Fin.toNatWk ρ)) ∘ G ∘ ρ))
  := SimpleCongruenceD.step (PStepD.wk_cfg β n G k ρ)

def EStep.let1 {Γ : ℕ → ε} (e) (h : @toEStep φ _ Γ r ⟶ toEStep Γ r')
  : @toEStep φ _ Γ (let1 e r) ⟶ toEStep Γ (let1 e r')
  := SimpleCongruenceD.let1 e h

def EStep.let2 {Γ : ℕ → ε} (e) (h : @toEStep φ _ Γ r ⟶ toEStep Γ r')
  : @toEStep φ _ Γ (let2 e r) ⟶ toEStep Γ (let2 e r')
  := SimpleCongruenceD.let2 e h

def EStep.case_left {Γ : ℕ → ε} (e) (h : @toEStep φ _ Γ r ⟶ toEStep Γ r') (s)
  : @toEStep φ _ Γ (case e r s) ⟶ toEStep Γ (case e r' s)
  := SimpleCongruenceD.case_left e h s

def EStep.case_right {Γ : ℕ → ε} (e r) (h : @toEStep φ _ Γ s ⟶ toEStep Γ s')
  : @toEStep φ _ Γ (case e r s) ⟶ toEStep Γ (case e r s')
  := SimpleCongruenceD.case_right e r h

def EStep.cfg_entry {Γ : ℕ → ε} (h : @toEStep φ _ Γ r ⟶ toEStep Γ r') (n G)
  : @toEStep φ _ Γ (cfg r n G) ⟶ toEStep Γ (cfg r' n G)
  := SimpleCongruenceD.cfg_entry h n G

def EStep.cfg_block {Γ : ℕ → ε} (β n G i) (h : @toEStep φ _ Γ r ⟶ toEStep Γ r')
  : (@toEStep φ _ Γ (cfg β n (Function.update G i r))
  ⟶ toEStep Γ (cfg β n (Function.update G i r')))
  := SimpleCongruenceD.cfg_block β n G i h

def EStep.let1_func (Γ : ℕ → ε) (e : Term φ) : Prefunctor (EStep φ Γ) (EStep φ Γ) where
  obj := Region.let1 e
  map := EStep.let1 e

def EStep.let2_func (Γ : ℕ → ε) (e : Term φ) : Prefunctor (EStep φ Γ) (EStep φ Γ) where
  obj := Region.let2 e
  map := EStep.let2 e

def EStep.case_left_func (Γ : ℕ → ε) (e : Term φ) (s : Region φ)
  : Prefunctor (EStep φ Γ) (EStep φ Γ) where
  obj := (Region.case e · s)
  map := (EStep.case_left e · s)

def EStep.case_right_func (Γ : ℕ → ε) (e : Term φ) (r : Region φ)
  : Prefunctor (EStep φ Γ) (EStep φ Γ) where
  obj := Region.case e r
  map := EStep.case_right e r

def EStep.cfg_entry_func (Γ : ℕ → ε) (n) (G : Fin n → Region φ)
  : Prefunctor (EStep φ Γ) (EStep φ Γ) where
  obj := (Region.cfg · n G)
  map := (EStep.cfg_entry · n G)

def EStep.cfg_block_func (Γ : ℕ → ε) (β : Region φ) (n) (G : Fin n → Region φ) (i : Fin n)
  : Prefunctor (EStep φ Γ) (EStep φ Γ) where
  obj := (λg => Region.cfg β n (Function.update G i g))
  map := EStep.cfg_block β n G i

def EStep.let1_path {Γ : ℕ → ε} (e) (h : Quiver.Path (@toEStep φ _ Γ r) r')
  : Quiver.Path (toEStep Γ (Region.let1 e r)) (Region.let1 e r')
  := (let1_func Γ e).mapPath h

def EStep.let2_path {Γ : ℕ → ε} (e) (h : Quiver.Path (@toEStep φ _ Γ r) r')
  : Quiver.Path (toEStep Γ (Region.let2 e r)) (Region.let2 e r')
  := (let2_func Γ e).mapPath h

def EStep.case_left_path {Γ : ℕ → ε} (e) (h : Quiver.Path (@toEStep φ _ Γ r) r') (s)
  : Quiver.Path (toEStep Γ (Region.case e r s)) (Region.case e r' s)
  := (case_left_func Γ e s).mapPath h

def EStep.case_right_path {Γ : ℕ → ε} (e r) (h : Quiver.Path (@toEStep φ _ Γ s) s')
  : Quiver.Path (toEStep Γ (Region.case e r s)) (Region.case e r s')
  := (case_right_func Γ e r).mapPath h

def EStep.case_path {Γ : ℕ → ε} (e)
  (hr : Quiver.Path (@toEStep φ _ Γ r) r')
  (hs : Quiver.Path (@toEStep φ _ Γ s) s')
  : Quiver.Path (toEStep Γ (Region.case e r s)) (Region.case e r' s')
  := Quiver.Path.comp (case_left_path e hr _) (case_right_path e _ hs)

def EStep.cfg_entry_path {Γ : ℕ → ε} (n G) (h : Quiver.Path (@toEStep φ _ Γ r) r')
  : Quiver.Path (toEStep Γ (Region.cfg r n G)) (Region.cfg r' n G)
  := (cfg_entry_func Γ n G).mapPath h

def EStep.cfg_block_path {Γ : ℕ → ε} (β n G i) (h : Quiver.Path (@toEStep φ _ Γ r) r')
  : Quiver.Path
    (toEStep Γ (Region.cfg β n (Function.update G i r)))
    (Region.cfg β n (Function.update G i r'))
  := (cfg_block_func Γ β n G i).mapPath h

def EStep.cast_path_trg {Γ : ℕ → ε} {r₁ r₂ r₂' : Region φ}
  (h : Quiver.Path (@toEStep φ _ Γ r₁) r₂) (h' : r₂ = r₂')
  : Quiver.Path (@toEStep φ _ Γ r₁) r₂' := h' ▸ h

def EStep.cast_path_src {Γ : ℕ → ε} {r₁ r₁' r₂ : Region φ}
  (h' : r₁ = r₁') (h : Quiver.Path (@toEStep φ _ Γ r₁') r₂)
  : Quiver.Path (@toEStep φ _ Γ r₁) r₂ := h' ▸ h

def EStep.refl_path {Γ : ℕ → ε} {r : Region φ}
  : Quiver.Path (@toEStep φ _ Γ r) r := Quiver.Path.nil

def EStep.path_of_eq {Γ : ℕ → ε} {r r' : Region φ} (h : r = r')
  : Quiver.Path (@toEStep φ _ Γ r) r' := cast_path_trg refl_path h

def EStep.cfg_blocks_partial {Γ : ℕ → ε} (β n) (G : Fin n → Region φ) (G': Fin n → Region φ)
  (h : ∀i, Quiver.Path (@toEStep φ _ Γ (G i)) (G' i))
  : ∀k : ℕ, Quiver.Path
    (toEStep Γ (Region.cfg β n G))
    (Region.cfg β n (λi => if i < k then G' i else G i))
  | 0 => Quiver.Path.nil
  | k + 1 => if hk : k < n then
      Quiver.Path.comp
        (cast_path_trg (cfg_blocks_partial β n G G' h k)
          (by
            congr
            rw [Function.eq_update_self_iff]
            simp))
        (cast_path_trg (cfg_block_path β n
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
      cast_path_trg (cfg_blocks_partial β n G G' h k) (by
        have hk := Nat.le_of_not_lt hk;
        simp only [cfg.injEq, heq_eq_eq, true_and]
        funext i
        have hi := Nat.lt_of_lt_of_le i.prop hk
        simp [hi, Nat.lt_succ_of_lt hi]
      )

def EStep.cfg_blocks {Γ : ℕ → ε} (β n G G')
  (h : ∀i, Quiver.Path (@toEStep φ _ Γ (G i)) (G' i))
  : Quiver.Path
    (toEStep Γ (Region.cfg β n G))
    (Region.cfg β n G')
  := cast_path_trg (cfg_blocks_partial β n G G' h n) (by simp)

def EStep.cfg_elim {Γ : ℕ → ε} (β : Region φ) (n G)
  : Quiver.Path (toEStep Γ (cfg (β.lwk (· + n)) n G)) β
  := match β with
  | Region.br ℓ e =>
    have h : ℓ + n - n = ℓ := by simp;
    (h ▸ cfg_br_ge Γ (ℓ + n) e n G (by simp)).toPath
  | Region.let1 a β =>
    Quiver.Path.comp
      (cfg_let1 Γ a (β.lwk (· + n)) n G).toPath
      (let1_path a (cfg_elim β n _))
  | Region.let2 a β =>
    Quiver.Path.comp
      (cfg_let2 Γ a (β.lwk (· + n)) n G).toPath
      (let2_path a (cfg_elim β n _))
  | Region.case e r s =>
    Quiver.Path.comp
      (cfg_case Γ e (r.lwk (· + n)) (s.lwk (· + n)) n G).toPath
      (case_path e (cfg_elim r n _) (cfg_elim s n _))
  | Region.cfg β n' G' =>
    Quiver.Path.comp
      (cfg_cfg Γ _ _ _ _ _).toPath
      (cast_path_src
        (by
          simp only [cfg.injEq, heq_eq_eq, true_and]
          constructor
          congr
          funext i
          rw [Fin.toNatWk, Nat.liftnWk]
          split
          rfl
          rw [Nat.add_assoc, Nat.add_comm n n']
          funext i
          simp only [Fin.addCases, Function.comp_apply, eq_rec_constant]
          split
          . rw [lwk_lwk]
            congr
            funext i'
            rw [Function.comp_apply, Fin.toNatWk]
          . sorry
        )
        (cast_path_trg (wk_cfg _ β (n + n')
          (Fin.addCases (lwk (· + n') ∘ G) (lwk (n.liftnWk (· + n')) ∘ G')) _ (
            Fin.castLE (Nat.le_add_left n' n)
          )).toPath
          (by
            congr
            funext i
            simp only [Fin.addCases, Function.comp_apply, eq_rec_constant, Fin.castLE, i.prop,
              ↓reduceDite, Fin.castLT_mk, Fin.eta]
            sorry
          )))

end Region

end BinSyntax
