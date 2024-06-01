import Mathlib.Combinatorics.Quiver.Path

import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Effect

namespace BinSyntax

variable [Φ: EffectSet φ ε] [SemilatticeSup ε] [OrderBot ε]

-- TODO: define as Subst.cons or smt...
def Term.subst₂ (a b: Term φ) : Subst φ
  | 0 => a
  | 1 => b
  | n + 2 => Term.var n

inductive Region.PureBeta (Γ : ℕ → ε) : Region φ → Region φ → Prop
  | let1 (e : Term φ) (r : Region φ)
    : e.effect Γ = ⊥ → PureBeta Γ (r.let1 e) (r.vsubst e.subst0)

theorem Region.PureBeta.let1_pure {Γ : ℕ → ε} {e} {r r' : Region φ}
  (h : Region.PureBeta Γ (r.let1 e) r') : e.effect Γ = ⊥ := by cases h; assumption

theorem Region.PureBeta.let1_trg {Γ : ℕ → ε} {e} {r r' : Region φ}
  (h : Region.PureBeta Γ (r.let1 e) r') : r' = r.vsubst e.subst0 := by cases h; rfl

inductive Region.Reduce : Region φ → Region φ → Prop
  | let2_pair (a b r) : Reduce (let2 (Term.pair a b) r) (let1 a $ let1 (b.wk Nat.succ) $ r)
  | case_inl (e r s) : Reduce (case (Term.inl e) r s) (let1 e r)
  | case_inr (e r s) : Reduce (case (Term.inr e) r s) (let1 e s)

theorem Region.Reduce.let2_pair_trg {a b} {r r' : Region φ}
  (h : Region.Reduce (Region.let2 (Term.pair a b) r) r')
  : r' = (Region.let1 a $ Region.let1 (b.wk Nat.succ) $ r) := by cases h; rfl

theorem Region.Reduce.case_inl_trg {e} {r s r' : Region φ}
  (h : Region.Reduce (Region.case (Term.inl e) r s) r')
  : r' = (Region.let1 e r) := by cases h; rfl

theorem Region.Reduce.case_inr_trg {e} {r s s' : Region φ}
  (h : Region.Reduce (Region.case (Term.inr e) r s) s')
  : s' = (Region.let1 e s) := by cases h; rfl

inductive Region.TermEta1 : Region φ → Region φ → Prop
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

theorem Region.TermEta1.let1_op_trg {f e} {r r' : Region φ}
  (h : Region.TermEta1 (Region.let1 (Term.op f e) r) r')
  : r' = (Region.let1 e $ Region.let1 (Term.op f (Term.var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := by cases h; rfl

theorem Region.TermEta1.let1_pair_trg {a b} {r r' : Region φ}
  (h : Region.TermEta1 (Region.let1 (Term.pair a b) r) r')
  : r' = (Region.let1 a
    $ Region.let1 (b.wk Nat.succ)
    $ Region.let1 (Term.pair (Term.var 1) (Term.var 0))
    $ r.vwk (Nat.liftWk (· + 2)))
  := by cases h; rfl

theorem Region.TermEta1.let1_inl_trg {e} {r r' : Region φ}
  (h : Region.TermEta1 (Region.let1 (Term.inl e) r) r')
  : r' = (Region.let1 e $ Region.let1 (Term.inl (Term.var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := by cases h; rfl

theorem Region.TermEta1.let1_inr_trg {e} {r r' : Region φ}
  (h : Region.TermEta1 (Region.let1 (Term.inr e) r) r')
  : r' = (Region.let1 e $ Region.let1 (Term.inr (Term.var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := by cases h; rfl

theorem Region.TermEta1.let1_abort_trg {e} {r r' : Region φ}
  (h : Region.TermEta1 (Region.let1 (Term.abort e) r) r')
  : r' = (Region.let1 e $ Region.let1 (Term.abort (Term.var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := by cases h; rfl

inductive Region.TermEta2 : Region φ → Region φ → Prop
  | let2_op (f e r) : TermEta2 (let2 (Term.op f e) r) (let1 e
      $ let2 (Term.op f (Term.var 0))
      $ r.vwk (Nat.liftnWk 2 Nat.succ))
  | let2_abort (e r) : TermEta2 (let2 (Term.abort e) r) (let1 e
      $ let2 (Term.abort (Term.var 0))
      $ r.vwk (Nat.liftnWk 2 Nat.succ))

inductive Region.Eta : Region φ → Region φ → Prop
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
    (cfg (br (ℓ - n) e) n G)
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
    (cfg β (n' + n) (Fin.addCases (lwk (· + n) ∘ G') G))

inductive Region.WkCfg : Region φ → Region φ → Prop
  | cfg (β n G k) (ρ : Fin k → Fin n)
    : WkCfg (cfg (β.lwk (Fin.toNatWk ρ)) n G) (cfg β k (G ∘ ρ))

theorem Region.WkCfg.trans {r r' r'' : Region φ}
  (h : Region.WkCfg r r') (h' : Region.WkCfg r' r'') : Region.WkCfg r r'' :=
  by cases h; cases h'; rw [lwk_lwk, <-Fin.toNatWk_comp]; constructor

inductive Region.SimpleCongruence (P : Region φ → Region φ → Prop) : Region φ → Region φ → Prop
  | step (r r') : P r r' → SimpleCongruence P r r'
  | let1 (e r r') : SimpleCongruence P r r' → SimpleCongruence P (let1 e r) (let1 e r')
  | let2 (e r r') : SimpleCongruence P r r' → SimpleCongruence P (let2 e r) (let2 e r')
  | case_left (e r s r') : SimpleCongruence P r r' → SimpleCongruence P (case e r s) (case e r' s)
  | case_right (e r s s') : SimpleCongruence P s s' → SimpleCongruence P (case e r s) (case e r s')
  | cfg_entry (r r' n G) : SimpleCongruence P r r' → SimpleCongruence P (cfg r n G) (cfg r' n G)
  | cfg_block (r r' n G i G') : SimpleCongruence P r r' → G' = Function.update G i r' →
    SimpleCongruence P (cfg β n G) (cfg β n G')

theorem Region.SimpleCongruence.refl (hP : IsRefl _ P) (r : Region φ) : SimpleCongruence P r r :=
  step _ _ (hP.refl r)

open Term

inductive Region.PStepD (Γ : ℕ → ε) : Region φ → Region φ → Type
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
    PStepD Γ (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).vsubst e.subst0) n G)
  | cfg_br_ge (ℓ e n G) (h : n ≤ ℓ) :
    PStepD Γ (cfg (br ℓ e) n G) (cfg (br (ℓ - n) e) n G)
  | cfg_let1 (a β n G) :
    PStepD Γ (cfg (let1 a β) n G) (let1 a $ cfg β n (vwk Nat.succ ∘ G))
  | cfg_let2 (a β n G) :
    PStepD Γ (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk (· + 2) ∘ G))
  | cfg_case (e r s n G) :
    PStepD Γ (cfg (case e r s) n G)
      (case e (cfg r n (vwk Nat.succ ∘ G)) (cfg s n (vwk Nat.succ ∘ G)))
  | cfg_cfg (β n G n' G') :
    PStepD Γ (cfg (cfg β n G) n' G') (cfg β (n' + n) (Fin.addCases (lwk (· + n) ∘ G') G))
  | wk_cfg (β n G k) (ρ : Fin k → Fin n) :
    PStepD Γ (cfg (β.lwk (Fin.toNatWk ρ)) n G) (cfg β k (G ∘ ρ))

inductive Region.SimpleCongruenceD (P : Region φ → Region φ → Type u) : Region φ → Region φ → Type u
  | step (r r') : P r r' → SimpleCongruenceD P r r'
  | let1 (e r r') : SimpleCongruenceD P r r' → SimpleCongruenceD P (let1 e r) (let1 e r')
  | let2 (e r r') : SimpleCongruenceD P r r' → SimpleCongruenceD P (let2 e r) (let2 e r')
  | case_left (e r s r') : SimpleCongruenceD P r r' → SimpleCongruenceD P (case e r s) (case e r' s)
  | case_right (e r s s') : SimpleCongruenceD P s s'
    → SimpleCongruenceD P (case e r s) (case e r s')
  | cfg_entry (r r' n G) : SimpleCongruenceD P r r' → SimpleCongruenceD P (cfg r n G) (cfg r' n G)
  | cfg_block (r r' n G i G') : SimpleCongruenceD P r r' → G' = Function.update G i r' →
    SimpleCongruenceD P (cfg β n G) (cfg β n G')

def Region.pStepQuiver (Γ : ℕ → ε) : Quiver (Region φ) where
  Hom := SimpleCongruenceD (PStepD Γ)

end BinSyntax
