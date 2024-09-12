import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.CategoryTheory.PathCategory
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Discretion.Correspondence.Definitions

import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Effect.Subst
import DeBruijnSSA.BinSyntax.Syntax.Fv

import DeBruijnSSA.BinSyntax.Syntax.Rewrite.Region.Rewrite
import DeBruijnSSA.BinSyntax.Syntax.Rewrite.Region.Equiv
import DeBruijnSSA.BinSyntax.Syntax.Rewrite.Region.Reduce
import DeBruijnSSA.BinSyntax.Syntax.Rewrite.Region.Step

import DeBruijnSSA.BinSyntax.Syntax.Rewrite.Region.Cong

namespace BinSyntax

variable {φ : Type u} {ε : Type v} [Φ: EffectSet φ ε] [SemilatticeSup ε] [OrderBot ε]

-- -- TODO: define as Subst.cons or smt...
-- def Term.subst₂ (a b: Term φ) : Subst φ
--   | 0 => a
--   | 1 => b
--   | n + 2 => Term.var n

namespace Region

open Term

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
  := single $ BCongD.rel $ StepD.let1_beta e r h

def RWD.case_inl {Γ : ℕ → ε} (e) (r s : Region φ)
  : RWD StepD Γ (case (inl e) r s) (let1 e r)
  := single $ BCongD.rel $ StepD.case_inl e r s

def RWD.case_inr {Γ : ℕ → ε} (e) (r s : Region φ)
  : RWD StepD Γ (case (inr e) r s) (let1 e s)
  := single $ BCongD.rel $ StepD.case_inr e r s

def RWD.let1_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : RWD StepD Γ (let1 (op f e) r) (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := single $ BCongD.rel $ StepD.let1_op f e r

def RWD.let1_op_op {Γ : ℕ → ε} (f e) (r : Region φ)
  : RWD StepD Γ (let1 e $ let1 (op f (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (op f e) r)
  := single $ BCongD.rel $ StepD.let1_op_op f e r

def RWD.let1_pair {Γ : ℕ → ε} (a b) (r : Region φ)
  : RWD StepD Γ (let1 (pair a b) r)
    (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) r.vwk1.vwk1
  )
  := single $ BCongD.rel $ StepD.let1_pair a b r

def RWD.let1_pair_op {Γ : ℕ → ε} (a b) (r : Region φ)
  : RWD StepD Γ (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) r.vwk1.vwk1)
    (let1 (pair a b) r)
  := single $ BCongD.rel $ StepD.let1_pair_op a b r

def RWD.let1_inl {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 (inl e) r) (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := single $ BCongD.rel $ StepD.let1_inl e r

def RWD.let1_inl_op {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 e $ let1 (inl (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (inl e) r)
  := single $ BCongD.rel $ StepD.let1_inl_op e r

def RWD.let1_inr {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 (inr e) r) (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := single $ BCongD.rel $ StepD.let1_inr e r

def RWD.let1_inr_op {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 e $ let1 (inr (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (inr e) r)
  := single $ BCongD.rel $ StepD.let1_inr_op e r

def RWD.let1_abort {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 (abort e) r) (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
  := single $ BCongD.rel $ StepD.let1_abort e r

def RWD.let1_abort_op {Γ : ℕ → ε} (e) (r : Region φ)
  : RWD StepD Γ (let1 e $ let1 (abort (var 0)) $ r.vwk (Nat.liftWk Nat.succ))
    (let1 (abort e) r)
  := single $ BCongD.rel $ StepD.let1_abort_op e r

def RWD.cfg_br_lt {Γ : ℕ → ε} (ℓ) (e : Term φ) (n G) (h : ℓ < n)
  : RWD StepD Γ (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).let1 e) n G)
  := single $ BCongD.rel $ StepD.cfg_br_lt ℓ e n G h

def RWD.cfg_br_lt_op {Γ : ℕ → ε} (ℓ) (e : Term φ) (n G) (h : ℓ < n)
  : RWD StepD Γ (cfg ((G ⟨ℓ, h⟩).let1 e) n G) (cfg (br ℓ e) n G)
  := single $ BCongD.rel $ StepD.cfg_br_lt_op ℓ e n G h

-- def RWD.cfg_let1 {Γ : ℕ → ε} (a : Term φ) (β n G)
--   : RWD StepD Γ (cfg (let1 a β) n G) (let1 a $ cfg β n (vwk1 ∘ G))
--   := single $ BCongD.rel $ StepD.cfg_let1 a β n G

-- def RWD.cfg_let1_op {Γ : ℕ → ε} (a : Term φ) (β n G)
--   : RWD StepD Γ (let1 a $ cfg β n (vwk1 ∘ G))
--     (cfg (let1 a β) n G)
--   := single $ BCongD.rel $ StepD.cfg_let1_op a β n G

-- def RWD.cfg_let2 {Γ : ℕ → ε} (a : Term φ) (β n G)
--   : RWD StepD Γ (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk1 ∘ vwk1 ∘ G))
--   := single $ BCongD.rel $ StepD.cfg_let2 a β n G

-- def RWD.cfg_let2_op {Γ : ℕ → ε} (a : Term φ) (β n G)
--   : RWD StepD Γ (let2 a $ cfg β n (vwk1 ∘ vwk1 ∘ G))
--     (cfg (let2 a β) n G)
--   := single $ BCongD.rel $ StepD.cfg_let2_op a β n G

-- def RWD.cfg_case {Γ : ℕ → ε} (e : Term φ) (r s n G)
--   : RWD StepD Γ (cfg (case e r s) n G)
--     (case e (cfg r n (vwk1 ∘ G)) (cfg s n (vwk1 ∘ G))
--   )
--   := single $ BCongD.rel $ StepD.cfg_case e r s n G

-- def RWD.cfg_case_op {Γ : ℕ → ε} (e : Term φ) (r s n G)
--   : RWD StepD Γ (case e (cfg r n (vwk1 ∘ G)) (cfg s n (vwk1 ∘ G)))
--     (cfg (case e r s) n G)
--   := single $ BCongD.rel $ StepD.cfg_case_op e r s n G

-- def RWD.cfg_cfg {Γ : ℕ → ε} (β : Region φ) (n G n' G')
--   : RWD StepD Γ (cfg (cfg β n G) n' G') (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
--   := single $ BCongD.rel $ StepD.cfg_cfg β n G n' G'

-- def RWD.cfg_cfg_op {Γ : ℕ → ε} (β : Region φ) (n G n' G')
--   : RWD StepD Γ (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
--     (cfg (cfg β n G) n' G')
--   := single $ BCongD.rel $ StepD.cfg_cfg_op β n G n' G'

-- def RWD.cfg_zero {Γ : ℕ → ε} (β : Region φ) (G)
--   : RWD StepD Γ (cfg β 0 G) β := single $ BCongD.rel $ StepD.cfg_zero β G

-- def RWD.cfg_zero_op {Γ : ℕ → ε} (β : Region φ) (G)
--   : RWD StepD Γ β (cfg β 0 G) := single $ BCongD.rel $ StepD.cfg_zero_op β G

-- def RWD.wk_cfg {Γ : ℕ → ε} (β : Region φ) (n G k) (ρ : Fin k → Fin n) /-(hρ : Function.Bijective ρ)-/
--   : RWD StepD Γ
--     (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
--     (cfg β k (G ∘ ρ))
--   := single $ BCongD.rel $ StepD.wk_cfg β n G k ρ

-- def RWD.dead_cfg_left {Γ : ℕ → ε} (β : Region φ) (n G m G')
--   : RWD StepD Γ
--     (cfg (β.lwk (· + n)) (n + m) (Fin.addCases G (lwk (· + n) ∘ G')))
--     (cfg β m G')
--   := single $ BCongD.rel $ StepD.dead_cfg_left β n G m G'

-- def RWD.swap_cfg' {Γ : ℕ → ε} (β : Region φ) (n G m G')
--   : RWD StepD Γ
--     (cfg
--       (lwk (Fin.toNatWk (Fin.swapAdd n m)) β)
--       (m + n) (lwk (Fin.toNatWk (Fin.swapAdd n m)) ∘ Fin.addCases G' G))
--     (cfg β (n + m) (Fin.addCases G G'))
--   :=
--   have h : Fin.addCases G G' = Fin.addCases G' G ∘ Fin.swapAdd n m := by
--     rw [Fin.addCases_comp_swapAdd]
--   by
--     rw [h]
--     apply wk_cfg

def RWD.cast_trg {P} {Γ : ℕ → ε} {r₀ r₁ r₁' : Region φ} (h : RWD P Γ r₀ r₁) (hr₁ : r₁ = r₁')
  : RWD P Γ r₀ r₁'
  := Corr.Path.cast_trg h hr₁

def RWD.cast_src {P} {Γ : ℕ → ε} {r₀ r₀' r₁ : Region φ} (hr₀ : r₀ = r₀') (h : RWD P Γ r₀' r₁)
  : RWD P Γ r₀ r₁
  := Corr.Path.cast_src hr₀ h

def RWD.cast {P} {Γ : ℕ → ε} {r₀ r₀' r₁ r₁' : Region φ} (hr₀ : r₀ = r₀') (hr₁ : r₁ = r₁')
  (h : RWD P Γ r₀ r₁) : RWD P Γ r₀' r₁'
  := Corr.Path.cast hr₀ hr₁ h

-- def RWD.swap_cfg {Γ : ℕ → ε} (β : Region φ) (n G m G')
--   : RWD StepD Γ
--     (cfg β (n + m) (Fin.addCases G G'))
--     (cfg
--       (lwk (Fin.toNatWk (Fin.swapAdd n m)) β)
--       (m + n) (lwk (Fin.toNatWk (Fin.swapAdd n m)) ∘ Fin.addCases G' G))
--   := cast_trg (cast_src
--     (by
--       rw [
--         <-Fin.comp_addCases,
--         <-Function.comp.assoc,
--         lwk_lwk, comp_lwk,
--         Fin.swapAdd
--       ]
--       simp [<-Fin.toNatWk_comp, Fin.addCases_natAdd_castAdd_nil]
--     )
--     (swap_cfg'
--       (β.lwk (Fin.toNatWk (Fin.addCases (Fin.natAdd m) (Fin.castAdd n))))
--       m
--       (lwk (Fin.toNatWk (Fin.addCases (Fin.natAdd m) (Fin.castAdd n))) ∘ G')
--       n
--       (lwk (Fin.toNatWk (Fin.addCases (Fin.natAdd m) (Fin.castAdd n))) ∘ G)))
--     (by simp [Fin.comp_addCases, Fin.swapAdd])

def RWD.let1V0_id {Γ : ℕ → ε} (r : Region φ) (hΓ : Γ 0 = ⊥)
  : RWD StepD Γ r.let1V0 r
  := cast_trg
    (let1_beta (Term.var 0) (r.vwk (Nat.liftWk Nat.succ)) hΓ)
    (by rw [<-vsubst_fromWk_apply, vsubst_vsubst, vsubst_id']; funext i; cases i <;> rfl)

def RWD.let2_eta {Γ : ℕ → ε} (r : Region φ)
  : RWD StepD Γ
    (let2 e $
     let1 ((Term.var 1).pair (Term.var 0)) $
     r.vwk1.vwk1) (let1 e r)
  := single $ BCongD.rel $ StepD.let2_eta e r

def RWD.let2_eta_op {Γ : ℕ → ε} (r : Region φ)
  : RWD StepD Γ (let1 (Term.var 0) r)
    (let2 (Term.var 0) $
     let1 ((Term.var 1).pair (Term.var 0)) $
     r.vwk1.vwk1)
  := single $ BCongD.rel $ StepD.let2_eta_op r

-- def RWD.let1_eta {Γ : ℕ → ε} (r : Region φ)
--   : RWD StepD Γ
--     (let1 (Term.var 0) $
--      r.vwk1) r
--   := single $ BCongD.rel $ StepD.let1_eta r

-- def RWD.let1_eta_op {Γ : ℕ → ε} (r : Region φ)
--   : RWD StepD Γ r
--     (let1 (Term.var 0) $
--      r.vwk1)
--   := single $ BCongD.rel $ StepD.let1_eta_op r

instance instTransRWD
  {P : (ℕ → ε) → Region φ → Region φ → Type _} {Γ}
  : Trans (RWD P Γ) (RWD P Γ) (RWD P Γ) where
  trans := RWD.comp

-- infixr:10 " ⟶R " => λ{P Γ} => RWD P Γ

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
                  (Fin.val_ne_of_ne he)
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

-- def RWD.dead_cfg_right {Γ : ℕ → ε} (β : Region φ) (n G m G')
--   : RWD StepD Γ
--     (cfg (β.lwk (n.liftnWk (· + m))) (n + m) (Fin.addCases (lwk (n.liftnWk (· + m)) ∘ G) G'))
--     (cfg β n G) :=
--     (cast_trg (swap_cfg (β.lwk (n.liftnWk (· + m))) n (lwk (n.liftnWk (· + m)) ∘ G) m G')
--       (by rw [
--         Fin.comp_addCases, lwk_lwk, <-Function.comp.assoc, comp_lwk,
--         Fin.toNatWk_swapAdd_comp_liftnWk_add]
--       )).comp
--     (dead_cfg_left β m _ n G)

-- def RWD.cfg_elim {Γ : ℕ → ε} (β : Region φ) (n G)
--   : RWD StepD Γ (cfg (β.lwk (· + n)) n G) β
--   :=
--   let s : RWD StepD Γ
--     (cfg (β.lwk (· + n)) n G)
--     (cfg (β.lwk (· + n)) (n + 0) (Fin.addCases G (lwk (· + n) ∘ Fin.elim0)))
--     := RWD.of_eq (by simp [Fin.addCases_zero])
--   (s.comp (dead_cfg_left β n G 0 Fin.elim0)).comp (RWD.cfg_zero _ _)
  -- := match β with
  -- | Region.br ℓ e => (cfg_br_ge (ℓ + n) e n G (by simp)).cast_trg (by simp)
  -- | Region.let1 a β => (cfg_let1 a (β.lwk (· + n)) n G).comp (let1 a (cfg_elim β n _))
  -- | Region.let2 a β => (cfg_let2 a (β.lwk (· + n)) n G).comp (let2 a (cfg_elim β n _))
  -- | Region.case e r s =>
  --   (cfg_case e (r.lwk (· + n)) (s.lwk (· + n)) n G).comp
  --     (case e (cfg_elim r n _) (cfg_elim s n _))
  -- | Region.cfg β n' G' => (cfg_cfg _ _ _ _ _).comp (dead_cfg_right _ _ _ _ _)

-- def RWD.cfg_br_ge {Γ : ℕ → ε} (ℓ) (e : Term φ) (n G) (h : n ≤ ℓ)
--   : RWD StepD Γ (cfg (br ℓ e) n G) (br (ℓ - n) e)
--   := cast_src (by simp [h]) (cfg_elim (br (ℓ - n) e) n G)

-- TODO: vwk, lwk lore...
