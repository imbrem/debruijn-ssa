import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.CategoryTheory.PathCategory
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Discretion.Correspondence.Definitions

import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Effect.Subst
import DeBruijnSSA.BinSyntax.Syntax.Fv

import DeBruijnSSA.BinSyntax.Syntax.Rewrite.Region.Rewrite
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

-- TODO: CongD is effect monotone/antitone iff underlying is
-- ==> CongD is effect preserving iff underlying is

-- TODO: make these rewrites bidirectional


-- TODO: fix this to fuse...
instance instSetoid : Setoid (Region φ) := Relation.EqvGen.setoid (Cong Rewrite)

theorem eqv_let1 (e) (p : r ≈ r') : @let1 φ e r ≈ let1 e r'
  := Cong.eqv_let1 e p

theorem eqv_let2 (e) (p : r ≈ r') : @let2 φ e r ≈ let2 e r'
  := Cong.eqv_let2 e p

theorem eqv_case_left (e) (p : r ≈ r') (s) : @case φ e r s ≈ case e r' s
  := Cong.eqv_case_left e p s

theorem eqv_case_right (e r) (p : s ≈ s') : @case φ e r s ≈ case e r s'
  := Cong.eqv_case_right e r p

theorem eqv_case (e) (pr : r ≈ r') (ps : s ≈ s') : @case φ e r s ≈ case e r' s'
  := Cong.eqv_case e pr ps

theorem eqv_cfg_entry (p : r ≈ r') (n) (G) : @cfg φ r n G ≈ cfg r' n G
  := Cong.eqv_cfg_entry p n G

theorem eqv_cfg_block (β n G i) (p : G i ≈ g')
  : @cfg φ β n G ≈ cfg β n (Function.update G i g')
  := Cong.eqv_cfg_block β n G i p

theorem eqv_cfg_blocks (β n G G') (p : G ≈ G')
  : @cfg φ β n G ≈ cfg β n G'
  := Cong.eqv_cfg_blocks β n G G' p

theorem eqv_cfg (pβ : β ≈ β) (n) {G G' : Fin n → Region φ} (pG : G ≈ G')
  : @cfg φ β n G ≈ cfg β n G'
  := Cong.eqv_cfg pβ n pG

theorem eqv_let1_op {f e r} : @let1 φ (op f e) r ≈ (let1 e $ let1 (op f (var 0)) $ r.vwk1)
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.let1_op f e r

theorem eqv_let1_let1 {a b r} : @let1 φ (a.let1 b) r ≈ (let1 a $ let1 b $ r.vwk1)
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.let1_let1 a b r

theorem eqv_let1_pair {a b r}
  : @let1 φ (pair a b) r ≈ (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) $ r.vwk1.vwk1)
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.let1_pair a b r

theorem eqv_let1_let2 {a b r} : @let1 φ (a.let2 b) r ≈ (let2 a $ let1 b $ r.vwk1.vwk1)
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.let1_let2 a b r

theorem eqv_let1_inl {e r} : @let1 φ (inl e) r ≈ (let1 e $ let1 (inl (var 0)) $ r.vwk1)
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.let1_inl e r

theorem eqv_let1_inr {e r} : @let1 φ (inr e) r ≈ (let1 e $ let1 (inr (var 0)) $ r.vwk1)
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.let1_inr e r

theorem eqv_let1_abort {e r} : @let1 φ (abort e) r ≈ (let1 e $ let1 (abort (var 0)) $ r.vwk1)
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.let1_abort e r

theorem eqv_let2_bind {e r} : @let2 φ e r ≈ (let1 e $ let2 (var 0) $ r.vwk (Nat.liftnWk 2 Nat.succ))
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.let2_bind e r

theorem eqv_case_bind {e r s}
  : @case φ e r s ≈ (let1 e $ case (var 0) (r.vwk1) (s.vwk1))
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.case_bind e r s

-- TODO: go prove

-- theorem eqv_let2_op {f e r}
--   : @let2 φ (op f e) r ≈ (let1 e $ let2 (op f (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
--   := sorry--EqvGen.rel _ _ $ Cong.rel $ Rewrite.let2_op f e r

-- theorem eqv_let2_pair {a b r}
--   : @let2 φ (pair a b) r ≈ (let1 a $ let1 (b.wk Nat.succ) $ r)
--   := sorry--EqvGen.rel _ _ $ Cong.rel $ Rewrite.let2_pair a b r

-- theorem eqv_let2_abort {e r}
--   : @let2 φ (abort e) r ≈ (let1 e $ let2 (abort (var 0)) $ r.vwk (Nat.liftnWk 2 Nat.succ))
--   := sorry--EqvGen.rel _ _ $ Cong.rel $ Rewrite.let2_abort e r

-- theorem eqv_case_op {f e r s}
--   : @case φ (op f e) r s ≈ (let1 e $ case (op f (var 0)) (r.vwk1) (s.vwk1))
--   := sorry--EqvGen.rel _ _ $ Cong.rel $ Rewrite.case_op f e r s

-- theorem eqv_case_abort {e r s}
--   : @case φ (abort e) r s ≈ (let1 e $ case (abort (var 0)) (r.vwk1) (s.vwk1))
--   := sorry--EqvGen.rel _ _ $ Cong.rel $ Rewrite.case_abort e r s

-- theorem eqv_let1_case {a b r s}
--   : (@let1 φ a $ case (b.wk Nat.succ) r s)
--   ≈ case b (let1 (a.wk Nat.succ) (r.vwk (Nat.swap0 1))) (let1 (a.wk Nat.succ) (s.vwk (Nat.swap0 1)))
--   := EqvGen.rel _ _ $ Cong.rel $ Rewrite.let1_case a b r s

-- theorem eqv_let2_case {a b r s}
--   : (@let2 φ a $ case (b.wk (· + 2)) r s)
--   ≈ case b (let2 (a.wk Nat.succ) (r.vwk (Nat.swap0 2))) (let2 (a.wk Nat.succ) (s.vwk (Nat.swap0 2)))
--   := EqvGen.rel _ _ $ Cong.rel $ Rewrite.let2_case a b r s

theorem eqv_cfg_br_lt {ℓ e n G} (h : ℓ < n)
  : @cfg φ (br ℓ e) n G ≈ cfg ((G ⟨ℓ, h⟩).let1 e) n G
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.cfg_br_lt ℓ e n G h

theorem eqv_cfg_let1 {a β n G}
  : @cfg φ (let1 a β) n G ≈ (let1 a $ cfg β n (vwk1 ∘ G))
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.cfg_let1 a β n G

theorem eqv_cfg_let2 {a β n G}
  : @cfg φ (let2 a β) n G ≈ (let2 a $ cfg β n (vwk1 ∘ vwk1 ∘ G))
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.cfg_let2 a β n G

theorem eqv_cfg_case {e r s n G}
  : @cfg φ (case e r s) n G
    ≈ case e (cfg r n (vwk1 ∘ G)) (cfg s n (vwk1 ∘ G))
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.cfg_case e r s n G

theorem eqv_cfg_cfg {β n G n' G'}
  : @cfg φ (cfg β n G) n' G' ≈ cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G'))
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.cfg_cfg β n G n' G'

-- theorem eqv_cfg_fuse {β n G k} (ρ : Fin k → Fin n) (hρ : Function.Surjective ρ)
--   : @cfg φ (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G)
--     ≈ cfg β k (G ∘ ρ)
--   := EqvGen.rel _ _ $ Cong.rel $ Rewrite.cfg_fuse β n G k ρ hρ

theorem eqv_let1_eta {e} {r : Region φ}
  : @let1 φ e (let1 (Term.var 0) r.vwk1) ≈ let1 e r
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.let1_eta e r

theorem eqv_let2_eta {e} {r : Region φ}
  : @let2 φ e (let1 ((Term.var 1).pair (Term.var 0)) r.vwk1.vwk1)
    ≈ let1 e r
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.let2_eta e r

theorem eqv_case_eta {e r}
  : @case φ e (let1 (Term.var 0).inl r.vwk1) (let1 (Term.var 0).inr r.vwk1)
    ≈ let1 e r
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.case_eta e r

theorem eqv_vwk {r r' : Region φ} (ρ : ℕ → ℕ) (p : r ≈ r') : r.vwk ρ ≈ r'.vwk ρ
  := Cong.eqv_vwk (λρ _ _ p => p.vwk ρ) ρ p
