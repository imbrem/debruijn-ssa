import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Symmetric
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

theorem eqv_cfg_br_lt {ℓ e n G} (h : ℓ < n)
  : @cfg φ (br ℓ e) n G ≈ cfg ((G ⟨ℓ, h⟩).let1 e) n G
  := Relation.EqvGen.rel _ _ $ Cong.rel $ Rewrite.cfg_br_lt ℓ e n G h

theorem eqv_vwk {r r' : Region φ} (ρ : ℕ → ℕ) (p : r ≈ r') : r.vwk ρ ≈ r'.vwk ρ
  := Cong.eqv_vwk (λρ _ _ p => p.vwk ρ) ρ p
