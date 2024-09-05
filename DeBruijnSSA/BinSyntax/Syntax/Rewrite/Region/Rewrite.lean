import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.CategoryTheory.PathCategory
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Discretion.Correspondence.Definitions

import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Effect.Subst
import DeBruijnSSA.BinSyntax.Syntax.Fv
namespace BinSyntax

variable {φ : Type u} {ε : Type v} [Φ: EffectSet φ ε] [SemilatticeSup ε] [OrderBot ε]

-- -- TODO: define as Subst.cons or smt...
-- def Term.subst₂ (a b: Term φ) : Subst φ
--   | 0 => a
--   | 1 => b
--   | n + 2 => Term.var n

namespace Region

open Term

inductive RewriteD : Region φ → Region φ → Type _
  | let1_op (f a r) :
    RewriteD (let1 (op f a) r) (let1 a $ let1 (op f (var 0)) $ r.vwk1)
  | let1_let1 (a b r) :
    RewriteD (let1 (Term.let1 a b) r) (let1 a $ let1 b $ r.vwk1)
  | let1_pair (a b r) :
    RewriteD (let1 (pair a b) r)
    (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) $ r.vwk1.vwk1)
  | let1_let2 (a b r) :
    RewriteD (let1 (Term.let2 a b) r) (let2 a $ let1 b $ r.vwk1.vwk1)
  | let1_inl (e r) :
    RewriteD (let1 (inl e) r) (let1 e $ let1 (inl (var 0)) $ r.vwk1)
  | let1_inr (e r) :
    RewriteD (let1 (inr e) r) (let1 e $ let1 (inr (var 0)) $ r.vwk1)
  | let1_case (a l r s) :
    RewriteD (let1 (Term.case a l r) s) (case a (let1 l $ s.vwk1) (let1 r $ s.vwk1))
  | let1_abort (e r) :
    RewriteD (let1 (abort e) r) (let1 e $ let1 (abort (var 0)) $ r.vwk1)
  | let2_bind (e r) :
    RewriteD (let2 e r) (let1 e $ (let2 (Term.var 0) r.vwk2))
  | let2_pair (a b r) :
    RewriteD (let2 (pair a b) r) (let1 a $ let1 b.wk0 $ r)
  | case_bind (e r s) :
    RewriteD (case e r s) (let1 e $ case (Term.var 0) (r.vwk1) (s.vwk1))
  | cfg_br_lt (ℓ e n G) (h : ℓ < n) :
    RewriteD (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).let1 e) n G)
  | cfg_let1 (a β n G) :
    RewriteD (cfg (let1 a β) n G) (let1 a $ cfg β n (vwk1 ∘ G))
  | cfg_let2 (a β n G) :
    RewriteD (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk1 ∘ vwk1 ∘ G))
  | cfg_case (e r s n G) :
    RewriteD (cfg (case e r s) n G)
      (case e (cfg r n (vwk1 ∘ G)) (cfg s n (vwk1 ∘ G)))
  | cfg_cfg (β n G n' G') :
    RewriteD (cfg (cfg β n G) n' G') (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
  | cfg_zero (β G) : RewriteD (cfg β 0 G) β
  -- | cfg_fuse (β n G k) (ρ : Fin k → Fin n) (hρ : Function.Surjective ρ) :
  --   RewriteD
  --     (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
  --     (cfg β k (G ∘ ρ))
  | let1_eta (e) (r : Region φ) :
    RewriteD (let1 e (let1 (Term.var 0) r.vwk1)) (let1 e r)
  | let2_eta (e) (r : Region φ) :
    RewriteD (let2 e (let1 ((Term.var 1).pair (Term.var 0)) r.vwk1.vwk1))
      (let1 e r)
  | case_eta (e r) :
    RewriteD (case e (let1 (Term.var 0).inl r.vwk1) (let1 (Term.var 0).inr r.vwk1))
      (let1 e r)
  | let1_let1_case (a b r s) :
    RewriteD
      (let1 a $ let1 b $ case (var 1) r s)
      (let1 a $ case (var 0) (let1 b.wk0 r.vswap01) (let1 b.wk0 s.vswap01))
  | let1_let2_case (a b r s) :
    RewriteD
      (let1 a $ let2 b $ case (var 2) r s)
      (let1 a $ case (var 0) (let2 b.wk0 r.vswap02) (let2 b.wk0 s.vswap02))
  | let1_case_case (a d ll lr rl rr) :
    RewriteD
      (let1 a $ case d (case (var 1) ll lr) (case (var 1) rl rr))
      (let1 a $ case (var 0)
        (case d.wk0 ll.vswap01 rl.vswap01)
        (case d.wk0 lr.vswap01 rr.vswap01))

def RewriteD.cast_src {r₀ r₀' r₁ : Region φ} (h : r₀ = r₀') (p : RewriteD r₀ r₁)
  : RewriteD r₀' r₁ := h ▸ p

def RewriteD.cast_trg {r₀ r₁ r₁' : Region φ} (p : RewriteD r₀ r₁) (h : r₁ = r₁')
  : RewriteD r₀ r₁' := h ▸ p

def RewriteD.cast {r₀ r₀' r₁ r₁' : Region φ} (h₀ : r₀ = r₀') (h₁ : r₁ = r₁')
  (p : RewriteD r₀ r₁) : RewriteD r₀' r₁' := h₁ ▸ h₀ ▸ p

-- theorem RewriteD.effect {Γ : ℕ → ε} {r r' : Region φ} (p : RewriteD r r')
--  : r.effect Γ = r'.effect Γ
--   := by cases p with
--   | let1_let1 | let1_op =>
--     simp only [Region.effect, Term.effect, Nat.liftBot_zero, ge_iff_le, bot_le, sup_of_le_left]
--     rw [<-sup_assoc]
--     apply congr
--     rw [sup_comm]
--     rw [vwk1, effect_vwk, Nat.liftBot_comp_liftWk]
--     rfl
--   | let1_let2 =>
--     simp only [Region.effect, Term.effect, Nat.liftBot_zero, ge_iff_le, bot_le, sup_of_le_left]
--     rw [<-sup_assoc]
--     apply congrArg
--     simp only [vwk1, effect_vwk, Nat.liftnBot_two, Nat.liftBot_comp_liftWk]
--     rfl
--   | let1_case => sorry
--   | let2_bind => sorry
--   | let2_pair => sorry
--   | case_bind => sorry
--   -- | let1_case a b r s =>
--   --   simp only [Region.effect, Term.effect, Term.effect_liftBot_wk_succ]
--   --   have h : ∀x y z w : ε, x ⊔ (y ⊔ z) ⊔ (y ⊔ w) = y ⊔ (x ⊔ z ⊔ w) := by
--   --     intro x y z w
--   --     rw [
--   --       sup_assoc, sup_assoc, sup_assoc, sup_comm, sup_comm z, <-sup_assoc, <-sup_assoc, sup_idem,
--   --       sup_assoc y, sup_assoc y]
--   --     apply congrArg
--   --     simp only [sup_assoc, sup_comm]
--   --   have h' : Nat.liftBot (Nat.liftBot Γ) ∘ Nat.swap0 1 = Nat.liftBot (Nat.liftBot Γ) := by
--   --     funext i
--   --     cases i with
--   --     | zero => rfl
--   --     | succ i => cases i <;> rfl
--   --   simp only [h, h', Region.effect_vwk]
--   -- | let2_case =>
--   --   simp only [Region.effect, Term.effect, Term.effect_liftBot_wk_succ, Term.effect_liftnBot_wk_add]
--   --   have h : ∀x y z w : ε, x ⊔ (y ⊔ z) ⊔ (y ⊔ w) = y ⊔ (x ⊔ z ⊔ w) := by
--   --     intro x y z w
--   --     rw [
--   --       sup_assoc, sup_assoc, sup_assoc, sup_comm, sup_comm z, <-sup_assoc, <-sup_assoc, sup_idem,
--   --       sup_assoc y, sup_assoc y]
--   --     apply congrArg
--   --     simp only [sup_assoc, sup_comm]
--   --   rw [h]
--   --   have h' : Nat.liftBot (Nat.liftBot (Nat.liftBot Γ)) ∘ Nat.swap0 2
--   --     = Nat.liftBot (Nat.liftBot (Nat.liftBot Γ)) := by
--   --     funext i
--   --     cases i with
--   --     | zero => rfl
--   --     | succ i => cases i with
--   --       | zero => rfl
--   --       | succ i => cases i <;> rfl
--   --   simp [Nat.liftnBot_two, Region.effect_vwk, h']
--   | cfg_br_lt ℓ e n G h =>
--     simp only [Region.effect, Term.effect, Term.effect_liftBot_wk_succ, Term.effect_liftnBot_wk_add]
--     rw [sup_assoc]
--     apply congrArg
--     rw [sup_of_le_right]
--     exact Fin.elem_le_sup (λi => (G i).effect (Nat.liftBot Γ)) ⟨ℓ, h⟩
--   | cfg_let2 =>
--     simp only [Region.effect, Term.effect, Term.effect_liftBot_wk_succ, Term.effect_liftnBot_wk_add]
--     rw [sup_assoc]
--     apply congrArg
--     apply congrArg
--     apply congrArg
--     funext i
--     simp [Nat.liftnBot_two]
--   | cfg_case => simp [sup_assoc]
--   | cfg_cfg =>
--     simp only [effect_cfg, sup_assoc]
--     apply congrArg
--     rw [Fin.comp_addCases, Fin.sup_addCases]
--     apply congrArg
--     apply congrArg
--     funext i
--     simp [Region.effect_lwk]
--   -- | cfg_fuse β n G k ρ hρ =>
--   --   simp only [effect_cfg, effect_lwk, <-Function.comp.assoc, effect_comp_lwk]
--   --   apply congrArg
--   --   rw [Fin.sup_comp_surj _ hρ]
--   | let1_eta => sorry
--   | let2_eta =>
--     simp only [Region.effect, Term.effect, Nat.liftnBot, Nat.lt_succ_self, ↓reduceIte,
--       Nat.zero_lt_succ, ge_iff_le, le_refl, sup_of_le_left, vwk1, effect_vwk, bot_le,
--       sup_of_le_right]
--     congr
--     funext k
--     cases k <;> rfl
--   | case_eta => sorry
--   | let1_let1_case => sorry
--   | let1_let2_case => sorry
--   | let1_case_case => sorry
--   | _ => simp [Nat.liftBot, sup_assoc]

inductive Rewrite : Region φ → Region φ → Prop
  | let1_op (f a r) :
    Rewrite (let1 (op f a) r) (let1 a $ let1 (op f (var 0)) $ r.vwk1)
  | let1_let1 (a b r) :
    Rewrite (let1 (Term.let1 a b) r) (let1 a $ let1 b $ r.vwk1)
  | let1_pair (a b r) :
    Rewrite (let1 (pair a b) r)
    (let1 a $ let1 (b.wk Nat.succ) $ let1 (pair (var 1) (var 0)) $ r.vwk1.vwk1)
  | let1_let2 (a b r) :
    Rewrite (let1 (Term.let2 a b) r) (let2 a $ let1 b $ r.vwk1.vwk1)
  | let1_inl (e r) :
    Rewrite (let1 (inl e) r) (let1 e $ let1 (inl (var 0)) $ r.vwk1)
  | let1_inr (e r) :
    Rewrite (let1 (inr e) r) (let1 e $ let1 (inr (var 0)) $ r.vwk1)
  | let1_case (a l r s) :
    Rewrite (let1 (Term.case a l r) s) (case a (let1 l $ s.vwk1) (let1 r $ s.vwk1))
  | let1_abort (e r) :
    Rewrite (let1 (abort e) r) (let1 e $ let1 (abort (var 0)) $ r.vwk1)
  | let2_bind (e r) :
    Rewrite (let2 e r) (let1 e $ (let2 (Term.var 0) r.vwk2))
  | let2_pair (a b r) :
    Rewrite (let2 (pair a b) r) (let1 a $ let1 b.wk0 $ r)
  | case_bind (e r s) :
    Rewrite (case e r s) (let1 e $ case (Term.var 0) (r.vwk1) (s.vwk1))
  -- | let1_case (a b r s) :
  --   Rewrite (let1 a $ case (b.wk Nat.succ) r s)
  --   (case b
  --     (let1 (a.wk Nat.succ) (r.vwk (Nat.swap0 1)))
  --     (let1 (a.wk Nat.succ) (s.vwk (Nat.swap0 1))))
  -- | let2_case (a b r s) :
  --   Rewrite (let2 a $ case (b.wk (· + 2)) r s)
  --   (case b
  --     (let2 (a.wk Nat.succ) (r.vwk (Nat.swap0 2)))
  --     (let2 (a.wk Nat.succ) (s.vwk (Nat.swap0 2))))
  | cfg_br_lt (ℓ e n G) (h : ℓ < n) :
    Rewrite (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).let1 e) n G)
  | cfg_let1 (a β n G) :
    Rewrite (cfg (let1 a β) n G) (let1 a $ cfg β n (vwk1 ∘ G))
  | cfg_let2 (a β n G) :
    Rewrite (cfg (let2 a β) n G) (let2 a $ cfg β n (vwk1 ∘ vwk1 ∘ G))
  | cfg_case (e r s n G) :
    Rewrite (cfg (case e r s) n G)
      (case e (cfg r n (vwk1 ∘ G)) (cfg s n (vwk1 ∘ G)))
  | cfg_cfg (β n G n' G') :
    Rewrite (cfg (cfg β n G) n' G') (cfg β (n + n') (Fin.addCases G (lwk (· + n) ∘ G')))
  | cfg_zero (β G) : Rewrite (cfg β 0 G) β
  -- | cfg_fuse (β n G k) (ρ : Fin k → Fin n) (hρ : Function.Surjective ρ) :
  --   Rewrite
  --     (cfg (lwk (Fin.toNatWk ρ) β) n (lwk (Fin.toNatWk ρ) ∘ G))
  --     (cfg β k (G ∘ ρ))
  | let1_eta (e) (r : Region φ) :
    Rewrite (let1 e (let1 (Term.var 0) r.vwk1)) (let1 e r)
  | let2_eta (e) (r : Region φ) :
    Rewrite (let2 e (let1 ((Term.var 1).pair (Term.var 0)) r.vwk1.vwk1))
      (let1 e r)
  | case_eta (e r) :
    Rewrite (case e (let1 (Term.var 0).inl r.vwk1) (let1 (Term.var 0).inr r.vwk1))
      (let1 e r)
  | let1_let1_case (a b r s) :
    Rewrite
      (let1 a $ let1 b $ case (var 1) r s)
      (let1 a $ case (var 0) (let1 b.wk0 r.vswap01) (let1 b.wk0 s.vswap01))
  | let1_let2_case (a b r s) :
    Rewrite
      (let1 a $ let2 b $ case (var 2) r s)
      (let1 a $ case (var 0) (let2 b.wk0 r.vswap02) (let2 b.wk0 s.vswap02))
  | let1_case_case (a d ll lr rl rr) :
    Rewrite
      (let1 a $ case d (case (var 1) ll lr) (case (var 1) rl rr))
      (let1 a $ case (var 0)
        (case d.wk0 ll.vswap01 rl.vswap01)
        (case d.wk0 lr.vswap01 rr.vswap01))

theorem RewriteD.rewrite {r r' : Region φ} (p : RewriteD r r') : Rewrite r r'
  := by cases p <;> constructor--; assumption

-- TODO: make a def...
theorem Rewrite.nonempty {r r' : Region φ} (p : Rewrite r r') : Nonempty (RewriteD r r')
  := by cases p <;> constructor <;> constructor--; assumption

theorem Rewrite.of_nonempty {r r' : Region φ} (p : Nonempty (RewriteD r r')) : Rewrite r r'
  := let ⟨p⟩ := p; p.rewrite

theorem Rewrite.nonempty_iff {r r' : Region φ} : Rewrite r r' ↔ Nonempty (RewriteD r r')
  := ⟨nonempty, of_nonempty⟩

theorem Rewrite.cast_src {r₀ r₀' r₁ : Region φ} (h : r₀ = r₀') (p : Rewrite r₀ r₁)
  : Rewrite r₀' r₁ := h ▸ p

theorem Rewrite.cast_trg {r₀ r₁ r₁' : Region φ} (p : Rewrite r₀ r₁) (h : r₁ = r₁')
  : Rewrite r₀ r₁' := h ▸ p

-- theorem Rewrite.fvs_eq {r r' : Region φ} (p : Rewrite r r') : r.fvs = r'.fvs := by cases p with
--   | let1_case => sorry
--   | let2_pair => sorry
--   -- | let1_case a b r s =>
--   --   simp only [fvs, fvs_wk, Nat.succ_eq_add_one, Set.liftnFv_of_union, Set.liftnFv_map_add,
--   --     <-Set.union_assoc]
--   --   rw [Set.union_comm a.fvs]
--   --   simp only [Set.union_assoc (b.fvs ∪ a.fvs)]
--   --   rw [Set.union_comm (Set.liftnFv 1 _) a.fvs]
--   --   simp only [<-Set.union_assoc (b.fvs ∪ a.fvs)]
--   --   rw [Set.union_assoc b.fvs a.fvs a.fvs, Set.union_self]
--   --   simp only [Set.union_assoc]
--   --   apply congrArg
--   --   apply congrArg
--   --   congr 1
--   --   sorry
--   --   sorry
--   -- | let2_case a b r s =>
--   --   stop
--   --   simp only [fvs, fvs_wk, Set.liftnFv_of_union, Set.liftnFv_map_add, Nat.succ_eq_add_one,
--   --     <-Set.union_assoc]
--   --   rw [Set.union_comm a.fvs]
--   --   simp only [Set.union_assoc (b.fvs ∪ a.fvs)]
--   --   rw [Set.union_comm (Set.liftnFv 1 _) a.fvs]
--   --   simp only [<-Set.union_assoc (b.fvs ∪ a.fvs)]
--   --   rw [Set.union_assoc b.fvs a.fvs a.fvs, Set.union_self]
--   --   congr
--   --   rw [Set.liftnFv_succ, Set.liftnFv_one, Set.liftnFv_succ']
--   --   rw [Set.liftnFv_succ, Set.liftnFv_one, Set.liftnFv_succ']
--   | cfg_br_lt ℓ e n G h =>
--     simp only [fvs]
--     rw [Set.union_assoc]
--     congr
--     apply Eq.symm
--     apply Set.union_eq_self_of_subset_left
--     apply Set.subset_iUnion_of_subset ⟨ℓ, h⟩
--     rfl
--   | cfg_case e r s G =>
--     simp only [fvs, Set.union_assoc, Function.comp_apply, fvs_vwk1, Set.liftFv_map_liftWk,
--       Nat.succ_eq_add_one, Set.map_add_liftnFv, Set.liftnFv_of_union, Set.liftnFv_iUnion,
--       Set.liftnFv_of_inter, le_refl, Set.liftnFv_Ici, Set.inter_univ]
--     apply congrArg
--     apply congrArg
--     rw [Set.union_comm (s.fvs.liftnFv 1), <-Set.union_assoc, Set.union_self]
--   | cfg_cfg => simp [fvs, Set.union_assoc, Fin.comp_addCases_apply, Set.iUnion_addCases]
--   -- | cfg_fuse β n G k ρ hρ =>
--   --   simp only [fvs, fvs_lwk]
--   --   rw [Set.iUnion_congr_of_surjective _ hρ]
--   --   intro i
--   --   simp
--   | let2_eta =>
--     simp only [fvs, Term.fvs, Set.union_singleton, fvs_vwk1, Set.liftFv_map_liftWk,
--       Nat.succ_eq_add_one, Set.map_add_liftnFv, Set.liftnFv_of_union, Nat.ofNat_pos,
--       Set.liftnFv_insert_lt, Nat.one_lt_ofNat, Set.liftnFv_singleton_lt, Set.empty_union]
--     congr
--     ext k
--     rw [Set.mem_liftnFv, Set.mem_liftFv]
--     simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_Ici, le_add_iff_nonneg_left, zero_le,
--       and_true]
--     constructor
--     intro ⟨x, hx, hx'⟩
--     cases x with
--     | zero => cases hx'
--     | succ x =>
--       cases hx'
--       exact hx
--     intro hk
--     exact ⟨k + 1, hk, rfl⟩
--   | case_eta => sorry
--   | let1_let1_case => sorry
--   | let1_let2_case => sorry
--   | let1_case_case => sorry
--   | _ => simp [vwk2, fvs_vwk, fvs_vwk1, Term.fvs_wk, Set.liftnFv_iUnion, Set.union_assoc]

def RewriteD.vwk {r r' : Region φ} (ρ : ℕ → ℕ) (d : RewriteD r r') : RewriteD (r.vwk ρ) (r'.vwk ρ)
  := by cases d with
  | let2_pair a b r =>
    convert (let2_pair (a.wk ρ) (b.wk ρ) (r.vwk (Nat.liftnWk 2 ρ))) using 1
    simp [Term.wk0, Term.wk_wk, Nat.liftWk_comp_succ, Nat.liftnWk_two]
  | cfg_cfg β n G n' G' =>
    simp only [Region.vwk, wk, Fin.comp_addCases_apply]
    rw [<-Function.comp.assoc, Region.vwk_comp_lwk, Function.comp.assoc]
    constructor
  | let2_eta e r =>
    simp only [Region.vwk, wk, Nat.liftnWk, Nat.lt_succ_self, ↓reduceIte, Nat.zero_lt_succ,
      Nat.liftWk_comm_liftnWk_apply, vwk_liftnWk₂_vwk1, vwk_liftWk₂_vwk1]
    constructor
  | let1_let1_case a b r s =>
    convert (let1_let1_case
      (a.wk ρ) (b.wk (Nat.liftWk ρ)) (r.vwk (Nat.liftnWk 3 ρ)) (s.vwk (Nat.liftnWk 3 ρ)))
      using 1
    simp [Nat.liftnWk_succ, Nat.liftnWk_zero]
    simp only [BinSyntax.Region.vwk, wk, Nat.liftWk_zero, wk0, wk_wk, Nat.liftWk_comp_succ, vswap01,
      vwk_vwk, let1.injEq, true_and]
    congr <;> funext k <;> cases k using Nat.cases3 <;> rfl
  | let1_let2_case a b r s =>
    convert (let1_let2_case
      (a.wk ρ) (b.wk (Nat.liftWk ρ)) (r.vwk (Nat.liftnWk 4 ρ)) (s.vwk (Nat.liftnWk 4 ρ)))
      using 1
    simp [Nat.liftnWk_succ, Nat.liftnWk_zero]
    simp only [BinSyntax.Region.vwk, wk, Nat.liftWk_zero, wk0, wk_wk, Nat.liftWk_comp_succ, vswap02,
      vwk_vwk, let1.injEq, true_and]
    congr <;> funext k <;> cases k using Nat.cases4 <;> rfl
  | let1_case_case a d ll lr rl rr =>
    convert (let1_case_case
      (a.wk ρ) (d.wk (Nat.liftWk ρ)) (ll.vwk (Nat.liftnWk 3 ρ)) (lr.vwk (Nat.liftnWk 3 ρ))
      (rl.vwk (Nat.liftnWk 3 ρ)) (rr.vwk (Nat.liftnWk 3 ρ)))
      using 1
    simp [Nat.liftnWk_succ, Nat.liftnWk_zero]
    simp only [BinSyntax.Region.vwk, wk, Nat.liftWk_zero, wk0, wk_wk, Nat.liftWk_comp_succ, vswap01,
      vwk_vwk, let1.injEq, true_and]
    congr <;> funext k <;> cases k using Nat.cases3 <;> rfl
  | _ =>
    simp only [
      Region.vwk2, Region.vwk, wk, Nat.liftWk,
      vwk_liftWk₂_vwk1, wk_liftWk_wk_succ, vwk_liftnWk₂_liftWk_vwk2, vwk_liftnWk₂_vwk1,
      wk_liftnWk_wk_add, Nat.liftWk_comm_liftnWk_apply, Function.comp_apply]
    constructor

theorem Rewrite.vwk {r r' : Region φ} (ρ : ℕ → ℕ) (p : Rewrite r r') : Rewrite (r.vwk ρ) (r'.vwk ρ)
  := let ⟨d⟩ := p.nonempty; (d.vwk ρ).rewrite

def RewriteD.lwk {r r' : Region φ} (ρ : ℕ → ℕ) (d : RewriteD r r') : RewriteD (r.lwk ρ) (r'.lwk ρ)
  := by cases d with
  | cfg_br_lt ℓ e n G hℓ =>
    simp only [Region.lwk, Nat.liftnWk, hℓ, ↓reduceIte]
    apply cfg_br_lt
  | cfg_cfg β n G n' G' =>
    simp only [Region.lwk]
    apply cast_trg
    apply cfg_cfg
    congr
    · rw [Nat.liftnWk_add]; rfl
    · funext i
      simp only [Fin.comp_addCases_apply]
      simp only [Fin.addCases]
      split
      · simp [Nat.liftnWk_add, *]
      · simp only [Function.comp_apply, eq_rec_constant, Region.lwk_lwk]
        congr
        funext k
        simp only [Function.comp_apply, Nat.liftnWk]
        split
        case isTrue h =>
          rw [ite_cond_eq_true]
          simp_arith [Nat.succ_le_of_lt h]
        case isFalse h =>
          rw [ite_cond_eq_false]
          rw [Nat.sub_add_eq]
          simp only [add_tsub_cancel_right]
          rw [Nat.add_comm n n', <-Nat.add_assoc]
          rw [Nat.add_comm]
          simp [Nat.le_of_not_lt h]
  | let1_let1_case a b r s =>
    convert (let1_let1_case a b (r.lwk ρ) (s.lwk ρ)) using 1
    simp [vswap01, vwk_lwk]
  | let1_let2_case a b r s =>
    convert (let1_let2_case a b (r.lwk ρ) (s.lwk ρ)) using 1
    simp [vswap02, vwk_lwk]
  | let1_case_case a d ll lr rl rr =>
    convert (let1_case_case a d (ll.lwk ρ) (lr.lwk ρ) (rl.lwk ρ) (rr.lwk ρ)) using 1
    simp [vswap01, vwk_lwk]
  | _ =>
    simp only [
      Region.vwk2, Region.lwk, wk, Function.comp_apply, lwk_vwk, lwk_vwk1, Function.comp_apply]
    constructor

theorem Rewrite.lwk {r r' : Region φ} (ρ : ℕ → ℕ) (p : Rewrite r r') : Rewrite (r.lwk ρ) (r'.lwk ρ)
  := let ⟨d⟩ := p.nonempty; (d.lwk ρ).rewrite

-- TODO: vsubst, lsubst
