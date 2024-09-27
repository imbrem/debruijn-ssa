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

namespace Region

open Term

inductive RewriteD : Region φ → Region φ → Type _
  | let1_op (f a r) :
    RewriteD (let1 (op f a) r) (let1 a $ let1 (op f (var 0)) $ r.vwk1)
  | let1_let1 (a b r) :
    RewriteD (let1 (Term.let1 a b) r) (let1 a $ let1 b $ r.vwk1)
  | let1_pair (a b r) :
    RewriteD (let1 (pair a b) r)
    (let1 a $ let1 b.wk0 $ let1 (pair (var 1) (var 0)) $ r.vwk1.vwk1)
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
--   --   simp only [effect_cfg, effect_lwk, <-Function.comp_assoc, effect_comp_lwk]
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
  | cfg_br_lt (ℓ e n G) (h : ℓ < n) :
    Rewrite (cfg (br ℓ e) n G) (cfg ((G ⟨ℓ, h⟩).let1 e) n G)

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

def RewriteD.vsubst {r r' : Region φ} (σ : Term.Subst φ) (p : RewriteD r r')
  : RewriteD (r.vsubst σ) (r'.vsubst σ) := by cases p with
  | let1_op f a r =>
    convert (let1_op f (a.subst σ) (r.vsubst σ.lift)) using 1
    simp [Term.subst, Region.vsubst_lift₂_vwk1]
  | let1_let1 a b r =>
    convert (let1_let1 (a.subst σ) (b.subst σ.lift) (r.vsubst σ.lift)) using 1
    simp [Term.subst, Region.vsubst_lift₂_vwk1]
  | let1_pair a b r =>
    convert (let1_pair (a.subst σ) (b.subst σ) (r.vsubst σ.lift)) using 1
    simp [Term.subst, Region.vsubst_lift₂_vwk1, Term.wk0_subst]
  | let1_let2 a b r =>
    convert (let1_let2 (a.subst σ) (b.subst (σ.liftn 2)) (r.vsubst σ.lift)) using 1
    simp [Term.subst, Region.vsubst_lift₂_vwk1, Term.Subst.liftn_two]
  | let1_inl e r =>
    convert (let1_inl (e.subst σ) (r.vsubst σ.lift)) using 1
    simp [Term.subst, Region.vsubst_lift₂_vwk1]
  | let1_inr e r =>
    convert (let1_inr (e.subst σ) (r.vsubst σ.lift)) using 1
    simp [Term.subst, Region.vsubst_lift₂_vwk1]
  | let1_case a l r s =>
    convert (let1_case (a.subst σ) (l.subst σ.lift) (r.subst σ.lift) (s.vsubst σ.lift)) using 1
    simp [Term.subst, Region.vsubst_lift₂_vwk1]
  | let1_abort e r =>
    convert (let1_abort (e.subst σ) (r.vsubst σ.lift)) using 1
    simp [Term.subst, Region.vsubst_lift₂_vwk1]
  | let2_bind e r =>
    convert (let2_bind (e.subst σ) (r.vsubst (σ.liftn 2))) using 1
    simp [Term.subst, Region.vsubst_lift₂_vwk1, Region.vsubst_lift₃_vwk2, Term.Subst.liftn_two]
  | let2_pair a b r =>
    convert (let2_pair (a.subst σ) (b.subst σ) (r.vsubst (σ.liftn 2))) using 1
    simp [Term.subst, Region.vsubst_lift₂_vwk1, Term.wk0_subst, Term.Subst.liftn_two]
  | case_bind e r s =>
    convert (case_bind (e.subst σ) (r.vsubst σ.lift) (s.vsubst σ.lift)) using 1
    simp [Term.subst, Region.vsubst_lift₂_vwk1]
  | cfg_br_lt ℓ e n G h => exact (cfg_br_lt ℓ (e.subst σ) n (λi => (G i).vsubst σ.lift) h)

theorem Rewrite.vsubst {r r' : Region φ} (σ : Term.Subst φ) (p : Rewrite r r')
  : Rewrite (r.vsubst σ) (r'.vsubst σ)
  := let ⟨d⟩ := p.nonempty; (d.vsubst σ).rewrite

def RewriteD.lsubst {r r' : Region φ} (σ : Subst φ) (p : RewriteD r r')
  : RewriteD (r.lsubst σ) (r'.lsubst σ) := by cases p with
  | let1_op f a r =>
    convert (let1_op f a (r.lsubst σ.vlift)) using 1
    simp [vwk1_lsubst_vlift]
  | let1_let1 a b r =>
    convert (let1_let1 a b (r.lsubst σ.vlift)) using 1
    simp [vwk1_lsubst_vlift]
  | let1_pair a b r =>
    convert (let1_pair a b (r.lsubst σ.vlift)) using 1
    simp [vwk1_lsubst_vlift]
  | let1_let2 a b r =>
    convert (let1_let2 a b (r.lsubst σ.vlift)) using 1
    simp [vwk1_lsubst_vlift, Subst.vliftn_two]
  | let1_inl e r =>
    convert (let1_inl e (r.lsubst σ.vlift)) using 1
    simp [vwk1_lsubst_vlift]
  | let1_inr e r =>
    convert (let1_inr e (r.lsubst σ.vlift)) using 1
    simp [vwk1_lsubst_vlift]
  | let1_case a l r s =>
    convert (let1_case a l r (s.lsubst σ.vlift)) using 1
    simp [vwk1_lsubst_vlift]
  | let1_abort e r =>
    convert (let1_abort e (r.lsubst σ.vlift)) using 1
    simp [vwk1_lsubst_vlift]
  | let2_bind e r =>
    convert (let2_bind e (r.lsubst (σ.vliftn 2))) using 1
    simp [vwk2_lsubst_vlift₂, Subst.vliftn_two]
  | let2_pair a b r =>
    convert (let2_pair a b (r.lsubst (σ.vliftn 2))) using 1
    simp [vwk1_lsubst_vlift, Subst.vliftn_two]
  | case_bind e r s =>
    convert (case_bind e (r.lsubst σ.vlift) (s.lsubst σ.vlift)) using 1
    simp [vwk1_lsubst_vlift]
  | cfg_br_lt ℓ e n G h =>
    convert (cfg_br_lt ℓ e n (λi => (G i).lsubst (σ.liftn n).vlift) h) using 1
    simp [Subst.liftn, h]

theorem Rewrite.lsubst {r r' : Region φ} (σ : Subst φ) (p : Rewrite r r')
  : Rewrite (r.lsubst σ) (r'.lsubst σ)
  := let ⟨d⟩ := p.nonempty; (d.lsubst σ).rewrite

def RewriteD.vwk {r r' : Region φ} (ρ : ℕ → ℕ) (d : RewriteD r r') : RewriteD (r.vwk ρ) (r'.vwk ρ)
  := by
  simp only [<-Region.vsubst_fromWk]
  exact RewriteD.vsubst _ d

theorem Rewrite.vwk {r r' : Region φ} (ρ : ℕ → ℕ) (p : Rewrite r r') : Rewrite (r.vwk ρ) (r'.vwk ρ)
  := let ⟨d⟩ := p.nonempty; (d.vwk ρ).rewrite

def RewriteD.lwk {r r' : Region φ} (ρ : ℕ → ℕ) (d : RewriteD r r') : RewriteD (r.lwk ρ) (r'.lwk ρ)
  := by
  simp only [<-Region.lsubst_fromLwk]
  exact RewriteD.lsubst _ d

theorem Rewrite.lwk {r r' : Region φ} (ρ : ℕ → ℕ) (p : Rewrite r r') : Rewrite (r.lwk ρ) (r'.lwk ρ)
  := let ⟨d⟩ := p.nonempty; (d.lwk ρ).rewrite

end Region

end BinSyntax
