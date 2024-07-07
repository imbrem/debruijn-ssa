import DeBruijnSSA.BinSyntax.Rewrite.Term.Uniform
import DeBruijnSSA.BinSyntax.Rewrite.Term.Step

import Discretion.Utils.Quotient

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

instance InS.instSetoid {Γ : Ctx α ε} {V : Ty α × ε} : Setoid (InS φ Γ V)
  := Uniform.Setoid TStep Γ V

theorem InS.eqv_def {Γ : Ctx α ε} {V : Ty α × ε} {r r' : InS φ Γ V}
  : r ≈ r' ↔ Uniform (φ := φ) TStep Γ V r r'
  := by rfl

theorem InS.congr_eq {Γ : Ctx α ε} {V : Ty α × ε} {r r' : InS φ Γ V}
  (h : r = r') : r ≈ r'
  := h ▸ Setoid.refl r

theorem InS.op_congr {Γ : Ctx α ε} {a a' : InS φ Γ ⟨A, e⟩}
  (hf : Φ.EFn f A B e) (ha : a ≈ a') : op f hf a ≈ op f hf a'
  := Uniform.op hf ha

theorem InS.let1_bound_congr {Γ : Ctx α ε} {a a' : InS φ Γ ⟨A, e⟩}
  (ha : a ≈ a') (b : InS φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩) : let1 a b ≈ let1 a' b
  := Uniform.let1_bound ha b.prop

theorem InS.let1_body_congr {Γ : Ctx α ε} (a : InS φ Γ ⟨A, e⟩) {b b' : InS φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  (hb : b ≈ b') : let1 a b ≈ let1 a b'
  := Uniform.let1_body a.prop hb

theorem InS.let1_congr {Γ : Ctx α ε} {a a' : InS φ Γ ⟨A, e⟩} {b b' : InS φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  (ha : a ≈ a') (hb : b ≈ b') : let1 a b ≈ let1 a' b'
  := Setoid.trans (let1_bound_congr ha b) (let1_body_congr a' hb)

theorem InS.pair_left_congr {Γ : Ctx α ε} {a a' : InS φ Γ ⟨A, e⟩}
  (ha : a ≈ a') (b : InS φ Γ ⟨B, e⟩) : pair a b ≈ pair a' b
  := Uniform.pair_left ha b.prop

theorem InS.pair_right_congr {Γ : Ctx α ε} (a : InS φ Γ ⟨A, e⟩) {b b' : InS φ Γ ⟨B, e⟩}
  (hb : b ≈ b') : pair a b ≈ pair a b'
  := Uniform.pair_right a.prop hb

theorem InS.pair_congr {Γ : Ctx α ε} {a a' : InS φ Γ ⟨A, e⟩} {b b' : InS φ Γ ⟨B, e⟩}
  (ha : a ≈ a') (hb : b ≈ b') : pair a b ≈ pair a' b'
  := Setoid.trans (pair_left_congr ha b) (pair_right_congr a' hb)

theorem InS.let2_bound_congr {Γ : Ctx α ε} {a a' : InS φ Γ ⟨Ty.prod A B, e⟩}
  (ha : a ≈ a') (b : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩) : let2 a b ≈ let2 a' b
  := Uniform.let2_bound ha b.prop

theorem InS.let2_body_congr {Γ : Ctx α ε} (a : InS φ Γ ⟨Ty.prod A B, e⟩)
  {b b' : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩} (hb : b ≈ b') : let2 a b ≈ let2 a b'
  := Uniform.let2_body a.prop hb

theorem InS.let2_congr {Γ : Ctx α ε} {a a' : InS φ Γ ⟨Ty.prod A B, e⟩}
  {b b' : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  (ha : a ≈ a') (hb : b ≈ b') : let2 a b ≈ let2 a' b'
  := Setoid.trans (let2_bound_congr ha b) (let2_body_congr a' hb)

theorem InS.inl_congr {Γ : Ctx α ε} {a a' : InS φ Γ ⟨A, e⟩}
  (ha : a ≈ a') : inl (right := B) a ≈ inl a'
  := Uniform.inl ha

theorem InS.inr_congr {Γ : Ctx α ε} {a a' : InS φ Γ ⟨B, e⟩}
  (ha : a ≈ a') : inr (left := A) a ≈ inr a'
  := Uniform.inr ha

theorem InS.case_disc_congr {Γ : Ctx α ε} {a a' : InS φ Γ ⟨Ty.coprod A B, e⟩}
  (ha : a ≈ a') (l : InS φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩) (r : InS φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩)
  : case a l r ≈ case a' l r
  := Uniform.case_disc ha l.prop r.prop

theorem InS.case_left_congr {Γ : Ctx α ε} (a : InS φ Γ ⟨Ty.coprod A B, e⟩)
  {l l' : InS φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} (hl : l ≈ l') (r : InS φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩)
  : case a l r ≈ case a l' r
  := Uniform.case_left a.prop hl r.prop

theorem InS.case_right_congr {Γ : Ctx α ε} (a : InS φ Γ ⟨Ty.coprod A B, e⟩)
  (l : InS φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩) {r r' : InS φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩} (hr : r ≈ r')
  : case a l r ≈ case a l r'
  := Uniform.case_right a.prop l.prop hr

theorem InS.case_congr {Γ : Ctx α ε} {a a' : InS φ Γ ⟨Ty.coprod A B, e⟩}
  (ha : a ≈ a') {l l' : InS φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩} (hl : l ≈ l')
  {r r' : InS φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩} (hr : r ≈ r')
  : case a l r ≈ case a' l' r'
  := Setoid.trans (case_disc_congr ha l r)
  $ Setoid.trans (case_left_congr a' hl r) (case_right_congr a' l' hr)

theorem InS.abort_congr {Γ : Ctx α ε} {A : Ty α} {a a' : InS φ Γ ⟨Ty.empty, e⟩}
  (ha : a ≈ a') : abort a A ≈ abort a' A
  := Uniform.abort ha

theorem InS.wk_congr_right {Γ Δ : Ctx α ε}
  (ρ : Ctx.InS Γ Δ) {r r' : InS φ Δ V} (hr : r ≈ r') : r.wk ρ ≈ r'.wk ρ
  := Uniform.wk TStep.wk ρ.prop hr

theorem InS.wk_congr {Γ Δ : Ctx α ε} {ρ ρ' : Ctx.InS Γ Δ}
  {r r' : InS φ Δ V} (hρ : ρ ≈ ρ') (hr : r ≈ r') : r.wk ρ ≈ r'.wk ρ'
  := r.wk_equiv hρ ▸ wk_congr_right ρ' hr

theorem InS.wk_res_congr {Γ : Ctx α ε} {V V'} (h : V ≤ V') {r r' : InS φ Γ V} (hr : r ≈ r')
  : r.wk_res h ≈ r'.wk_res h
  := Uniform.wk_res (λh p => p.wk_res h) h hr

theorem InS.let1_beta {Γ : Ctx α ε} {a : InS φ Γ ⟨A, ⊥⟩} {b : InS φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  : let1 (a.wk_eff (by simp)) b ≈ b.subst a.subst0
  := Uniform.rel $ TStep.let1_beta a.prop b.prop

theorem InS.let1_beta_drop {Γ : Ctx α ε} (a : InS φ Γ ⟨A, ⊥⟩) (b : InS φ Γ ⟨B, e⟩)
  : let1 (a.wk_eff (by simp)) b.wk0 ≈ b
  := Uniform.rel $ TStep.let1_beta_drop a.prop b.prop

theorem TStep.subst {Γ Δ : Ctx α ε} {L r r'} {σ} (hσ : σ.Wf Γ Δ)
  : TStep (φ := φ) Δ L r r' → Uniform TStep Γ L (r.subst σ) (r'.subst σ)
  | let1_beta de dr => Uniform.rel $ (let1_beta (de.subst hσ) (dr.subst hσ.slift)).cast_trg sorry
  | rewrite d d' p => Uniform.rel $ rewrite (d.subst hσ) (d'.subst hσ) sorry
  | reduce d d' p => Uniform.rel $ reduce (d.subst hσ) (d'.subst hσ) sorry
  | initial di d d' => sorry -- TODO: initiality lifting lore, follows by let1_beta drop initial
  | terminal de de' => Uniform.rel $ terminal (de.subst hσ) (de'.subst hσ)

theorem InS.subst_congr_right {Γ Δ : Ctx α ε} {V} {r r' : InS φ Δ V}
  (σ : Subst.InS φ Γ Δ) (hr : r ≈ r') : r.subst σ ≈ r'.subst σ
  := Uniform.subst_flatten TStep.subst σ.prop hr

instance Subst.InS.instSetoid {Γ Δ : Ctx α ε} : Setoid (Subst.InS φ Γ Δ) where
  r σ τ := ∀i : Fin Δ.length, σ.get i ≈ τ.get i
  iseqv := {
    refl := (λ_ _ => Setoid.refl _)
    symm := (λh i => (h i).symm)
    trans := (λhl hr i => Setoid.trans (hl i) (hr i))
  }

theorem Subst.InS.var_congr {Γ Δ : Ctx α ε} {σ τ : Subst.InS φ Γ Δ} (hσ : σ ≈ τ)
  {V} (n) (h : Δ.Var n V) : σ.var n h ≈ τ.var n h
  := by
  -- TODO: cleanup...
  have hσ := hσ ⟨n, h.length⟩
  apply Uniform.wk_res
  intro Γ V V' r r' hV p
  exact TStep.wk_res hV p
  exact h.get
  exact hσ

theorem Subst.InS.lift_congr {Γ Δ : Ctx α ε} (hv : V ≤ V') {σ τ : Subst.InS φ Γ Δ}
  (h : σ ≈ τ) : σ.lift hv ≈ τ.lift hv := by intro i; cases i using Fin.cases with
  | zero => exact Setoid.refl _
  | succ i => exact InS.wk_congr_right Ctx.InS.wk0 (h i)

theorem Subst.InS.slift_congr {Γ Δ : Ctx α ε} {head} {σ τ : Subst.InS φ Γ Δ}
  (h : σ ≈ τ) : σ.lift (le_refl head) ≈ τ.lift (le_refl head)
  := lift_congr (le_refl _) h

theorem Subst.InS.sliftn₂_congr {Γ Δ : Ctx α ε} {left right} {σ τ : Subst.InS φ Γ Δ}
  (h : σ ≈ τ) : σ.liftn₂ (le_refl left) (le_refl right) ≈ τ.liftn₂ (le_refl left) (le_refl right)
  := sorry

theorem InS.subst_equiv_congr {Γ Δ : Ctx α ε} {V}
  {σ τ : Subst.InS φ Γ Δ} (hσ : σ ≈ τ) : (r : InS φ Δ V) → r.subst σ ≈ r.subst τ
  | ⟨r, hr⟩ => by induction hr generalizing Γ with
  | var dv => exact Subst.InS.var_congr hσ _ dv
  | op df de Ie => exact op_congr df (Ie hσ)
  | let1 da db Ia Ib => exact let1_congr (Ia hσ) (Ib (Subst.InS.slift_congr hσ))
  | let2 da db Ia Ib => exact let2_congr (Ia hσ) (Ib (Subst.InS.sliftn₂_congr hσ))
  | pair dl dr Il Ir => exact pair_congr (Il hσ) (Ir hσ)
  | inl d Id => exact inl_congr (Id hσ)
  | inr d Id => exact inr_congr (Id hσ)
  | case de dl dr Ie Il Ir =>
    exact case_congr (Ie hσ)
      (Il (Subst.InS.slift_congr hσ))
      (Ir (Subst.InS.slift_congr hσ))
  | abort d Id => exact abort_congr (Id hσ)
  | unit => exact Setoid.refl _

theorem InS.subst_congr {Γ Δ : Ctx α ε} {V}
  {σ σ' : Subst.InS φ Γ Δ} (hσ : σ ≈ σ') {r r' : InS φ Δ V} (hr : r ≈ r') : r.subst σ ≈ r'.subst σ'
  := Setoid.trans (InS.subst_equiv_congr hσ r) (InS.subst_congr_right σ' hr)

-- TODO: stick rules down here...
