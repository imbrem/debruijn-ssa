import DeBruijnSSA.BinSyntax.Rewrite.Region.Step
import DeBruijnSSA.BinSyntax.Rewrite.Region.Uniform
import DeBruijnSSA.BinSyntax.Rewrite.Term.Setoid

import Discretion.Utils.Quotient

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

instance InS.Setoid (φ) [EffInstSet φ (Ty α) ε] (Γ : Ctx α ε) (L : LCtx α) : Setoid (InS φ Γ L)
  := Uniform.Setoid TStep Γ L

theorem InS.eqv_def {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ Γ L}
  : r ≈ r' ↔ Uniform (φ := φ) TStep Γ L r r'
  := by rfl

theorem InS.let1_body_congr {Γ : Ctx α ε} {L : LCtx α}
  {r r' : InS φ _ L} (a : Term.InS φ Γ ⟨A, e⟩)
    : r ≈ r' → InS.let1 a r ≈ InS.let1 a r' := Uniform.let1 a.prop

theorem InS.let2_body_congr {Γ : Ctx α ε} {L : LCtx α}
  {r r' : InS φ _ L} (a : Term.InS φ Γ ⟨Ty.prod A B, e⟩)
    : r ≈ r' → InS.let2 a r ≈ InS.let2 a r' := Uniform.let2 a.prop

theorem InS.case_left_congr {Γ : Ctx α ε} {L : LCtx α}
  {e : Term.InS φ Γ ⟨Ty.coprod A B, e'⟩} {r r' s : InS φ _ L}
  (h : r ≈ r') : InS.case e r s ≈ InS.case e r' s := Uniform.case_left e.prop h s.prop

theorem InS.case_right_congr {Γ : Ctx α ε} {L : LCtx α}
  {e : Term.InS φ Γ ⟨Ty.coprod A B, e'⟩} {r s s' : InS φ _ L}
  (h : s ≈ s') : InS.case e r s ≈ InS.case e r s' := Uniform.case_right e.prop r.prop h

-- TODO: add congruence for terms...
theorem InS.case_branches_congr {Γ : Ctx α ε} {L : LCtx α}
  {e : Term.InS φ Γ ⟨Ty.coprod A B, e'⟩} {r r' s s' : InS φ _ L}
  (h : r ≈ r') (h' : s ≈ s') : InS.case e r s ≈ InS.case e r' s'
  := Setoid.trans (InS.case_left_congr h) (InS.case_right_congr h')

theorem InS.cfg_entry_congr {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {β β' : InS φ Γ (R ++ L)} {G} (pβ : β ≈ β')
  : InS.cfg R β G ≈ InS.cfg R β' G := Uniform.cfg_entry _ rfl pβ (λi => (G i).prop)

theorem InS.cfg_block_congr {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α) (β : InS φ Γ (R ++ L)) (G) (i) {g' : InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  (pG : (G i) ≈ g')
  : InS.cfg R β G ≈ InS.cfg R β (Function.update G i g') := by
  simp only [eqv_def, cfg]
  rw [coe_update]
  apply Uniform.cfg_block
  exact β.prop
  exact (λi => (G i).prop)
  apply pG
  rfl

theorem InS.cfg_blocks_partial_congr {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α) (β : InS φ Γ (R ++ L)) {G G'} (pG : G ≈ G') (k : ℕ)
  : InS.cfg R β G ≈ InS.cfg R β (λi => if i < k then (G' i) else (G i)) := by
  induction k with
  | zero => simp only [not_lt_zero', ↓reduceIte]; exact Setoid.refl _
  | succ k I =>
    apply Setoid.trans I
    if h : R.length ≤ k then
      have h : ∀i : Fin R.length, i < k ↔ i < k + 1 := λi =>
        ⟨λ_ => Nat.lt_of_lt_of_le i.prop (Nat.le_succ_of_le h),
         λ_ => Nat.lt_of_lt_of_le i.prop h⟩
      simp only [h]
      apply Setoid.refl
    else
      have h' :
        (λi : Fin R.length => if i < k + 1 then (G' i) else (G i))
        = (Function.update
          (λi : Fin R.length => if i < k then (G' i) else (G i))
          ⟨k, Nat.lt_of_not_le h⟩ (G' ⟨k, Nat.lt_of_not_le h⟩))
        := funext (λi => by
          split
          case isTrue h =>
            cases h with
            | refl => simp
            | step h =>
              have h := Nat.lt_of_succ_le h
              rw [Function.update_noteq]
              simp [h]
              simp only [ne_eq, Fin.ext_iff]
              exact Nat.ne_of_lt h
          case isFalse h =>
            have h := Nat.lt_of_succ_le $ Nat.le_of_not_lt h
            have h' := Nat.not_lt_of_lt $ h
            rw [Function.update_noteq]
            simp [h']
            simp only [ne_eq, Fin.ext_iff]
            exact Ne.symm $ Nat.ne_of_lt h)
      rw [h']
      apply cfg_block_congr
      simp [pG ⟨k, Nat.lt_of_not_le h⟩]

theorem InS.cfg_blocks_congr {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α) (β : InS φ Γ (R ++ L)) {G G'} (pG : G ≈ G')
  : InS.cfg R β G ≈ InS.cfg R β G' := by
  have h : G' = λi : Fin R.length => if i < R.length then (G' i) else (G i) := by simp
  rw [h]
  apply cfg_blocks_partial_congr
  exact pG

theorem InS.cfg_congr {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α) {β β' : InS φ Γ (R ++ L)} (pβ : β ≈ β') {G G'} (pG : G ≈ G')
  : InS.cfg R β G ≈ InS.cfg R β' G' := by
  apply Setoid.trans
  apply cfg_entry_congr
  assumption
  apply cfg_blocks_congr
  assumption

theorem InS.cfg_congr' {Γ : Ctx α ε} {L : LCtx α}
  (n : ℕ) (R : LCtx α) (hR : R.length = n)
  {β β' : InS φ Γ (R ++ L)} (pβ : β ≈ β') {G G'} (pG : G ≈ G')
  : InS.cfg' n R hR β G ≈ InS.cfg' n R hR β' G' := by
  cases hR
  apply cfg_congr <;> assumption

theorem InS.vwk_congr_right {Γ Δ : Ctx α ε} {L : LCtx α} {r r' : InS φ Δ L}
  (ρ : Γ.InS Δ) (hr : r ≈ r') : r.vwk ρ ≈ r'.vwk ρ
  := Uniform.vwk TStep.vwk ρ.prop hr

theorem InS.vwk_congr {Γ Δ : Ctx α ε} {L : LCtx α} {r r' : InS φ Δ L}
  {ρ ρ' : Γ.InS Δ} (hρ : ρ ≈ ρ') (hr : r ≈ r') : r.vwk ρ ≈ r'.vwk ρ'
  := r.vwk_equiv hρ ▸ vwk_congr_right ρ' hr

theorem InS.lwk_congr_right {Γ : Ctx α ε} {L K : LCtx α} {r r' : InS φ Γ L}
  (ρ : L.InS K) (hr : r ≈ r') : r.lwk ρ ≈ r'.lwk ρ
  := Uniform.lwk TStep.lwk ρ.prop hr

theorem InS.lwk_congr {Γ : Ctx α ε} {L K : LCtx α} {r r' : InS φ Γ L}
  {ρ ρ' : L.InS K} (hρ : ρ ≈ ρ') (hr : r ≈ r') : r.lwk ρ ≈ r'.lwk ρ'
  := r.lwk_equiv hρ ▸ lwk_congr_right ρ' hr

theorem TStep.vsubst {Γ Δ : Ctx α ε} {L} {r r' : Region φ} {σ : Term.Subst φ}
  (hσ : σ.Wf Γ Δ) : TStep Δ L r r' → Uniform TStep Γ L (r.vsubst σ) (r'.vsubst σ)
  | TStep.let1_beta de dr => sorry
  | TStep.rewrite d d' p => sorry
  | TStep.reduce d d' p => sorry
  | TStep.initial di d d' => sorry
  | TStep.terminal de de' dr => sorry

theorem TStep.vsubst_to_congr {Γ Δ : Ctx α ε} {L}
  {r r' : InS φ Δ L} (σ : Term.Subst.InS φ Γ Δ) (h : TStep Δ L (r : Region φ) (↑r'))
  : r.vsubst σ ≈ r'.vsubst σ := by
  cases r; cases r'
  exact vsubst σ.prop h

theorem InS.vsubst_congr_right {Γ Δ : Ctx α ε} {L : LCtx α}
  (σ : Term.Subst.InS φ Γ Δ) {r r' : InS φ Δ L} (hr : r ≈ r') : r.vsubst σ ≈ r'.vsubst σ
  := Uniform.vsubst_flatten TStep.vsubst σ.prop hr

-- theorem InS.vsubst_congr {Γ Δ : Ctx α ε} {L r r' : InS φ Δ L}
--   {σ σ' : Term.Subst.InS φ Γ Δ} (hσ : σ ≈ σ') (hr : r ≈ r')
--   : r.vsubst σ ≈ r'.vsubst σ' := sorry

open Term.InS

theorem InS.let1_op {Γ : Ctx α ε} {L : LCtx α}
  {r : InS φ (⟨B, ⊥⟩::Γ) L}
  (f : φ) (hf : Φ.EFn f A B e)
  (a : Term.InS φ Γ ⟨A, e⟩)
    : r.let1 (a.op f hf)
    ≈ (r.vwk1.let1 ((var 0 (by simp)).op f hf)).let1 a
  := Uniform.rel $ TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.let1_let1 {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
  {r : InS φ (⟨B, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩) (b : Term.InS φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩)
    : let1 (a.let1 b) r
    ≈ (let1 a $ let1 b $ r.vwk1)
  := Uniform.rel $ TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.let1_pair {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α} (e' := ⊥)
  {r : InS φ (⟨Ty.prod A B, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩) (b : Term.InS φ Γ ⟨B, e⟩)
    : r.let1 (a.pair b) ≈ (
      let1 a $
      let1 (b.wk ⟨Nat.succ, (by simp)⟩) $
      let1 ((var 1 (by simp)).pair (e := e') (var 0 (by simp))) $
      r.vwk1.vwk1)
  := Uniform.rel $ TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.let1_inl {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α} (e' := ⊥)
  {r : InS φ (⟨A.coprod B, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩)
    : r.let1 a.inl
    ≈ (r.vwk1.let1 ((var 0 (by simp)).inl (e := e'))).let1 a
  := Uniform.rel $ TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.let1_inr {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α} (e' := ⊥)
  {r : InS φ (⟨A.coprod B, ⊥⟩::Γ) L}
  (b : Term.InS φ Γ ⟨B, e⟩)
    : r.let1 b.inr
    ≈ (r.vwk1.let1 ((var 0 (by simp)).inr (e := e'))).let1 b
  := Uniform.rel $ TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.let1_case {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
  {s : InS φ (⟨C, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨Ty.coprod A B, e⟩)
  (l : Term.InS φ (⟨A, ⊥⟩::Γ) ⟨C, e⟩)
  (r : Term.InS φ (⟨B, ⊥⟩::Γ) ⟨C, e⟩)
    : let1 (a.case l r) s
    ≈ case a (let1 l s.vwk1) (let1 r s.vwk1)
  := Uniform.rel $ TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.let1_abort {Γ : Ctx α ε} {L : LCtx α} {A : Ty α} (e' := ⊥)
  {r : InS φ (⟨A, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨Ty.empty, e⟩)
    : r.let1 (a.abort _)
    ≈ (r.vwk1.let1 ((var 0 (by simp)).abort (e := e') _)).let1 a
  := Uniform.rel $ TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.let2_bind {Γ : Ctx α ε} {L : LCtx α}
  {e : Term.InS φ Γ ⟨A.prod B, e⟩} {r : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  : let2 e r
  ≈ let1 e (let2 (var 0 Ctx.Var.shead) (r.vwk (Ctx.InS.wk0.liftn₂ (le_refl _) (le_refl _))))
  := Uniform.rel $ TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.case_bind {Γ : Ctx α ε} {L : LCtx α}
  {e : Term.InS φ Γ ⟨A.coprod B, e⟩} {r : InS φ (⟨A, ⊥⟩::Γ) L} {s : InS φ (⟨B, ⊥⟩::Γ) L}
  : case e r s
  ≈ let1 e (case (var 0 Ctx.Var.shead) r.vwk1 s.vwk1)
  := Uniform.rel $ TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.let2_op {Γ : Ctx α ε} {L : LCtx α}
  {r : InS φ (⟨C, ⊥⟩::⟨B, ⊥⟩::Γ) L}
  (f : φ) (hf : Φ.EFn f A (Ty.prod B C) e)
  (a : Term.InS φ Γ ⟨A, e⟩)
    : r.let2 (a.op f hf) ≈ (
      let1 a $
      let2 ((var 0 (by simp)).op f hf) $
      r.vwk (ρ := ⟨Nat.liftnWk 2 Nat.succ, by apply Ctx.Wkn.sliftn₂; simp⟩))
  := sorry
  -- := Uniform.rel $
  -- TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.let2_pair {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
  {r : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨A, e⟩)
  (b : Term.InS φ Γ ⟨B, e⟩)
    : r.let2 (a.pair b) ≈ (
      let1 a $
      let1 (b.wk ⟨Nat.succ, (by simp)⟩) r)
  := sorry
  -- := Uniform.rel $
  -- TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.let2_abort {Γ : Ctx α ε} {L : LCtx α} {A : Ty α} (e' := ⊥)
  {r : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  (a : Term.InS φ Γ ⟨Ty.empty, e⟩)
    : r.let2 (a.abort _) ≈ (
      let1 a $
      let2 ((var 0 (by simp)).abort (e := e') (A.prod B)) $
      r.vwk ⟨Nat.liftnWk 2 Nat.succ, by apply Ctx.Wkn.sliftn₂; simp⟩)
    := sorry
  -- := Uniform.rel $
  -- TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.case_op {Γ : Ctx α ε} {L : LCtx α}
  (f : φ) (hf : Φ.EFn f A (B.coprod C) e)
  (a : Term.InS φ Γ ⟨A, e⟩) (r : InS φ (⟨B, ⊥⟩::Γ) L) (s : InS φ (⟨C, ⊥⟩::Γ) L)
  : r.case (a.op f hf) s ≈
    (let1 a $ case (Term.InS.op f hf (var 0 (by simp))) r.vwk1 s.vwk1)
  := sorry
  -- := Uniform.rel $
  -- TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.case_abort {Γ : Ctx α ε} {L : LCtx α} (e' := ⊥)
  (a : Term.InS φ Γ ⟨Ty.empty, e⟩) (r : InS φ (⟨A, ⊥⟩::Γ) L) (s : InS φ (⟨B, ⊥⟩::Γ) L)
  : r.case (a.abort _) s ≈
    (let1 a $ case (Term.InS.abort (e := e') (var 0 (by simp)) (A.coprod B)) r.vwk1 s.vwk1)
  := sorry
  -- := Uniform.rel $
  -- TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

-- TODO: replacements for let1_case, let2_case

theorem InS.cfg_br_lt {Γ : Ctx α ε} {L : LCtx α}
  (ℓ) (a : Term.InS φ Γ ⟨A, ⊥⟩)
  (R : LCtx α)  (G : (i : Fin R.length) → InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  (hℓ : (R ++ L).Trg ℓ A) (hℓ' : ℓ < R.length)
  : (InS.br ℓ a hℓ).cfg R G
  ≈ (let1 a $ (G ⟨ℓ, hℓ'⟩).vwk_id (by simp only [Ctx.Wkn.lift_id_iff,
    Prod.mk_le_mk, le_refl, and_true, Ctx.Wkn.id]; exact List.get_append ℓ hℓ' ▸ hℓ.get)).cfg R G
  := Uniform.rel $ TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

-- TODO: fix this statement ^

theorem InS.cfg_let1 {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨A, ea⟩)
  (R : LCtx α) (β : InS φ (⟨A, ⊥⟩::Γ) (R ++ L))
  (G : (i : Fin R.length) → InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
    : (let1 a β).cfg R G ≈ (let1 a $ β.cfg R (λi => (G i).vwk1))
  := Uniform.rel $ TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.cfg_let2 {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨Ty.prod A B, ea⟩)
  (R : LCtx α) (β : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) (R ++ L))
  (G : (i : Fin R.length) → InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
    : (let2 a β).cfg R G ≈ (let2 a $ β.cfg R (λi => (G i).vwk1.vwk1))
  := Uniform.rel $ TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.cfg_case {Γ : Ctx α ε} {L : LCtx α}
  (e : Term.InS φ Γ ⟨Ty.coprod A B, ea⟩)
  (R : LCtx α)
  (r : InS φ (⟨A, ⊥⟩::Γ) (R ++ L))
  (s : InS φ (⟨B, ⊥⟩::Γ) (R ++ L))
  (G : (i : Fin R.length) → InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
    : (InS.case e r s).cfg R G
    ≈ InS.case e (r.cfg R (λi => (G i).vwk1)) (s.cfg R (λi => (G i).vwk1))
  := Uniform.rel $ TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.cfg_cfg_eqv_cfg' {Γ : Ctx α ε} {L : LCtx α}
  (R S : LCtx α) (β : InS φ Γ (R ++ (S ++ L)))
  (G : (i : Fin R.length) → InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ (S ++ L)))
  (G' : (i : Fin S.length) → InS φ (⟨S.get i, ⊥⟩::Γ) (S ++ L))
    : (β.cfg R G).cfg S G'
    ≈ (β.cast rfl (by rw [List.append_assoc])).cfg'
      (R.length + S.length) (R ++ S) (by rw [List.length_append])
      (Fin.addCases
        (λi => (G i).cast (by
          simp only [List.get_eq_getElem, Fin.cast, Fin.coe_castAdd]
          rw [List.getElem_append]
          -- TODO: put in discretion
          ) (by rw [List.append_assoc]))
        (λi => ((G' i).lwk (LCtx.InS.add_left_append (S ++ L) R)).cast (by
          simp only [List.get_eq_getElem, Fin.cast, Fin.coe_natAdd]
          -- TODO: put in discretion
          sorry
        )
          (by rw [List.append_assoc])))
  := Uniform.rel $
  TStep.rewrite InS.coe_wf InS.coe_wf (by
    simp only [Set.mem_setOf_eq, coe_cfg, id_eq, coe_cfg', coe_cast]
    apply Rewrite.cast_trg
    apply Rewrite.cfg_cfg
    congr
    funext i
    if h : i < R.length then
      have hi : i = Fin.castAdd S.length ⟨i, h⟩ := rfl
      rw [hi]
      simp only [Fin.addCases_left]
      rfl
    else
      let hi := Fin.natAdd_subNat_cast (le_of_not_lt h)
      rw [<-hi]
      simp only [Fin.addCases_right]
      rfl
    )

theorem InS.cfg_zero {Γ : Ctx α ε} {L : LCtx α}
  (β : InS φ Γ L)
  : β.cfg [] (λi => i.elim0) ≈ β
  := Uniform.rel $ TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.let2_eta {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨Ty.prod A B, ea⟩)
  (r : InS φ (⟨A.prod B, ⊥⟩::Γ) L)
    : (let2 a $
        let1 ((var 1 ⟨by simp, le_refl _⟩).pair (var 0 (by simp))) r.vwk1.vwk1)
    ≈ let1 a r
  := Uniform.rel $ TStep.rewrite InS.coe_wf InS.coe_wf (by constructor)

theorem InS.wk_cfg {Γ : Ctx α ε} {L : LCtx α}
  (R S : LCtx α) (β : InS φ Γ (R ++ L))
  (G : (i : Fin S.length) → InS φ ((List.get S i, ⊥)::Γ) (R ++ L))
  (ρ : Fin R.length → Fin S.length)
  (hρ : LCtx.Wkn (R ++ L) (S ++ L) (Fin.toNatWk ρ))
  : cfg S (β.lwk ⟨Fin.toNatWk ρ, hρ⟩) (λi => (G i).lwk ⟨Fin.toNatWk ρ, hρ⟩)
  ≈ cfg R β (λi => (G (ρ i)).vwk_id (Ctx.Wkn.id.toFinWk_id hρ i))
  := Uniform.rel $ TStep.reduce InS.coe_wf InS.coe_wf (by constructor)

theorem InS.case_inl {Γ : Ctx α ε} {L : LCtx α}
  (e : Term.InS φ Γ ⟨A, ea⟩)
  (r : InS φ (⟨A, ⊥⟩::Γ) L)
  (s : InS φ (⟨B, ⊥⟩::Γ) L)
    : case e.inl r s ≈ let1 e r
  := Uniform.rel $ TStep.reduce InS.coe_wf InS.coe_wf (by constructor)

theorem InS.case_inr {Γ : Ctx α ε} {L : LCtx α}
  (e : Term.InS φ Γ ⟨B, ea⟩)
  (r : InS φ (⟨A, ⊥⟩::Γ) L)
  (s : InS φ (⟨B, ⊥⟩::Γ) L)
    : case e.inr r s ≈ let1 e s
  := Uniform.rel $ TStep.reduce InS.coe_wf InS.coe_wf (by constructor)

theorem InS.let1_beta {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ Γ ⟨A, ⊥⟩)
  (r : InS φ (⟨A, ⊥⟩::Γ) L)
    : let1 a r ≈ r.vsubst a.subst0
  := Uniform.rel $ TStep.let1_beta a.prop r.prop

theorem InS.initial {Γ : Ctx α ε} {L : LCtx α} (hi : Γ.IsInitial) (r r' : InS φ Γ L) : r ≈ r'
  := Uniform.rel (TStep.initial hi r.2 r'.2)

theorem InS.terminal {Γ : Ctx α ε} {L : LCtx α}
  (e e' : Term.InS φ Γ ⟨Ty.unit, ⊥⟩) (r : InS φ (⟨Ty.unit, ⊥⟩::Γ) L)
  : let1 e r ≈ let1 e' r
  := Uniform.rel (TStep.terminal e.2 e'.2 r.2)

-- theorem InS.let1_cong_uniform_alt {Γ : Ctx α ε} {L : LCtx α}
--   {a a' : Term φ} (ha : Term.Wf.Cong Term.TStep Γ V a a') (r : Region φ)
--   (hr : Wf (⟨V.1, ⊥⟩::Γ) r L)
--   : Uniform TStep Γ L (Region.let1 a r) (Region.let1 a' r) := by
--   induction ha generalizing r with
--   | op hf ha Ia =>
--     apply Uniform.trans
--     exact Uniform.rel $ TStep.let1_op hf (ha.left Term.TStep.left) hr
--     apply Uniform.symm
--     apply Uniform.trans
--     exact Uniform.rel $ TStep.let1_op hf (ha.right Term.TStep.right) hr
--     apply Uniform.symm
--     exact Ia _ (hr.vwk1.let1 ((Term.Wf.var (by simp)).op hf))
--   | let1_bound ha hb Ia =>
--     apply Uniform.trans
--     apply Uniform.rel
--     exact TStep.let1_let1 (ha.left Term.TStep.left) hb hr
--     apply Uniform.symm
--     apply Uniform.trans
--     exact Uniform.rel $ TStep.let1_let1 (ha.right Term.TStep.right) hb hr
--     apply Uniform.symm
--     exact Ia _ (hr.vwk1.let1 hb)
--   | let1_body ha hb Ib =>
--     apply Uniform.trans
--     exact Uniform.rel $ TStep.let1_let1 ha (hb.left Term.TStep.left) hr
--     apply Uniform.symm
--     apply Uniform.trans
--     exact Uniform.rel $ TStep.let1_let1 ha (hb.right Term.TStep.right) hr
--     apply Uniform.symm
--     exact Uniform.let1 ha $ Ib _ hr.vwk1
--   | pair_left ha hb Ia =>
--     apply Uniform.trans
--     exact Uniform.rel $ TStep.let1_pair (ha.left Term.TStep.left) hb hr
--     apply Uniform.symm
--     apply Uniform.trans
--     exact Uniform.rel $ TStep.let1_pair (ha.right Term.TStep.right) hb hr
--     apply Uniform.symm
--     exact Ia _ (Wf.let1 hb.wk0
--       (Wf.let1 (Term.Wf.pair (Term.Wf.var Ctx.Var.shead.step) (Term.Wf.var Ctx.Var.shead))
--       hr.vwk1.vwk1))
--   | pair_right ha hb Ib =>
--     apply Uniform.trans
--     exact Uniform.rel $ TStep.let1_pair ha (hb.left Term.TStep.left) hr
--     apply Uniform.symm
--     apply Uniform.trans
--     exact Uniform.rel $ TStep.let1_pair ha (hb.right Term.TStep.right) hr
--     apply Uniform.symm
--     sorry
--   | let2_bound => sorry
--   | let2_body => sorry
--   | inl => sorry
--   | inr => sorry
--   | case_disc => sorry
--   | case_left => sorry
--   | case_right => sorry
--   | abort => sorry
--   | rel => sorry

theorem InS.let1_uniform_congr {Γ : Ctx α ε} {L : LCtx α}
  {a a' : Term φ} (ha : Term.Uniform Term.TStep Γ ⟨A, e⟩ a a') (r : InS φ (⟨A, ⊥⟩::Γ) L)
  : InS.let1 ⟨a, ha.left Term.TStep.wf⟩ r ≈ InS.let1 ⟨a', ha.right Term.TStep.wf⟩ r
  := Uniform.let1_equiv ha r.prop

theorem InS.let1_bound_congr {Γ : Ctx α ε} {L : LCtx α}
  {a a' : Term.InS φ Γ ⟨A, e⟩} (ha : a ≈ a') (r : InS φ (⟨A, ⊥⟩::Γ) L)
  : InS.let1 a r ≈ InS.let1 a' r := let1_uniform_congr ha r

theorem InS.let1_congr {Γ : Ctx α ε} {L : LCtx α}
  {a a' : Term.InS φ Γ ⟨A, e⟩} (ha : a ≈ a') {r r' : InS φ (⟨A, ⊥⟩::Γ) L} (hr : r ≈ r')
  : InS.let1 a r ≈ InS.let1 a' r' := (let1_bound_congr ha r).trans (let1_body_congr a' hr)

theorem InS.let2_bound_congr {Γ : Ctx α ε} {L : LCtx α}
  {a a' : Term.InS φ Γ ⟨Ty.prod A B, e⟩} (ha : a ≈ a') (r : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L)
  : InS.let2 a r ≈ InS.let2 a' r
  := Setoid.trans let2_bind (Setoid.trans (let1_bound_congr ha _) let2_bind.symm)

theorem InS.let2_congr {Γ : Ctx α ε} {L : LCtx α}
  {a a' : Term.InS φ Γ ⟨Ty.prod A B, e⟩} (ha : a ≈ a') {r r' : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  (hr : r ≈ r') : InS.let2 a r ≈ InS.let2 a' r'
  := (let2_bound_congr ha r).trans (let2_body_congr a' hr)

theorem InS.case_disc_congr {Γ : Ctx α ε} {L : LCtx α}
  {a a' : Term.InS φ Γ ⟨Ty.coprod A B, e⟩} (ha : a ≈ a') (r : InS φ (⟨A, ⊥⟩::Γ) L)
  (s : InS φ (⟨B, ⊥⟩::Γ) L) : InS.case a r s ≈ InS.case a' r s
  := Setoid.trans case_bind (Setoid.trans (let1_bound_congr ha _) case_bind.symm)

theorem InS.case_congr {Γ : Ctx α ε} {L : LCtx α}
  {a a' : Term.InS φ Γ ⟨Ty.coprod A B, e⟩} (ha : a ≈ a') {r r' : InS φ (⟨A, ⊥⟩::Γ) L}
  (hr : r ≈ r') {s s' : InS φ (⟨B, ⊥⟩::Γ) L} (hs : s ≈ s')
  : InS.case a r s ≈ InS.case a' r' s'
  := (case_disc_congr ha r s).trans (case_branches_congr hr hs)

theorem InS.br_bind {Γ : Ctx α ε} {L : LCtx α}
  {ℓ} {a : Term.InS φ Γ ⟨A, ⊥⟩} {hℓ : L.Trg ℓ A}
  : br ℓ a hℓ ≈ let1 a (br ℓ (var 0 Ctx.Var.shead) hℓ)
  := by apply Setoid.symm; apply let1_beta

theorem InS.br_congr {Γ : Ctx α ε} {L : LCtx α} (ℓ) {a a' : Term.InS φ Γ ⟨A, ⊥⟩}
  (ha : a ≈ a') (hℓ : L.Trg ℓ A) : InS.br ℓ a hℓ ≈ InS.br ℓ a' hℓ
  := Setoid.trans br_bind (Setoid.trans (let1_bound_congr ha _) br_bind.symm)

theorem InS.vsubst_subst_equiv {Γ Δ : Ctx α ε} {L : LCtx α}
  {σ σ' : Term.Subst.InS φ Γ Δ} (hσ : σ ≈ σ') (r : InS φ Δ L) : r.vsubst σ ≈ r.vsubst σ'
  := by induction r using InS.induction generalizing Γ with
  | br ℓ a hℓ => exact br_congr ℓ (Term.InS.subst_equiv_congr hσ a) hℓ
  | let1 a r Ir =>
    exact let1_congr
      (Term.InS.subst_equiv_congr hσ a)
      (Ir (Term.Subst.InS.slift_congr hσ))
  | let2 a r Ir =>
    exact let2_congr
      (Term.InS.subst_equiv_congr hσ a)
      (Ir (Term.Subst.InS.sliftn₂_congr hσ))
  | case a r s Ir Is =>
    exact case_congr
      (Term.InS.subst_equiv_congr hσ a)
      (Ir (Term.Subst.InS.slift_congr hσ))
      (Is (Term.Subst.InS.slift_congr hσ))
  | cfg R hβ hG Iβ IG => exact cfg_congr _ (Iβ hσ) (λi => IG i (Term.Subst.InS.slift_congr hσ))

theorem InS.vsubst_congr {Γ Δ : Ctx α ε} {L : LCtx α}
  {σ σ' : Term.Subst.InS φ Γ Δ} (hσ : σ ≈ σ') {r r' : InS φ Δ L} (hr : r ≈ r')
  : r.vsubst σ ≈ r'.vsubst σ'
  := (vsubst_subst_equiv hσ r).trans (vsubst_congr_right _ hr)
