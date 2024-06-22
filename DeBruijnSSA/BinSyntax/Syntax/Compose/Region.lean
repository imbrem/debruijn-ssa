import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Rewrite

namespace BinSyntax

namespace Region

variable [Φ: EffectSet φ ε] [SemilatticeSup ε] [OrderBot ε]

def lsubst0 (r : Region φ) : Subst φ
  | 0 => r
  | ℓ + 1 => br ℓ (Term.var 0)

def alpha (ℓ : ℕ) (r : Region φ) : Subst φ
  := Function.update Subst.id ℓ r

def ret (e : Term φ) := br 0 e

def nil : Region φ := ret (Term.var 0)

@[simp]
theorem nil_vwk1 : nil.vwk1 = @nil φ := rfl

@[simp]
theorem alpha0_nil : alpha 0 nil = @Subst.id φ := by
  rw [alpha, Function.update_eq_self_iff]
  rfl

theorem vlift_alpha (n : ℕ) (r : Region φ) : (alpha n r).vlift = alpha n r.vwk1 := by
  simp only [Subst.vlift, alpha, Function.comp_update]
  rfl

theorem vliftn_alpha (n m : ℕ) (r : Region φ) : (alpha n r).vliftn m = alpha n (r.vwk (Nat.liftWk (· + m))) := by
  simp only [Subst.vliftn, alpha, Function.comp_update]
  rfl

theorem lift_alpha (n) (r : Region φ) : (alpha n r).lift = alpha (n + 1) (r.lwk Nat.succ) := by
  funext i; cases i; rfl;
  simp only [Subst.lift, alpha, Function.update, eq_rec_constant, Subst.id, dite_eq_ite,
    add_left_inj]
  split <;> rfl

theorem liftn_alpha (n m) (r : Region φ) : (alpha n r).liftn m = alpha (n + m) (r.lwk (· + m)) := by
  rw [Subst.liftn_eq_iterate_lift]
  induction m generalizing n r with
  | zero => simp
  | succ m I =>
    simp only [Function.iterate_succ, Function.comp_apply, lift_alpha, I, lwk_lwk]
    apply congrArg₂
    simp_arith
    apply congrFun
    apply congrArg
    funext i
    simp_arith

theorem vwk_lift_alpha (n : ℕ) (r : Region φ)
  : vwk (Nat.liftWk ρ) ∘ (alpha n r) = alpha n (r.vwk (Nat.liftWk ρ)) := by
  simp [alpha, Function.comp_update]

def append (r r' : Region φ) : Region φ := r.lsubst (r'.vwk1.alpha 0)

instance : Append (Region φ) := ⟨Region.append⟩

theorem append_def (r r' : Region φ) : r ++ r' = r.lsubst (r'.vwk1.alpha 0) := rfl

@[simp]
theorem append_nil (r : Region φ) : r ++ nil = r := by simp [append_def]

@[simp]
theorem nil_append (r : Region φ) : nil ++ r = r := by
  simp only [append_def, lsubst, Subst.vlift, vwk1, alpha, Function.comp_apply, Function.update_same]
  rw [<-vsubst_fromWk_apply, <-vsubst_comp_apply, <-vsubst_id r]
  congr <;> simp

theorem lsubst_alpha_let1 (k) (e : Term φ) (r r' : Region φ)
  : (r.let1 e).lsubst (r'.alpha k) = (r.lsubst (r'.vwk1.alpha k)).let1 e
  := by simp [vlift_alpha]

theorem let1_append (e : Term φ) (r r' : Region φ) : r.let1 e ++ r' = (r ++ r'.vwk1).let1 e
  := lsubst_alpha_let1 0 e _ _

theorem lsubst_alpha_let2 (k) (e : Term φ) (r r' : Region φ)
  : (r.let2 e).lsubst (r'.alpha k) = (r.lsubst ((r'.vwk (Nat.liftWk (· + 2))).alpha k)).let2 e
  := by simp only [append_def, lsubst, vlift_alpha, vliftn_alpha, vwk_vwk, vwk1, ← Nat.liftWk_comp]

theorem let2_append (e : Term φ) (r r' : Region φ) : r.let2 e ++ r' = (r ++ (r'.vwk (Nat.liftWk (· + 2)))).let2 e
  := by
  simp only [append_def, lsubst, vlift_alpha, vliftn_alpha, vwk_vwk, vwk1, ← Nat.liftWk_comp]
  rfl

theorem lsubst_alpha_case (k) (e : Term φ) (s t r : Region φ)
  : (case e s t).lsubst (r.alpha k) = (case e (s.lsubst (r.vwk1.alpha k)) (t.lsubst (r.vwk1.alpha k)))
  := by
  simp only [append_def, lsubst, vlift_alpha, vwk_vwk, vwk1, ← Nat.liftWk_comp]

theorem case_append (e : Term φ) (s t r : Region φ) : case e s t ++ r = case e (s ++ r.vwk1) (t ++ r.vwk1)
  := by simp only [append_def, lsubst, vlift_alpha, vwk_vwk, vwk1, ← Nat.liftWk_comp]

theorem lsubst_alpha_cfg (β n G k) (r : Region φ)
  : (cfg β n G).lsubst (r.alpha k) = cfg
    (β.lsubst ((r.lwk (· + n)).alpha (k + n))) n
    (lsubst ((r.lwk (· + n)).vwk1.alpha (k + n)) ∘ G)
  := by
  simp only [append_def, lsubst, vlift_alpha, vwk_vwk, vwk1, ← Nat.liftWk_comp, liftn_alpha]
  rfl

theorem vwk_liftWk_lsubst_alpha
  : (lsubst (alpha n r₁) r₀).vwk (Nat.liftWk ρ)
  = lsubst (alpha n (r₁.vwk (Nat.liftnWk 2 ρ))) (r₀.vwk (Nat.liftWk ρ))
  := by simp [vwk_lsubst, vwk_lift_alpha, Nat.liftnWk_eq_iterate_liftWk]

theorem vwk1_lsubst_alpha {r₀ r₁ : Region φ}
  : (lsubst (alpha n r₁) r₀).vwk1 = lsubst (alpha n (r₁.vwk (Nat.liftnWk 2 Nat.succ))) r₀.vwk1 := by
  rw [vwk1, vwk_lsubst, vwk_lift_alpha, Nat.liftnWk_eq_iterate_liftWk]
  rfl

theorem vwk_liftWk_lsubst_alpha_vwk1 {r₀ r₁ : Region φ}
  : (lsubst (alpha n r₁.vwk1) r₀).vwk (Nat.liftWk ρ)
  = lsubst (alpha n ((r₁.vwk (Nat.liftWk ρ)).vwk1)) (r₀.vwk (Nat.liftWk ρ)) := by
  rw [vwk_liftWk_lsubst_alpha]
  congr
  apply congrArg
  simp [vwk1, vwk_vwk, Nat.liftnWk_eq_iterate_liftWk, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]

theorem vwk1_lsubst_alpha_vwk1 {r₀ r₁ : Region φ}
  : (lsubst (alpha n r₁.vwk1) r₀).vwk1 = lsubst (alpha n (r₁.vwk1.vwk1)) r₀.vwk1 := by
  rw [vwk1_lsubst_alpha]
  simp only [vwk1, vwk_vwk]
  apply congrFun
  apply congrArg
  apply congrArg
  congr
  funext k; cases k <;> rfl

def PRwD.lsubst_alpha {Γ : ℕ → ε} {r₀ r₀'}
  (p : PRwD Γ r₀ r₀') (n) (r₁ : Region φ)
  : PRwD Γ (r₀.lsubst (alpha n r₁)) (r₀'.lsubst (alpha n r₁)) := match p with
  | let1_op f e r => cast_trg (let1_op _ _ _) (by simp [vlift_alpha, <-vwk1_lsubst_alpha_vwk1])
  | let1_pair a b r => cast_trg (let1_pair _ _ _) (by simp [vlift_alpha, <-vwk1_lsubst_alpha_vwk1])
  | let1_inl e r => cast_trg (let1_inl _ _) (by simp [vlift_alpha, <-vwk1_lsubst_alpha_vwk1])
  | let1_inr e r => cast_trg (let1_inr _ _) (by simp [vlift_alpha, <-vwk1_lsubst_alpha_vwk1])
  | let1_abort e r => cast_trg (let1_abort _ _) (by simp [vlift_alpha, <-vwk1_lsubst_alpha_vwk1])
  | let2_op f e r => cast_trg (let2_op _ _ _) (by
    --TODO: factor more nicely...
    simp only [vliftn_alpha, vwk_lsubst, vwk_lift_alpha, vwk_vwk, lsubst, vlift_alpha, vwk1]
    congr
    apply congrArg
    apply congrFun
    apply congrArg
    funext k; cases k <;> rfl)
  | let2_pair a b r => cast_trg (let2_pair _ _ _) (by
    --TODO: factor more nicely...
    simp only [lsubst, vliftn_alpha, vlift_alpha, vwk1, vwk_vwk, <-Nat.liftWk_comp]
    rfl)
  | let2_abort e r => cast_trg (let2_abort _ _) (by
    --TODO: factor more nicely...
    simp only [vliftn_alpha, vwk_lsubst, vwk_lift_alpha, vwk_vwk, lsubst, vlift_alpha, vwk1]
    congr
    apply congrArg
    apply congrFun
    apply congrArg
    funext k; cases k <;> rfl)
  | case_op f e r s => cast_trg (case_op _ _ _ _) (by simp [vlift_alpha, <-vwk1_lsubst_alpha_vwk1])
  | case_abort e r s
    => cast_trg (case_abort _ _ _) (by simp [vlift_alpha, <-vwk1_lsubst_alpha_vwk1])
  | let1_case a b r s => cast_trg (let1_case _ _ _ _)
    (by simp [vlift_alpha, <-vwk1_lsubst_alpha_vwk1])
  | let2_case a b r s => cast_trg (let2_case _ _ _ _) (by
    --TODO: factor more nicely...
    simp only [vliftn_alpha, vwk_lsubst, vwk_lift_alpha, vwk_vwk, lsubst, vlift_alpha, vwk1]
    congr <;>
    apply congrArg <;>
    apply congrFun <;>
    apply congrArg <;>
    funext k <;> cases k <;> rfl)
  | cfg_br_lt ℓ e n G hℓ => by
    simp only [lsubst, Subst.liftn, hℓ, ↓reduceIte, vsubst.eq_1, Term.subst, Term.subst0_zero]
    exact cfg_br_lt ℓ e n _ hℓ
  | cfg_let1 a β n G => cast_trg (cfg_let1 _ _ _ _) (by
    simp only [
      vliftn_alpha, liftn_alpha, vwk_lsubst, vwk_lift_alpha, vwk_vwk, lsubst, vlift_alpha, vwk1,
      vwk_lwk]
    congr
    funext i
    simp only [Function.comp_apply, vwk_lsubst, vwk_lift_alpha, vwk_vwk, ← Nat.liftWk_comp,
      Nat.liftWk_comp_succ, lwk_vwk]
  )
  | cfg_let2 a β n G => cast_trg (cfg_let2 _ _ _ _) (by
    simp only [
      vliftn_alpha, liftn_alpha, vwk_lsubst, vwk_lift_alpha, vwk_vwk, lsubst, vlift_alpha, vwk1,
      vwk_lwk]
    congr
    funext i
    simp only [Function.comp_apply, vwk_lsubst, vwk_lift_alpha, vwk_vwk, ← Nat.liftWk_comp,
      Nat.liftWk_comp_succ, lwk_vwk]
    rfl
    )
  | cfg_case e r s n G => cast_trg (cfg_case _ _ _ _ _) (by
    simp only [
      vliftn_alpha, liftn_alpha, vwk_lsubst, vwk_lift_alpha, vwk_vwk, lsubst, vlift_alpha, vwk1,
      vwk_lwk]
    congr <;>
    funext i <;>
    simp only [Function.comp_apply, vwk_lsubst, vwk_lift_alpha, vwk_vwk, ← Nat.liftWk_comp,
    Nat.liftWk_comp_succ, lwk_vwk]
  )
  | cfg_cfg β n G n' G' => cast_trg (cfg_cfg _ _ _ _ _) (by
    simp only [lsubst, cfg.injEq, heq_eq_eq, true_and, Subst.liftn_liftn]
    funext i
    simp only [Fin.addCases, Function.comp_apply, eq_rec_constant]
    split
    . rfl
    . simp only [liftn_alpha, vlift_alpha, lwk_lsubst, lsubst_lwk]
      congr
      funext k
      simp only [alpha, Function.comp_apply, Function.update, eq_rec_constant, dite_eq_ite]
      split
      case isTrue h =>
        cases h
        rw [Nat.add_assoc]
        simp only [add_right_inj]
        rw [Nat.add_comm]
        simp only [↓reduceIte, vwk1, vwk_lwk, lwk_lwk]
        congr
        funext k'
        simp_arith
      case isFalse h =>
        rw [ite_cond_eq_false]
        rfl
        rw [Nat.add_comm n n', <-Nat.add_assoc]
        simp [h]
  )
  | cfg_zero β G => by
    simp only [lsubst, Subst.liftn_zero]
    apply cfg_zero
  | cfg_fuse β n G k ρ hρ => by
    rw [
      lsubst_cfg, lsubst_cfg,
      lsubst_liftn_lwk_toNatWk,
      <-Function.comp.assoc,
      Subst.vlift_liftn_comm,
      lsubst_liftn_comp_lwk_toNatWk,
      Function.comp.assoc
    ]
    apply cast_trg
    apply cfg_fuse
    exact hρ
    rw [Subst.vlift_liftn_comm]
    rfl

def PStepD.lsubst_alpha {Γ : ℕ → ε} {r₀ r₀'}
  (p : PStepD Γ r₀ r₀') (k) (r₁ : Region φ)
  : PStepD Γ (r₀.lsubst (alpha k r₁)) (r₀'.lsubst (alpha k r₁)) := match p with
  | rw p => rw (p.lsubst_alpha k r₁)
  | rw_symm p => rw_symm (p.lsubst_alpha k r₁)
  | let1_beta e r he => cast_trg (let1_beta e _ he) (by rw [vsubst_subst0_lsubst_vlift])
  | case_inl e r s => case_inl e _ _
  | case_inr e r s => case_inr e _ _
  | wk_cfg β n G k ρ => by
    rw [
      lsubst_cfg, lsubst_cfg,
      lsubst_liftn_lwk_toNatWk,
      <-Function.comp.assoc,
      Subst.vlift_liftn_comm,
      lsubst_liftn_comp_lwk_toNatWk,
      Function.comp.assoc
    ]
    apply cast_trg
    apply wk_cfg
    rw [Subst.vlift_liftn_comm]
    rfl
  | dead_cfg_left β n G m G' =>
    cast_src (by
      simp only [lsubst_cfg, Fin.comp_addCases, liftn_alpha, vlift_alpha, lsubst_lwk, lwk_lsubst]
      congr
      . funext i
        -- TODO: factor out more nicely
        simp only [alpha, Nat.add_comm n m, ← Nat.add_assoc, Function.comp_apply, Function.update,
          add_left_inj, eq_rec_constant, dite_eq_ite]
        split
        . simp [lwk_lwk, <-Nat.add_assoc]
        . rfl
      . funext i
        congr
        . funext i
          simp only [Function.comp_apply, lsubst_lwk, lwk_lsubst]
          congr
          -- TODO: factor out more nicely
          funext i
          simp only [alpha, Nat.add_comm n m, ← Nat.add_assoc, Function.comp_apply, Function.update,
            add_left_inj, eq_rec_constant, dite_eq_ite]
          split
          . simp [vwk1, lwk_vwk, lwk_lwk, <-Nat.add_assoc]
          . rfl
    ) (dead_cfg_left _ n (lsubst (alpha (k + (n + m)) (lwk (· + (n + m)) r₁)).vlift ∘ G) m _)

-- TODO: factor out as more general lifting lemma
def SCongD.lsubst_alpha {Γ : ℕ → ε} {r₀ r₀'}
  (p : SCongD (PStepD Γ) r₀ r₀') (n) (r₁ : Region φ)
  : RWD (PStepD Γ) (r₀.lsubst (alpha n r₁)) (r₀'.lsubst (alpha n r₁)) := match p with
  | SCongD.step s => RWD.single (SCongD.step (s.lsubst_alpha n r₁))
  | SCongD.let1 e p => by
    simp only [lsubst_alpha_let1]
    apply RWD.let1 e
    apply lsubst_alpha p _ _
  | SCongD.let2 e p => by
    simp only [lsubst_alpha_let2]
    apply RWD.let2 e
    apply lsubst_alpha p _ _
  | SCongD.case_left e p t => by
    simp only [lsubst_alpha_case]
    apply RWD.case_left e
    apply lsubst_alpha p _ _
  | SCongD.case_right e s p => by
    simp only [lsubst_alpha_case]
    apply RWD.case_right e
    apply lsubst_alpha p _ _
  | SCongD.cfg_entry p n G => by
    simp only [lsubst_alpha_cfg]
    apply RWD.cfg_entry
    apply lsubst_alpha p _ _
  | SCongD.cfg_block β n G i p => by
    simp only [lsubst_alpha_cfg, Function.comp_update]
    apply RWD.cfg_block
    apply lsubst_alpha p _ _

-- TODO: factor out as more general lifting lemma
set_option linter.unusedVariables false in
def RWD.lsubst_alpha {Γ : ℕ → ε} {r₀ r₀'}
  (p : RWD (PStepD Γ) r₀ r₀') (n) (r₁ : Region φ)
  : RWD (PStepD Γ) (r₀.lsubst (alpha n r₁)) (r₀'.lsubst (alpha n r₁))
  := match p with
  | RWD.refl _ => RWD.refl _
  | RWD.cons p s => RWD.comp (p.lsubst_alpha n r₁) (s.lsubst_alpha n r₁)

def RWD.append_right {Γ : ℕ → ε} {r₀ r₀' : Region φ}
  (p : RWD (PStepD Γ) r₀ r₀') (r₁)
  : RWD (PStepD Γ) (r₀ ++ r₁) (r₀' ++ r₁)
  := p.lsubst_alpha 0 _

@[simp]
theorem Subst.vwk_liftWk_comp_id : vwk (Nat.liftWk ρ) ∘ id = @id φ := rfl

@[simp]
theorem Subst.vwk_liftnWk_comp_id (n : ℕ) : vwk (Nat.liftnWk (n + 1) ρ) ∘ id = @id φ := by
  rw [Nat.liftnWk_succ']
  rfl

theorem append_assoc (r r' r'' : Region φ) : (r ++ r') ++ r'' = r ++ (r' ++ r'')
  := by
  simp only [append_def, lsubst_lsubst]
  congr
  funext ℓ
  simp only [
    Subst.comp, Subst.vlift, vwk1, alpha, Function.comp_apply, Function.comp_update,
    Subst.vwk_liftWk_comp_id, vwk_vwk
  ]
  cases ℓ with
  | zero =>
    simp only [
      Function.update_same, vwk_lsubst, Function.comp_update, Subst.vwk_liftWk_comp_id, vwk_vwk]
    apply congrFun
    apply congrArg
    apply congrArg
    congr
    funext n
    cases n <;> rfl
  | succ => rfl

def lappend (r r' : Region φ) : Region φ := r ++ r'.let1V0

instance : ShiftRight (Region φ) := ⟨Region.lappend⟩

theorem lappend_def (r r' : Region φ) : r >>> r' = r ++ r'.let1V0 := rfl

theorem lappend_nil (r : Region φ) : r >>> nil = r ++ nil.let1V0 := rfl

-- def EStep.lappend_nil_id (Γ : ℕ → ε) (r : Region φ) : Quiver.Path (toEStep Γ (r >>> nil)) (toEStep Γ r)
--   := sorry

theorem nil_lappend (r : Region φ) : nil >>> r = r.let1V0 := nil_append _

def wappend (r r' : Region φ) : Region φ := cfg r 1 (λ_ => r'.lwk Nat.succ)

theorem wappend_def (r r' : Region φ) : r.wappend r' = cfg r 1 (λ_ => r'.lwk Nat.succ) := rfl

theorem wappend_nil (r : Region φ) : r.wappend nil = cfg r 1 (λ_ => br 1 (Term.var 0)) := rfl

theorem nil_wappend (r : Region φ) : nil.wappend r = cfg nil 1 (λ_ => r.lwk Nat.succ) := rfl

def Subst.left_label_distrib (e : Term φ) : Subst φ
  := λℓ => br ℓ (Term.pair (e.wk Nat.succ) (Term.var 0))

def Subst.right_label_distrib (e : Term φ) : Subst φ
  := λℓ => br ℓ (Term.pair (Term.var 0) (e.wk Nat.succ))

def left_label_distrib (r : Region φ) (e : Term φ) : Region φ
  := r.lsubst (Subst.left_label_distrib e)

def right_label_distrib (r : Region φ) (e : Term φ) : Region φ
  := r.lsubst (Subst.right_label_distrib e)

def left_distrib (r : Region φ) : Region φ
  := ((r.vwk Nat.succ).left_label_distrib (Term.var 0)).let2 (Term.var 0)

def right_distrib (r : Region φ) : Region φ
  := ((r.vwk (Nat.liftWk Nat.succ)).right_label_distrib (Term.var 1)).let2 (Term.var 0)

-- TODO: label threading vs. distribution, equal if fvi ≤ 1

def associator : Region φ :=
  let2 (Term.var 0) $
  let2 (Term.var 0) $
  ret (Term.pair (Term.var 0) (Term.pair (Term.var 1) (Term.var 2)))

def associator_inv : Region φ :=
  let2 (Term.var 0) $
  let2 (Term.var 1) $
  ret (Term.pair (Term.pair (Term.var 2) (Term.var 0)) (Term.var 1))

theorem associator_append_associator_inv_def
  : @associator φ ++ associator_inv = (let2 (Term.var 0) $
    let2 (Term.var 0) $
    let2 (Term.pair (Term.var 0) (Term.pair (Term.var 1) (Term.var 2))) $
    let2 (Term.var 1) $
    ret (Term.pair (Term.pair (Term.var 2) (Term.var 0)) (Term.var 1)))
  := rfl

def RWD.assocatior_append_associator_inv {Γ : ℕ → ε}
  : RWD (PStepD Γ) (@associator φ ++ associator_inv) nil
  := by
  rw [associator_append_associator_inv_def]
  sorry

def RWD.associator_inv_append_associator {Γ : ℕ → ε}
  : RWD (PStepD Γ) (@associator_inv φ ++ associator) nil
  := sorry

def proj_left : Region φ :=
  let2 (Term.var 0) $
  ret (Term.var 0)

def proj_right : Region φ :=
  let2 (Term.var 0) $
  ret (Term.var 1)

def left_unitor_inv : Region φ := ret (Term.pair Term.unit (Term.var 0))

def right_unitor_inv : Region φ := ret (Term.pair (Term.var 0) Term.unit)

def inl : Region φ := ret (Term.var 0).inl

def inr : Region φ := ret (Term.var 0).inr

def swap : Region φ :=
  let2 (Term.var 0) $
  ret (Term.pair (Term.var 1) (Term.var 0))

def let_eta : Region φ :=
  let1 (Term.var 0) $
  ret (Term.var 0)

def let2_eta : Region φ :=
  let2 (Term.var 0) $
  ret (Term.pair (Term.var 0) (Term.var 1))

def case_eta : Region φ := case (Term.var 0) (ret (Term.var 0).inl) (ret (Term.var 0).inr)

def drop : Region φ :=
  let1 (Term.var 0) $
  ret Term.unit

def join (r r' : Region φ) : Region φ := case (Term.var 0)
  (r.vwk (Nat.liftWk Nat.succ))
  (r'.lwk (Nat.liftWk Nat.succ))

def abort : Region φ := ret (Term.var 0).abort

def left_distributor : Region φ :=
  case (Term.var 0)
    (ret (Term.pair (Term.var 0) (Term.var 2).inl))
    (ret (Term.pair (Term.var 0) (Term.var 2).inr))

def left_distributor_inv : Region φ :=
  let2 (Term.var 0) $
  case (Term.var 1)
    (ret (Term.pair (Term.var 0) (Term.var 1)))
    (ret (Term.pair (Term.var 0) (Term.var 1)))

def right_distributor : Region φ :=
  case (Term.var 0)
    (ret (Term.pair (Term.var 2).inl (Term.var 0)))
    (ret (Term.pair (Term.var 2).inr (Term.var 0)))

def right_distributor_inv : Region φ :=
  let2 (Term.var 0) $
  case (Term.var 0)
    (ret (Term.pair (Term.var 2) (Term.var 0)))
    (ret (Term.pair (Term.var 2) (Term.var 0)))

def swap_sum : Region φ := case (Term.var 0) (ret (Term.var 0).inr) (ret (Term.var 0).inl)

def right_exit : Region φ :=
  case (Term.var 0)
    (br 0 (Term.var 0))
    (br 1 (Term.var 0))

def left_exit : Region φ :=
  case (Term.var 0)
    (br 1 (Term.var 0))
    (br 0 (Term.var 0))

def fixpoint (r : Region φ) : Region φ := cfg nil 1 (λ_ => r ++ left_exit)

def ite (b : Term φ) (r r' : Region φ) : Region φ := case b (r.vwk Nat.succ) (r'.vwk Nat.succ)

end Region

end BinSyntax
