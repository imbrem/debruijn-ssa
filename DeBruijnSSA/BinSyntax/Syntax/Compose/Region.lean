import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.InstSet

namespace BinSyntax

namespace Region

variable {φ : Type u} {ε : Type v} [Φ: EffectSet φ ε] [SemilatticeSup ε] [OrderBot ε]

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

theorem vliftn_alpha (n m : ℕ) (r : Region φ)
  : (alpha n r).vliftn m = alpha n (r.vwk (Nat.liftWk (· + m))) := by
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

theorem vsubst_lift_alpha {ρ : Term.Subst φ} (n : ℕ) (r : Region φ)
  : vsubst ρ.lift ∘ (alpha n r) = alpha n (r.vsubst ρ.lift) := by
  simp [alpha, Function.comp_update]

def seq (r r' : Region φ) : Region φ := r.lsubst (r'.vwk1.alpha 0)

instance : Append (Region φ) := ⟨Region.seq⟩

theorem append_def (r r' : Region φ) : r ++ r' = r.lsubst (r'.vwk1.alpha 0) := rfl

@[simp]
theorem append_nil (r : Region φ) : r ++ nil = r := by simp [append_def]

@[simp]
theorem nil_append (r : Region φ) : nil ++ r = r := by
  simp only [
    append_def, lsubst, Subst.vlift, vwk1, alpha, Function.comp_apply, Function.update_same]
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

theorem let2_append (e : Term φ) (r r' : Region φ)
  : r.let2 e ++ r' = (r ++ (r'.vwk (Nat.liftWk (· + 2)))).let2 e
  := by
  simp only [append_def, lsubst, vlift_alpha, vliftn_alpha, vwk_vwk, vwk1, ← Nat.liftWk_comp]
  rfl

theorem lsubst_alpha_case (k) (e : Term φ) (s t r : Region φ)
  : (case e s t).lsubst (r.alpha k)
  = (case e (s.lsubst (r.vwk1.alpha k)) (t.lsubst (r.vwk1.alpha k)))
  := by
  simp only [append_def, lsubst, vlift_alpha, vwk_vwk, vwk1, ← Nat.liftWk_comp]

theorem case_append (e : Term φ) (s t r : Region φ)
  : case e s t ++ r = case e (s ++ r.vwk1) (t ++ r.vwk1)
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

theorem vsubst_lift_lsubst_alpha {ρ : Term.Subst φ}
  : (lsubst (alpha n r₁) r₀).vsubst ρ.lift
  = lsubst (alpha n (r₁.vsubst (ρ.liftn 2))) (r₀.vsubst ρ.lift)
  := by simp [vsubst_lsubst, vsubst_lift_alpha, Term.Subst.liftn_eq_iterate_lift]

theorem vsubst_lift_lsubst_alpha_vwk1 {r₀ r₁ : Region φ} {ρ : Term.Subst φ}
  : (lsubst (alpha n r₁.vwk1) r₀).vsubst ρ.lift
  = lsubst (alpha n ((r₁.vsubst ρ.lift).vwk1)) (r₀.vsubst ρ.lift) := by
  rw [vsubst_lift_lsubst_alpha]
  congr
  apply congrArg
  simp only [vwk1, ← vsubst_fromWk, vsubst_vsubst]
  congr
  funext k
  cases k with
  | zero => rfl
  | succ k => simp [Term.Subst.comp, Term.subst_fromWk, Term.wk_wk, Term.Subst.liftn]

theorem vwk_lift_append {r₀ r₁ : Region φ}
  : (r₀ ++ r₁).vwk (Nat.liftWk ρ)
  = r₀.vwk (Nat.liftWk ρ) ++ r₁.vwk (Nat.liftWk ρ) := by
  simp only [append_def, vwk_liftWk_lsubst_alpha_vwk1]

theorem vsubst_lift_append {r₀ r₁ : Region φ} {ρ : Term.Subst φ}
  : (r₀ ++ r₁).vsubst ρ.lift
  = r₀.vsubst ρ.lift ++ r₁.vsubst ρ.lift := by
  simp only [append_def, vsubst_lift_lsubst_alpha_vwk1]

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

def lseq (r r' : Region φ) : Region φ := r ++ r'.let1V0

instance : ShiftRight (Region φ) := ⟨Region.lseq⟩

theorem lseq_def (r r' : Region φ) : r >>> r' = r ++ r'.let1V0 := rfl

theorem lseq_nil (r : Region φ) : r >>> nil = r ++ nil.let1V0 := rfl

theorem nil_lseq (r : Region φ) : nil >>> r = r.let1V0 := nil_append _

def wseq (r r' : Region φ) : Region φ := cfg r.lwk1 1 (Fin.elim1 r'.lwk0.vwk1)

def wrseq (r r' : Region φ) : Region φ := cfg r.lwk1 1 (Fin.elim1 r'.lwk0)

def wthen (r r' : Region φ) : Region φ := cfg r 1 (Fin.elim1 r'.lwk0)

theorem wseq_eq_wrseq (r r' : Region φ) : r.wseq r' = r.wrseq r'.vwk1
  := by rw [wseq, wrseq, vwk1_lwk0]

theorem wseq_eq_wthen (r r' : Region φ) : r.wseq r' = r.lwk1.wthen r'.vwk1
  := by rw [wseq, wthen, vwk1_lwk0]

theorem wrseq_eq_wthen (r r' : Region φ) : r.wrseq r' = r.lwk1.wthen r'
  := rfl

theorem vwk_wrseq (r r' : Region φ)
  : (r.wrseq r').vwk ρ = (r.vwk ρ).wrseq (r'.vwk (Nat.liftWk ρ)) := by
  simp only [wrseq, vwk]
  congr
  rw [lwk1, vwk_lwk]
  funext i; cases i using Fin.elim1
  simp only [vwk1, lwk0, vwk_lwk, Fin.elim1_zero, vwk_vwk]

theorem vwk_wthen (r r' : Region φ)
  : (r.wthen r').vwk ρ = (r.vwk ρ).wthen (r'.vwk (Nat.liftWk ρ)) := by
  simp only [wthen, vwk]
  congr
  funext i; cases i using Fin.elim1
  simp only [vwk1, lwk0, vwk_lwk, Fin.elim1_zero, vwk_vwk]

theorem lwk_wthen (r r' : Region φ)
  : (r.wthen r').lwk ρ = (r.lwk (Nat.liftWk ρ)).wthen (r'.lwk ρ) := by
  simp only [wthen, lwk, Nat.liftnWk_one]
  congr
  funext i; cases i using Fin.elim1
  simp only [lwk0, lwk_lwk, Fin.elim1_zero]
  rfl

theorem lwk_lift_wrseq (r r' : Region φ)
  : (r.wrseq r').lwk (Nat.liftWk ρ) = (r.lwk (Nat.liftWk ρ)).wrseq (r'.lwk (Nat.liftWk ρ)) := by
  simp only [wrseq, lwk, Nat.liftnWk_one, lwk1, lwk0, lwk_lwk]
  congr
  funext k; cases k <;> rfl
  funext i; cases i using Fin.elim1
  simp only [Fin.elim1_zero, lwk_lwk]
  rfl

theorem vwk_lift_wseq (r r' : Region φ)
  : (r.wseq r').vwk (Nat.liftWk ρ) = (r.vwk (Nat.liftWk ρ)).wseq (r'.vwk (Nat.liftWk ρ)) := by
  simp only [wseq_eq_wrseq, vwk_wrseq, vwk1, vwk_vwk]
  congr
  funext k; cases k <;> rfl

theorem lwk_lift_wseq (r r' : Region φ)
  : (r.wseq r').lwk (Nat.liftWk ρ) = (r.lwk (Nat.liftWk ρ)).wseq (r'.lwk (Nat.liftWk ρ)) := by
  simp only [wseq_eq_wrseq, lwk_lift_wrseq, vwk1, lwk_vwk]

-- def Subst.left_label_distrib (e : Term φ) : Subst φ
--   := λℓ => br ℓ (Term.pair (e.wk Nat.succ) (Term.var 0))

-- def Subst.right_label_distrib (e : Term φ) : Subst φ
--   := λℓ => br ℓ (Term.pair (Term.var 0) (e.wk Nat.succ))

-- def left_label_distrib (r : Region φ) (e : Term φ) : Region φ
--   := r.lsubst (Subst.left_label_distrib e)

-- def right_label_distrib (r : Region φ) (e : Term φ) : Region φ
--   := r.lsubst (Subst.right_label_distrib e)

-- def left_distrib (r : Region φ) : Region φ
--   := ((r.vwk Nat.succ).left_label_distrib (Term.var 0)).let2 (Term.var 0)

-- def right_distrib (r : Region φ) : Region φ
--   := ((r.vwk (Nat.liftWk Nat.succ)).right_label_distrib (Term.var 1)).let2 (Term.var 0)

-- -- TODO: label threading vs. distribution, equal if fvi ≤ 1

-- def associator : Region φ :=
--   let2 (Term.var 0) $
--   let2 (Term.var 1) $
--   ret (Term.pair (Term.var 1) (Term.pair (Term.var 0) (Term.var 2)))

-- def associator_inv : Region φ :=
--   let2 (Term.var 0) $
--   let2 (Term.var 0) $
--   ret (Term.pair (Term.pair (Term.var 3) (Term.var 1)) (Term.var 0))

-- def repack_left : Region φ :=
--   let2 (Term.var 0) $
--   let2 (Term.var 1) $
--   ret (Term.pair (Term.pair (Term.var 1) (Term.var 0)) (Term.var 2))

-- def repack_right : Region φ :=
--   let2 (Term.var 0) $
--   let2 (Term.var 0) $
--   ret (Term.pair (Term.var 3) (Term.pair (Term.var 1) (Term.var 0)))

-- theorem associator_append_associator_inv_def
--   : @associator φ ++ associator_inv = (let2 (Term.var 0) $
--     let2 (Term.var 1) $
--     let2 (Term.pair (Term.var 1) (Term.pair (Term.var 0) (Term.var 2))) $
--     let2 (Term.var 0) $
--     ret (Term.pair (Term.pair (Term.var 3) (Term.var 1)) (Term.var 0)))
--   := rfl

def proj_left : Region φ :=
  let2 (Term.var 0) $
  ret (Term.var 0)

def proj_right : Region φ :=
  let2 (Term.var 0) $
  ret (Term.var 1)

def left_unitor_inv : Region φ := ret (Term.pair Term.unit (Term.var 0))

def right_unitor_inv : Region φ := ret (Term.pair (Term.var 0) Term.unit)

def inj_l : Region φ := ret (Term.var 0).inl

def inj_r : Region φ := ret (Term.var 0).inr

def swap : Region φ :=
  ret (Term.let2 (Term.var 0) $ Term.pair (Term.var 1) (Term.var 0))

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

def zero : Region φ := ret (Term.var 0).abort

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

def left_exit : Region φ :=
  case (Term.var 0)
    (br 1 (Term.var 0))
    (br 0 (Term.var 0))

def right_exit : Region φ :=
  case (Term.var 0)
    (br 0 (Term.var 0))
    (br 1 (Term.var 0))

def fixpoint (r : Region φ) : Region φ := cfg nil 1 (Fin.elim1 (r.vwk1.lwk1 ++ left_exit))

theorem vwk_lift_fixpoint (r : Region φ)
  : r.fixpoint.vwk (Nat.liftWk ρ) = (r.vwk $ Nat.liftWk ρ).fixpoint := by
  simp only [fixpoint, vwk]
  congr
  funext i
  cases i using Fin.elim1 with
  | zero =>
    rw [Fin.elim1_zero, vwk_lift_append, vwk_lwk1, vwk_liftWk₂_vwk1]
    rfl

theorem vsubst_lift_fixpoint (r : Region φ) {ρ : Term.Subst φ}
  : r.fixpoint.vsubst ρ.lift = (r.vsubst ρ.lift).fixpoint := by
  simp only [fixpoint, vsubst]
  congr
  funext i
  cases i using Fin.elim1 with
  | zero =>
    rw [Fin.elim1_zero, vsubst_lift_append, vsubst_lwk1, vsubst_lift₂_vwk1]
    rfl

def ite (b : Term φ) (r r' : Region φ) : Region φ := case b (r.vwk Nat.succ) (r'.vwk Nat.succ)

-- end Region

-- end BinSyntax
