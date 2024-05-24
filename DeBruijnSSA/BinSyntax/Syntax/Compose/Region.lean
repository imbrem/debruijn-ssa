import DeBruijnSSA.BinSyntax.Syntax.Subst

namespace BinSyntax

namespace Region

def lsubst0 (r : Region φ) : Subst φ
  | 0 => r
  | ℓ + 1 => br ℓ (Term.var 0)

def alpha (ℓ : ℕ) (r : Region φ) : Subst φ
  := Function.update Subst.id ℓ r

def ret (e : Term φ) := br 0 e

def nil : Region φ := ret (Term.var 0)

@[simp]
def alpha0_nil : alpha 0 nil = @Subst.id φ := by
  rw [alpha, Function.update_eq_self_iff]
  rfl

def append (r r' : Region φ) : Region φ := r.lsubst (r'.alpha 0).vlift

instance : Append (Region φ) := ⟨Region.append⟩

theorem append_def (r r' : Region φ) : r ++ r' = r.lsubst (r'.alpha 0).vlift := rfl

@[simp]
theorem append_nil (r : Region φ) : r ++ nil = r := by simp [append_def]

@[simp]
theorem nil_append (r : Region φ) : nil ++ r = r := by
  simp only [append_def, lsubst, Subst.vlift, alpha, Function.comp_apply, Function.update_same]
  rw [<-vsubst_fromWk_apply, <-vsubst_comp_apply, <-vsubst_id r]
  congr <;> simp

-- TODO: ret append ret should be alpha0 or smt...

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
    Subst.comp, Subst.vlift, alpha, Function.comp_apply, Function.comp_update,
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

def case_eta : Region φ := case (Term.var 0) (ret (Term.var 0)) (ret (Term.var 0))

def drop : Region φ :=
  let1 (Term.var 0) $
  ret Term.unit

def join (r r' : Region φ) : Region φ := case (Term.var 0)
  (r.vwk (Nat.liftWk Nat.succ))
  (r'.lwk (Nat.liftWk Nat.succ))

def abort : Region φ := ret (Term.var 0).abort

def left_distributor : Region φ :=
  let2 (Term.var 0) $
  case (Term.var 1)
    (ret (Term.pair (Term.var 0) (Term.var 1)))
    (ret (Term.pair (Term.var 0) (Term.var 1)))

def right_distributor : Region φ :=
  let2 (Term.var 0) $
  case (Term.var 0)
    (ret (Term.pair (Term.var 2) (Term.var 0)))
    (ret (Term.pair (Term.var 2) (Term.var 0)))

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

def wappend (r r' : Region φ) : Region φ := cfg r 1 (λ_ => r'.lwk Nat.succ)

end Region

end BinSyntax
