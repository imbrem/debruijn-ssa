import DeBruijnSSA.BinSyntax.Rewrite.Region.LSubst
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Seq
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Product
import DeBruijnSSA.BinSyntax.Typing.Region.Compose

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

open Term.Eqv

def Eqv.rtimes {tyIn tyOut : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (tyLeft : Ty α) (r : Eqv φ (⟨tyIn, ⊥⟩::Γ) (tyOut::L))
  : Eqv φ (⟨tyLeft.prod tyIn, ⊥⟩::Γ) ((tyLeft.prod tyOut)::L)
  := Eqv.let2 (var 0 Ctx.Var.shead) $
  r.vwk1.vwk1 ;;
  ret (pair (var 1 (by simp)) (var 0 (by simp)))

infixl:70 " ⋊ "  => Eqv.rtimes

theorem Eqv.rtimes_eq_ret {tyIn tyOut : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {tyLeft : Ty α} {r : Term.Eqv φ (⟨tyIn, ⊥⟩::Γ) ⟨tyOut, ⊥⟩}
  : tyLeft ⋊ ret r = Eqv.ret (targets := L) (r.rtimes tyLeft) := by
  simp only [Eqv.rtimes, vwk1_ret, ret_ret, let2_ret, Term.Eqv.rtimes_def']
  rfl

theorem Eqv.vwk_lift_rtimes {A B : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨A, ⊥⟩::Δ) (B::L)} {ρ : Γ.InS Δ}
  : (X ⋊ r).vwk (ρ.lift (le_refl _)) = X ⋊ (r.vwk (ρ.lift (le_refl _))) := by
  rw [rtimes, vwk_let2, <-Ctx.InS.lift_lift, vwk_lift_seq]
  congr 2
  simp only [vwk1, vwk_vwk]
  congr 1
  ext k
  cases k <;> rfl

theorem Eqv.vwk1_rtimes {tyIn tyOut : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨tyIn, ⊥⟩::Γ) (tyOut::L)}
  : (X ⋊ r).vwk1 (inserted := inserted) = X ⋊ r.vwk1 := by
  simp only [vwk1, <-Ctx.InS.lift_wk0, vwk_lift_rtimes]

theorem Eqv.Pure.rtimes {tyIn tyOut : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (tyLeft : Ty α) {r : Eqv φ (⟨tyIn, ⊥⟩::Γ) (tyOut::L)}
  (hp : Eqv.Pure r) : Eqv.Pure (tyLeft ⋊ r) := let ⟨_, hp⟩ := hp; ⟨_, hp ▸ rtimes_eq_ret⟩

def Eqv.braid {left right : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨left.prod right, ⊥⟩::Γ) ((right.prod left)::L)
  := Eqv.let2 (var 0 Ctx.Var.shead) $
  ret (pair (var 0 (by simp)) (var 1 (by simp)))

theorem Eqv.braid_eq_ret {left right : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.braid (φ := φ) (left := left) (right := right) (Γ := Γ) (L := L) = Eqv.ret Term.Eqv.braid
  := by
  simp only [Eqv.braid, let2_ret]
  rfl

@[simp]
theorem Eqv.vwk1_braid {left right : Ty α} {Γ : Ctx α ε} {L : LCtx α} :
  (Eqv.braid (φ := φ) (left := left) (right := right) (Γ := Γ) (L := L)).vwk1 (inserted := inserted)
  = Eqv.braid := rfl

theorem Eqv.Pure.braid {left right : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.Pure (Eqv.braid (φ := φ) (left := left) (right := right) (Γ := Γ) (L := L))
  := ⟨_, braid_eq_ret⟩

theorem Eqv.repack {left right : Ty α} {rest : Ctx α ε} {targets : LCtx α}
  : Eqv.let2 (var 0 ⟨by simp, le_refl _⟩)
    (Eqv.ret (pair (var 1 (by simp)) (var 0 (by simp))))
  = Eqv.nil (φ := φ) (ty := left.prod right) (rest := rest) (targets := targets) := by
  rw [<-let1_0_nil, <-let2_eta, let1_beta]
  rfl

theorem Eqv.braid_braid {left right : Ty α}
  : Eqv.braid ;; Eqv.braid
  = (Eqv.nil (φ := φ) (ty := left.prod right) (rest := rest) (targets := targets)) := by
  simp only [braid_eq_ret, ret_ret, Term.Eqv.braid_braid, ret_nil]

theorem Eqv.rtimes_nil {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (tyLeft : Ty α)
  : tyLeft ⋊ Eqv.nil = (Eqv.nil (φ := φ) (ty := tyLeft.prod ty) (rest := Γ) (targets := L)) := by
  simp only [rtimes, nil_vwk1, nil_seq, repack]

-- theorem Eqv.ret_pair_rtimes {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α} {tyLeft : Ty α}
--   {l : Term.Eqv φ ((X, ⊥)::Γ) (tyLeft, ⊥)} {a : Term.Eqv φ ((X, ⊥)::Γ) (A, ⊥)}
--   {r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)}
--   : ret (l.pair a) ;; tyLeft ⋊ r = sorry
--   := sorry

theorem Eqv.rtimes_rtimes {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (tyLeft : Ty α) (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (s : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : (tyLeft ⋊ r) ;; (tyLeft ⋊ s) = tyLeft ⋊ (r ;; s) := by
  apply Eq.symm
  rw [rtimes, rtimes, let2_seq]
  congr 1
  simp only [vwk1_rtimes, seq_assoc, vwk1_seq, ret_seq]
  congr 1
  simp [rtimes, vsubst_let2, let2_pair, let1_beta, vsubst_vsubst]
  induction r using Quotient.inductionOn
  induction s using Quotient.inductionOn
  apply Eqv.eq_of_reg_eq
  simp only [Set.mem_setOf_eq, InS.vwk_br, Term.InS.wk_pair, Term.InS.wk_var, Ctx.InS.coe_wk1,
    Nat.liftWk_succ, Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, Nat.liftWk_zero, InS.coe_lsubst,
    InS.coe_alpha0, InS.coe_br, Term.InS.coe_pair, Term.InS.coe_var, InS.coe_vwk, Region.vwk_vwk,
    InS.coe_vsubst, Term.Subst.InS.coe_comp, Term.InS.coe_subst0, Term.Subst.InS.coe_liftn₂,
    Region.vsubst_lsubst]
  congr
  · funext k
    cases k <;> rfl
  · simp only [<-Region.vsubst_fromWk, Region.vsubst_vsubst]
    congr
    funext k
    cases k <;> rfl

def Eqv.ret_seq_rtimes {tyLeft tyIn tyOut : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (e : Term.Eqv φ ((tyIn', _)::Γ) ((tyLeft.prod tyIn), ⊥)) (r : Eqv φ (⟨tyIn, ⊥⟩::Γ) (tyOut::L))
  : ret e ;; tyLeft ⋊ r = (Eqv.let2 e $
    r.vwk1.vwk1 ;;
    ret (pair (var 1 (by simp)) (var 0 (by simp)))) := by
    rw [ret_seq, rtimes, vwk1]
    simp only [vwk_let2, wk_var, Set.mem_setOf_eq, Ctx.InS.coe_wk1, Nat.liftWk_zero, vwk_liftn₂_seq,
      vwk_ret, wk_pair, Ctx.InS.coe_liftn₂, Nat.liftnWk, Nat.one_lt_ofNat, ↓reduceIte,
      Nat.ofNat_pos, vsubst_let2, var0_subst0, List.length_cons, id_eq, Fin.zero_eta,
      List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, wk_res_self, vsubst_liftn₂_seq,
      vsubst_br, subst_pair, subst_liftn₂_var_one, ge_iff_le, le_refl, subst_liftn₂_var_zero]
    congr
    induction r using Quotient.inductionOn
    induction e using Quotient.inductionOn
    apply Eqv.eq_of_reg_eq
    simp only [Set.mem_setOf_eq, InS.coe_vsubst, Term.Subst.InS.coe_liftn₂, Term.InS.coe_subst0,
      InS.coe_vwk, Ctx.InS.coe_liftn₂, Ctx.InS.coe_wk1, Region.vwk_vwk]
    simp only [<-Region.vsubst_fromWk, Region.vsubst_vsubst]
    congr
    funext k; cases k <;> rfl

-- TODO: proper ltimes?
def Eqv.ltimes {tyIn tyOut : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨tyIn, ⊥⟩::Γ) (tyOut::L)) (tyRight : Ty α)
  : Eqv φ (⟨tyIn.prod tyRight, ⊥⟩::Γ) ((tyOut.prod tyRight)::L)
  := Eqv.braid ;; tyRight ⋊ r ;; Eqv.braid

infixl:70 " ⋉ "  => Eqv.ltimes

theorem Eqv.vwk1_ltimes {tyIn tyOut : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨tyIn, ⊥⟩::Γ) (tyOut::L)} {tyRight : Ty α}
  : (r ⋉ tyRight).vwk1 (inserted := inserted) = r.vwk1 ⋉ tyRight := by
  simp only [ltimes, vwk1_seq, vwk1_braid, vwk1_rtimes]

theorem Eqv.ltimes_eq_ret {tyIn tyOut : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {tyRight : Ty α} {r : Term.Eqv φ (⟨tyIn, ⊥⟩::Γ) ⟨tyOut, ⊥⟩}
  : ret (targets := L) r ⋉ tyRight = ret (r.ltimes tyRight) := by
  simp only [ltimes, braid_eq_ret, rtimes_eq_ret, ret_ret, Term.Eqv.braid_rtimes_braid]

theorem Eqv.Pure.ltimes {tyIn tyOut : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨tyIn, ⊥⟩::Γ) (tyOut::L)} (hr : r.Pure) (tyRight : Ty α)
  : Pure (r ⋉ tyRight) := seq (seq braid (hr.rtimes _)) braid

theorem Eqv.braid_rtimes_braid {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : Eqv.braid ;; C ⋊ r ;; Eqv.braid = r ⋉ C
  := rfl

theorem Eqv.braid_ltimes {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : Eqv.braid ;; r ⋉ C = C ⋊ r ;; Eqv.braid
  := by rw [<-braid_rtimes_braid, <-seq_assoc, <-seq_assoc, braid_braid, nil_seq]

theorem Eqv.braid_ltimes_braid {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : Eqv.braid ;; r ⋉ C ;; Eqv.braid = C ⋊ r
  := by rw [
    ltimes, seq_assoc, seq_assoc, braid_braid, seq_assoc, seq_nil, <-seq_assoc, braid_braid, nil_seq]

theorem Eqv.braid_rtimes {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : Eqv.braid ;; C ⋊ r = r ⋉ C ;; Eqv.braid
  := by rw [<-braid_ltimes_braid, <-seq_assoc, <-seq_assoc, braid_braid, nil_seq]

theorem Eqv.ltimes_nil {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.nil ⋉ tyRight = (Eqv.nil (φ := φ) (ty := ty.prod tyRight) (rest := Γ) (targets := L))
  := by rw [<-braid_rtimes_braid, rtimes_nil, seq_nil, braid_braid]

theorem Eqv.ltimes_ltimes {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (s : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : (r ⋉ tyRight) ;; (s ⋉ tyRight) = (r ;; s) ⋉ tyRight := by
  simp only [<-braid_rtimes_braid, <-rtimes_rtimes, seq_assoc]
  rw [<-seq_assoc braid braid, braid_braid, nil_seq]

def Eqv.pi_l {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨A.prod B, ⊥⟩::Γ) (A::L)
  := let2 (var 0 Ctx.Var.shead) (ret $ var 1 (by simp))

def Eqv.runit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨ty, ⊥⟩::Γ) (ty.prod Ty.unit::L)
  := ret $ (pair (var 0 Ctx.Var.shead) (unit _))

theorem Eqv.pi_l_eq_ret {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.pi_l (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L) = Eqv.ret Term.Eqv.pi_l := by
  simp only [Eqv.pi_l, let2_ret]
  rfl

theorem Eqv.runit_eq_ret {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.runit (φ := φ) (ty := ty) (Γ := Γ) (L := L) = Eqv.ret Term.Eqv.runit := by
  simp only [Eqv.runit, ret_ret]
  rfl

@[simp]
theorem Eqv.vwk1_pi_l {Γ : Ctx α ε} {L : LCtx α}
  : (pi_l (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L)).vwk1 (inserted := inserted) = pi_l := rfl

@[simp]
theorem Eqv.vwk2_pi_l {Γ : Ctx α ε} {L : LCtx α}
  : (pi_l (φ := φ) (A := A) (B := B) (Γ := V::Γ) (L := L)).vwk2 (inserted := inserted) = pi_l := rfl

@[simp]
theorem Eqv.vwk_lift_pi_l {Γ Δ : Ctx α ε} {L : LCtx α} {ρ : Ctx.InS Γ Δ}
  : (pi_l (φ := φ) (A := A) (B := B) (L := L)).vwk (ρ.lift (le_refl _)) = pi_l := rfl

@[simp]
theorem Eqv.vsubst_lift_pi_l {Γ Δ : Ctx α ε} {L : LCtx α} {ρ : Term.Subst.Eqv φ Γ Δ}
  : (pi_l (φ := φ) (A := A) (B := B) (L := L)).vsubst (ρ.lift (le_refl _)) = pi_l := by
  induction ρ using Quotient.inductionOn; rfl

theorem Eqv.ret_pair_pi_l {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
  {a : Term.Eqv φ ((X, ⊥)::Γ) (A, ⊥)} {b : Term.Eqv φ ((X, ⊥)::Γ) (B, ⊥)}
  : ret (targets := L) (a.pair b) ;; pi_l = ret a
  := by simp [ret, pi_l, ret_seq, vwk1, vwk_ret, Nat.liftnWk, let2_pair, let1_beta]

@[simp]
theorem Eqv.Pure.pi_l {Γ : Ctx α ε} {L : LCtx α}
  : (pi_l (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L)).Pure := ⟨_, pi_l_eq_ret⟩

theorem Eqv.Pure.runit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (runit (φ := φ) (ty := ty) (Γ := Γ) (L := L)).Pure := ⟨_, runit_eq_ret⟩

theorem Eqv.pi_l_runit_helper {Γ : Ctx α ε} {L : LCtx α}
  : pi_l (φ := φ) (A := A) (B := Ty.unit) (Γ := Γ) (L := L) ;; runit
  = let2 (var 0 ⟨by simp, le_refl _⟩)
    (let1 (unit ⊥) (ret $ pair (var 2 (by simp)) (var 0 (by simp)))) := by
  rw [let1_beta]
  rfl

theorem Eqv.pi_l_runit {Γ : Ctx α ε} {L : LCtx α}
  : pi_l (φ := φ) (A := A) (B := Ty.unit) (Γ := Γ) (L := L) ;; runit = nil := by
  rw [pi_l_runit_helper, terminal _ (var 0 (by simp)), let1_beta]
  apply repack

theorem Eqv.runit_pi_l {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : runit (φ := φ) (ty := ty) (Γ := Γ) (L := L) ;; pi_l = nil := by
  simp only [runit_eq_ret, pi_l_eq_ret, ret_ret, Term.Eqv.runit_pi_l, ret_nil]

def Eqv.pi_r {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨A.prod B, ⊥⟩::Γ) (B::L)
  := let2 (var 0 Ctx.Var.shead) (ret $ var 0 (by simp))

def Eqv.lunit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨ty, ⊥⟩::Γ) (Ty.unit.prod ty::L)
  := ret $ (pair (unit _) (var 0 Ctx.Var.shead))

theorem Eqv.pi_r_eq_ret {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.pi_r (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L) = Eqv.ret Term.Eqv.pi_r := by
  simp only [Eqv.pi_r, let2_ret]
  rfl

theorem Eqv.lunit_eq_ret {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.lunit (φ := φ) (ty := ty) (Γ := Γ) (L := L) = Eqv.ret Term.Eqv.lunit := by
  simp only [Eqv.lunit, ret_ret]
  rfl

@[simp]
theorem Eqv.vwk1_pi_r {Γ : Ctx α ε} {L : LCtx α}
  : (pi_r (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L)).vwk1 (inserted := inserted) = pi_r := rfl

@[simp]
theorem Eqv.vwk2_pi_r {Γ : Ctx α ε} {L : LCtx α}
  : (pi_r (φ := φ) (A := A) (B := B) (Γ := V::Γ) (L := L)).vwk2 (inserted := inserted) = pi_r := rfl

@[simp]
theorem Eqv.vwk_lift_pi_r {Γ Δ : Ctx α ε} {L : LCtx α} {ρ : Ctx.InS Γ Δ}
  : (pi_r (φ := φ) (A := A) (B := B) (L := L)).vwk (ρ.lift (le_refl _)) = pi_r := rfl

@[simp]
theorem Eqv.vsubst_lift_pi_r {Γ Δ : Ctx α ε} {L : LCtx α} {ρ : Term.Subst.Eqv φ Γ Δ}
  : (pi_r (φ := φ) (A := A) (B := B) (L := L)).vsubst (ρ.lift (le_refl _)) = pi_r := by
  induction ρ using Quotient.inductionOn; rfl

theorem Eqv.ret_pair_pi_r {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
  {a : Term.Eqv φ ((X, ⊥)::Γ) (A, ⊥)} {b : Term.Eqv φ ((X, ⊥)::Γ) (B, ⊥)}
  : ret (targets := L) (a.pair b) ;; pi_r = ret b
  := by
  simp only [pi_r, ret_seq, vwk1, vwk_let2, wk_var, Set.mem_setOf_eq, Ctx.InS.coe_wk1,
    Nat.liftWk_zero, vwk_ret, Ctx.InS.coe_liftn₂, Nat.liftnWk, Nat.ofNat_pos, ↓reduceIte,
    vsubst_let2, var0_subst0, List.length_cons, id_eq, Fin.zero_eta, List.get_eq_getElem,
    Fin.val_zero, List.getElem_cons_zero, wk_res_self, vsubst_br, ge_iff_le, le_refl,
    subst_liftn₂_var_zero, let2_pair, let1_beta, ret]
  congr
  exact subst0_wk0

@[simp]
theorem Eqv.Pure.pi_r {Γ : Ctx α ε} {L : LCtx α}
  : (pi_r (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L)).Pure := ⟨_, pi_r_eq_ret⟩

theorem Eqv.Pure.lunit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (lunit (φ := φ) (ty := ty) (Γ := Γ) (L := L)).Pure := ⟨_, lunit_eq_ret⟩

theorem Eqv.pi_r_lunit {Γ : Ctx α ε} {L : LCtx α}
  : pi_r (φ := φ) (A := Ty.unit) (B := B) (Γ := Γ) (L := L) ;; lunit = nil
  := by simp only [pi_r_eq_ret, lunit_eq_ret, ret_ret, Term.Eqv.pi_r_lunit, ret_nil]

theorem Eqv.lunit_pi_r {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : lunit (φ := φ) (ty := ty) (Γ := Γ) (L := L) ;; pi_r = nil
  := by simp only [pi_r_eq_ret, lunit_eq_ret, ret_ret, Term.Eqv.lunit_pi_r, ret_nil]

theorem Eqv.ret_pair_braid {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
  {a : Term.Eqv φ ((X, ⊥)::Γ) (A, ⊥)} {b : Term.Eqv φ ((X, ⊥)::Γ) (B, ⊥)}
  : ret (targets := L) (a.pair b) ;; braid = ret (pair b a) := by
  simp only [braid, ret_seq, vwk1, vwk_let2, wk_var, Set.mem_setOf_eq, Ctx.InS.coe_wk1,
    Nat.liftWk_zero, vwk_ret, wk_pair, Ctx.InS.coe_liftn₂, Nat.liftnWk, Nat.ofNat_pos, ↓reduceIte,
    Nat.one_lt_ofNat, vsubst_let2, var0_subst0, List.length_cons, id_eq, Fin.zero_eta,
    List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, wk_res_self, vsubst_br, subst_pair,
    ge_iff_le, le_refl, subst_liftn₂_var_zero, subst_liftn₂_var_one, let2_pair, let1_beta,
    var_succ_subst0, ↓dreduceIte, Nat.reduceSub, Nat.reduceAdd]
  simp only [ret]
  congr
  exact subst0_wk0

theorem Eqv.ltimes_def' {tyIn tyOut tyRight : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨tyIn, ⊥⟩::Γ) (tyOut::L)}
  : r ⋉ tyRight = (Eqv.let2 Term.Eqv.braid (e := ⊥) $
    r.vwk1.vwk1 ;;
    ret (pair (var 0 (by simp)) (var 1 (by simp)))) := by
  rw [ltimes, braid_eq_ret, ret_seq_rtimes, let2_seq, seq_assoc]
  simp only [vwk1_braid, ret_pair_braid]

theorem Eqv.ret_seq_ltimes {tyIn tyOut tyRight : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (e : Term.Eqv φ ((tyIn', _)::Γ) ((tyIn.prod tyRight), ⊥)) (r : Eqv φ (⟨tyIn, ⊥⟩::Γ) (tyOut::L))
  : ret e ;; r ⋉ tyRight = (Eqv.let2 (e ;;' Term.Eqv.braid (e := ⊥)) $
    r.vwk1.vwk1 ;;
    ret (pair (var 0 (by simp)) (var 1 (by simp))))
  := by
  rw [ltimes, braid_eq_ret, <-seq_assoc, <-seq_assoc, <-ret_of_seq, ret_seq_rtimes]
  simp only [let2_seq, seq_assoc, vwk1_braid, ret_pair_braid]

theorem Eqv.lunit_braid {Γ : Ctx α ε} {L : LCtx α}
  : (lunit (φ := φ) (ty := ty) (Γ := Γ) (L := L)) ;; braid = runit
  := by simp only [lunit, ret_pair_braid]; rfl

theorem Eqv.runit_braid {Γ : Ctx α ε} {L : LCtx α}
  : (runit (φ := φ) (ty := ty) (Γ := Γ) (L := L)) ;; braid = lunit
  := by simp only [runit, ret_pair_braid]; rfl

theorem Eqv.braid_pi_l {Γ : Ctx α ε} {L : LCtx α}
  : braid ;; pi_l (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L) = pi_r
  := by simp only [braid, let2_seq, vwk1_pi_l, ret_pair_pi_l]; rfl

theorem Eqv.braid_pi_r {Γ : Ctx α ε} {L : LCtx α}
  : braid ;; pi_r (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L) = pi_l
  := by rw [<-braid_pi_l, <-seq_assoc, braid_braid, nil_seq]

theorem Eqv.rtimes_pi_r {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : Ty.unit ⋊ r ;; pi_r = pi_r ;; r := by
  simp only [rtimes, let2_seq, vwk1_pi_r, seq_assoc, ret_pair_pi_r]
  simp only [pi_r, let2_seq]
  congr 1
  exact (seq_nil _).trans (nil_seq _).symm

theorem Eqv.ltimes_pi_l {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) : r ⋉ Ty.unit ;; pi_l = pi_l ;; r := by
  rw [<-braid_rtimes_braid, seq_assoc, braid_pi_l, seq_assoc, rtimes_pi_r, <-seq_assoc, braid_pi_r]

theorem Eqv.let2_tensor_vwk2 {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ ((A, ⊥)::Γ) (A', ⊥)} {b : Term.Eqv φ ((B, ⊥)::Γ) (B', ⊥)}
  {r : Eqv φ (⟨B', ⊥⟩::⟨A', ⊥⟩::Γ) (C::L)}
  : let2 (a.tensor b) r.vwk2
  = let2 (var 0 Ctx.Var.shead) (let1 a.wk1.wk0 (let1 b.wk1.wk1.wk0 r.vwk2.vwk2.vwk2)) := by
  rw [let2_bind, Term.Eqv.tensor, let1_let2]
  apply congrArg
  calc
    _ = let2 (a.wk1.wk0.pair b.wk1.wk1) r.vwk2.vwk2.vwk2 := Eq.symm <| by
      rw [let2_bind]; simp only [vwk2, vwk_vwk, vwk1, vwk_let2, wk_var, Set.mem_setOf_eq,
        Ctx.InS.coe_wk1, Nat.liftWk_zero]; congr 3; ext k; cases k using Nat.cases2 <;> rfl
    _ = _ := by rw [let2_pair]

theorem Eqv.let2_tensor_vwk2' {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ ((A, ⊥)::Γ) (A', ⊥)} {b : Term.Eqv φ ((B, ⊥)::Γ) (B', ⊥)}
  {r : Eqv φ (⟨B', ⊥⟩::⟨A', ⊥⟩::_::Γ) (C::L)} {r' : Eqv φ (⟨B', ⊥⟩::⟨A', ⊥⟩::Γ) (C::L)}
  (hr : r = r'.vwk2)
  : let2 (a.tensor b) r
  = let2 (var 0 Ctx.Var.shead) (let1 a.wk1.wk0 (let1 b.wk1.wk1.wk0 r'.vwk2.vwk2.vwk2))
  := by cases hr; rw [let2_tensor_vwk2]

theorem Eqv.let2_ltimes_vwk2 {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ ((A, ⊥)::Γ) (A', ⊥)}
  {r : Eqv φ (⟨B, ⊥⟩::⟨A', ⊥⟩::Γ) (C::L)}
  : let2 (a ⋉' _) r.vwk2
  = let2 (var 0 Ctx.Var.shead)
  (let1 a.wk1.wk0 (let1 (var 1 Ctx.Var.shead.step) r.vwk2.vwk2.vwk2)) := by
  rw [Term.Eqv.ltimes, let2_tensor_vwk2]; rfl

theorem Eqv.let2_ltimes_vwk2' {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ ((A, ⊥)::Γ) (A', ⊥)}
  {r : Eqv φ (⟨B, ⊥⟩::⟨A', ⊥⟩::_::Γ) (C::L)} {r' : Eqv φ (⟨B, ⊥⟩::⟨A', ⊥⟩::Γ) (C::L)}
  (hr : r = r'.vwk2)
  : let2 (a ⋉' _) r
  = let2 (var 0 Ctx.Var.shead)
  (let1 a.wk1.wk0 (let1 (var 1 Ctx.Var.shead.step) r'.vwk2.vwk2.vwk2))
  := by cases hr; rw [let2_ltimes_vwk2]

theorem Eqv.Pure.central_left {A A' B B' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) (A'::L)}
  (hl : l.Pure)
  (r : Eqv φ (⟨B, ⊥⟩::Γ) (B'::L))
  : (l ⋉ B) ;; (A' ⋊ r) = (A ⋊ r) ;; (l ⋉ B') := by
  let ⟨l, hp⟩ := hl;
  cases hp
  simp only [ltimes_eq_ret, ret_seq_rtimes]
  simp only [
    Eqv.rtimes, let2_seq, seq_assoc, vwk1_ret, <-ret_of_seq, wk1_ltimes, Term.Eqv.pair_ltimes_pure
  ]
  rw [
    let2_ltimes_vwk2'
      (r' := r.vwk1 ;; Eqv.ret (pair (var 1 (by simp)) (var 0 (by simp))))
      (hr := by simp only [vwk2_seq, vwk1_vwk2]; rfl)
  ]
  apply congrArg
  simp only [let1_beta, Term.Eqv.seq, let1_beta_var1]
  induction l using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Eqv.eq_of_reg_eq
  simp only [Set.mem_setOf_eq, InS.vwk_br, Term.InS.wk_pair, Term.InS.wk_var, Ctx.InS.coe_wk1,
    Nat.liftWk_succ, Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, Nat.liftWk_zero, InS.coe_vsubst,
    Term.InS.coe_subst0, Term.InS.coe_wk, Ctx.InS.coe_wk0, Term.InS.coe_var, InS.coe_vwk,
    Ctx.InS.coe_wk2, InS.coe_lsubst, InS.coe_alpha0, InS.coe_br, Term.InS.coe_pair,
    Region.vwk_lsubst, Region.vsubst_lsubst, Term.InS.coe_subst]
  congr
  · funext k
    cases k with
    | zero =>
      simp only [Term.wk_wk, alpha, Function.comp_apply, Region.vsubst, Term.subst,
        Nat.succ_eq_add_one, zero_add, Term.Subst.lift_succ, Term.subst0_zero, Term.Subst.lift_zero,
        Function.update_same, br.injEq, Term.pair.injEq, and_true, true_and]
      simp only [<-Term.subst_fromWk, Term.subst_subst]
      congr
      funext k
      cases k <;> rfl
    | _ => rfl
  · simp only [Region.vwk_vwk]
    simp only [<-Region.vsubst_fromWk, Region.vsubst_vsubst]
    congr
    funext k
    cases k <;> rfl

theorem Eqv.Pure.central_right {A A' B B' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (A'::L))
  {r : Eqv φ (⟨B, ⊥⟩::Γ) (B'::L)}
  (hr : r.Pure)
  : (A ⋊ r) ;; (l ⋉ B') = (l ⋉ B) ;; (A' ⋊ r) := by
  rw [
    <-braid_rtimes_braid, <-seq_assoc, <-seq_assoc, <-braid_ltimes, seq_assoc Eqv.braid,
    hr.central_left, <-seq_assoc, braid_rtimes, seq_assoc (l ⋉ B), braid_ltimes,
    seq_assoc, seq_assoc (A' ⋊ r), braid_braid, seq_nil
  ]

def Eqv.assoc {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨(A.prod B).prod C, ⊥⟩::Γ) (A.prod (B.prod C)::L) :=
  let2 (var 0 ⟨by simp, le_refl _⟩) $
  let2 (var 1 ⟨by simp, le_refl _⟩) $
  ret $ pair (var 1 (by simp)) (pair (var 0 (by simp)) (var 2 (by simp)))

theorem Eqv.vwk1_assoc {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (assoc (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).vwk1 (inserted := inserted)
  = assoc := rfl

theorem Eqv.vwk2_assoc {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (assoc (φ := φ) (A := A) (B := B) (C := C) (Γ := head::Γ) (L := L)).vwk2 (inserted := inserted)
  = assoc := rfl

def Eqv.assoc_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨A.prod (B.prod C), ⊥⟩::Γ) ((A.prod B).prod C::L) :=
  let2 (var 0 ⟨by simp, le_refl _⟩) $
  let2 (var 0 ⟨by simp, le_refl _⟩) $
  ret $ pair (pair (var 3 (by simp)) (var 1 (by simp))) (var 0 (by simp))

theorem Eqv.vwk1_assoc_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (assoc_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).vwk1 (inserted := inserted)
  = assoc_inv := rfl

theorem Eqv.assoc_eq_ret {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.assoc (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L) = Eqv.ret Term.Eqv.assoc := by
  simp only [Eqv.assoc, let2_ret]
  rfl

theorem Eqv.ret_assoc_reassoc {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {e : Term.Eqv φ ((X, ⊥)::Γ) ((A.prod B).prod C, ⊥)}
  : ret e ;; assoc (φ := φ) (L := L) = ret (e.reassoc)
  := by rw [assoc_eq_ret, <-ret_of_seq, Term.Eqv.seq_prod_assoc]

theorem Eqv.Pure.assoc {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (assoc (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).Pure := ⟨_, assoc_eq_ret⟩

theorem Eqv.assoc_inv_eq_ret {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.assoc_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L) = Eqv.ret Term.Eqv.assoc_inv
  := by simp only [Eqv.assoc_inv, let2_ret]; rfl

theorem Eqv.ret_assoc_inv_reassoc_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {e : Term.Eqv φ ((X, ⊥)::Γ) (A.prod (B.prod C), ⊥)}
  : ret e ;; assoc_inv (φ := φ) (L := L) = ret (e.reassoc_inv)
  := by rw [assoc_inv_eq_ret, <-ret_of_seq, Term.Eqv.seq_assoc_inv]

theorem Eqv.Pure.assoc_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (assoc_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).Pure := ⟨_, assoc_inv_eq_ret⟩

theorem Eqv.assoc_assoc_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L) ;; assoc_inv = nil
  := by simp only [assoc_eq_ret, assoc_inv_eq_ret, ret_ret, Term.Eqv.assoc_assoc_inv, ret_nil]

theorem Eqv.assoc_inv_assoc {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L) ;; assoc = nil
  := by simp only [assoc_eq_ret, assoc_inv_eq_ret, ret_ret, Term.Eqv.assoc_inv_assoc, ret_nil]

theorem Eqv.assoc_left_nat {A B C A' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (A'::L))
  : (l ⋉ B) ⋉ C ;; assoc = assoc ;; l ⋉ (B.prod C) := by
  rw [ltimes_def', let2_seq]
  simp only [vwk1_assoc, vwk1_ltimes]
  rw [ltimes_def', let2_seq, seq_assoc]
  simp only [vwk1_br, wk1_pair, wk1_var0, List.length_cons, Fin.zero_eta, List.get_eq_getElem,
    Fin.val_zero, List.getElem_cons_zero, wk1_var_succ, zero_add, Nat.reduceAdd, ← ret_of_seq]
  rw [let2_seq, seq_assoc]
  simp only [vwk1_assoc]
  rw [assoc_eq_ret, <-ret_of_seq]
  conv => lhs; rhs; rhs; rhs; rhs; lhs; simp [Term.Eqv.seq, Term.Eqv.let1_beta_pure]
  rw [assoc_pair]
  simp only [Term.Eqv.braid, let2_let2, vwk2, let2_pair, wk0_var, Nat.reduceAdd, let1_beta,
    vwk_let2, vsubst_let2]
  rw [assoc]
  simp only [let2_seq, vwk1_ltimes, ret_seq_ltimes, pair_seq_braid_pure, let2_pair, wk0_var,
    Nat.reduceAdd, let1_beta]
  congr 2
  induction l using Quotient.inductionOn
  apply Eqv.eq_of_reg_eq
  simp only [Set.mem_setOf_eq, InS.vwk_br, Term.InS.wk_pair, Term.InS.wk_var, Ctx.InS.coe_wk1,
    Nat.liftWk_zero, Nat.liftWk_succ, Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, InS.coe_vsubst,
    Term.Subst.InS.coe_liftn₂, Term.InS.coe_subst0, Term.InS.coe_var, InS.coe_vwk,
    Ctx.InS.coe_liftn₂, Ctx.InS.coe_wk2, InS.coe_lsubst, InS.coe_alpha0, InS.coe_br,
    Term.InS.coe_pair, Region.vwk_lsubst, Region.vsubst_lsubst]
  congr 1
  · funext k; cases k <;> rfl
  · simp only [Region.vwk_vwk]
    simp only [<-Region.vsubst_fromWk, Region.vsubst_vsubst]
    congr
    funext k; cases k <;> rfl

theorem Eqv.assoc_mid_nat {A B C B' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (m : Eqv φ (⟨B, ⊥⟩::Γ) (B'::L))
  : (A ⋊ m) ⋉ C ;; assoc = assoc ;; A ⋊ (m ⋉ C) := by
  rw [ltimes_def', let2_seq]
  simp only [Term.Eqv.braid, vwk1_assoc, let2_let2, vwk2_seq, vwk1_vwk2, vwk2_br, wk2_pair,
    wk2_var0, List.length_cons, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero,
    List.getElem_cons_zero, wk2_var1, Nat.reduceAdd, Fin.mk_one, Fin.val_one,
    List.getElem_cons_succ, vwk2_assoc, let2_pair, wk0_var, let1_beta]
  simp only [vwk1_rtimes]
  rw [br_zero_eq_ret, rtimes, let2_seq, seq_assoc]
  simp only [vwk1_ret, <-ret_of_seq]
  simp only [Term.Eqv.seq, wk_res_self, wk1_pair, wk1_var0, List.length_cons, Fin.zero_eta,
    List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, wk1_var_succ, zero_add,
    Nat.reduceAdd, let1_beta_pure, subst_pair, var0_subst0, var_succ_subst0]
  rw [let2_seq, seq_assoc]
  simp only [vwk1_assoc]
  rw [assoc_eq_ret, <-ret_of_seq, Term.Eqv.assoc_pair]
  simp only [assoc, let2_seq, vwk1_seq, vwk1_ltimes, vwk1_rtimes, ret_seq_rtimes]
  simp only [vsubst_let2, var0_subst0, List.length_cons, Fin.zero_eta, List.get_eq_getElem,
    Fin.val_zero, List.getElem_cons_zero, wk_res_self, var_succ_subst0, let2_pair, wk0_pair,
    wk0_var, zero_add, Nat.reduceAdd, let1_beta]
  simp only [vsubst_liftn₂_seq]
  simp only [vsubst_br, subst_pair, subst_liftn₂_var_one, ge_iff_le, le_refl, subst_liftn₂_var_zero,
    subst_liftn₂_var_add_2, var_succ_subst0, wk0_var, zero_add, Nat.reduceAdd, var0_subst0,
    List.length_cons, Nat.liftWk_succ, Nat.succ_eq_add_one, Fin.mk_one, List.get_eq_getElem,
    Fin.val_one, List.getElem_cons_succ, List.getElem_cons_zero, Fin.zero_eta, Fin.val_zero,
    wk_res_self]
  rw [br_zero_eq_ret, wk_res_self, ltimes_def', let2_seq, seq_assoc]
  simp only [
    vwk1_ret, <-ret_of_seq, Term.Eqv.seq, let1_beta_pure, Term.Eqv.braid, let2_let2, let2_pair
  ]
  simp only [wk0_var, Nat.reduceAdd, wk1_pair, wk1_var_succ, zero_add, wk1_var0, List.length_cons,
    Fin.zero_eta, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, subst_pair,
    var_succ_subst0, var0_subst0, wk_res_self, let1_beta, vsubst_let2, nil_subst0, wk_eff_self,
    let2_pair]
  congr 2
  induction m using Quotient.inductionOn
  apply Eqv.eq_of_reg_eq
  simp only [Set.mem_setOf_eq, InS.vwk_br, Term.InS.wk_pair, Term.InS.wk_var, Ctx.InS.coe_wk1,
    Nat.liftWk_zero, Nat.liftWk_succ, Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, InS.coe_vsubst,
    Term.Subst.InS.coe_liftn₂, Term.InS.coe_subst0, Term.InS.coe_var, InS.coe_vwk,
    Ctx.InS.coe_liftn₂, Ctx.InS.coe_wk2, InS.coe_lsubst, InS.coe_alpha0, InS.coe_br,
    InS.coe_let2, Term.InS.coe_pair, Region.vwk_lsubst, Region.vsubst_lsubst]
  congr 1
  · funext k; cases k <;> rfl
  · simp only [Region.vwk_vwk]
    simp only [<-Region.vsubst_fromWk, Region.vsubst_vsubst]
    congr
    funext k; cases k <;> rfl

theorem Eqv.seq_let2_wk0_pure {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ Γ ⟨X.prod Y, ⊥⟩}
  {r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)} {s : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::⟨B, ⊥⟩::Γ) (C::L)}
  : r ;; (let2 a.wk0 s) = let2 a.wk0 (r.vwk1.vwk1 ;; s.vswap02.vswap02).vswap02 := by
  rw [
    <-Term.Eqv.pair_eta_pure (p := a.wk0), let2_pair, <-Term.Eqv.wk0_pl,
    seq_let1_wk0_pure, <-Term.Eqv.wk0_pr, <-Term.Eqv.pair_eta_pure (p := a.wk0),
    let2_pair, wk0_pl
  ]
  apply congrArg
  conv => lhs; rhs; rhs; rw [vswap01, vwk_let1, <-Term.Eqv.swap01_def, Term.Eqv.swap01_wk0_wk0]
  rw [seq_let1_wk0_pure]
  simp only [vswap01, vwk_let1, vswap02]
  rw [<-Term.Eqv.swap01_def, Term.Eqv.swap01_wk0_wk0, <-Term.Eqv.wk0_pr]
  apply congrArg
  induction r using Quotient.inductionOn
  induction s using Quotient.inductionOn
  apply Eqv.eq_of_reg_eq
  simp only [Set.mem_setOf_eq, InS.coe_vwk, Ctx.InS.coe_lift, Ctx.InS.coe_swap01, InS.coe_lsubst,
    InS.coe_alpha0, Ctx.InS.coe_wk1, Region.vwk_lsubst, Ctx.InS.coe_swap02]
  congr 1
  · funext k
    cases k with
    | zero =>
      simp only [alpha, Region.vwk_vwk, Function.comp_apply, Function.update_same]
      congr
      funext k; cases k using Nat.cases3 <;> rfl
    | succ => rfl
  · simp only [Region.vwk_vwk]
    congr
    funext k; cases k <;> rfl

theorem Eqv.seq_let2_wk0_pure' {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (_::Γ) ⟨X.prod Y, ⊥⟩} {a' : Term.Eqv φ Γ ⟨X.prod Y, ⊥⟩}
  {r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)} {s : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::⟨B, ⊥⟩::Γ) (C::L)}
  (ha : a = a'.wk0)
  : r ;; (let2 a s) = let2 a'.wk0 (r.vwk1.vwk1 ;; s.vswap02.vswap02).vswap02 := by
  cases ha; rw [seq_let2_wk0_pure]

theorem Eqv.assoc_right_nat {A B C C' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨C, ⊥⟩::Γ) (C'::L))
  : (A.prod B) ⋊ r ;; assoc = assoc ;; A ⋊ (B ⋊ r) := by
  rw [rtimes, let2_seq]
  simp only [vwk1_assoc]
  rw [seq_assoc, assoc_eq_ret, <-ret_of_seq, seq_prod_assoc, Term.Eqv.reassoc]
  simp only [Term.Eqv.let2_pair, wk0_var, zero_add, let1_beta_pure, subst_let2, var_succ_subst0,
    subst_pair, subst_liftn₂_var_one, ge_iff_le, le_refl, subst_liftn₂_var_zero,
    subst_liftn₂_var_add_2, var0_subst0, List.length_cons, Nat.reduceAdd, Fin.zero_eta,
    List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, wk_res_self]
  rw [assoc, let2_seq]
  simp only [vwk1_rtimes, let2_seq, ret_seq_rtimes, let2_pair, let1_beta]
  simp only [wk0_pair, wk0_var, zero_add, Nat.reduceAdd]
  rw [rtimes, let2_seq, seq_assoc, vwk1_ret, vwk1_ret, <-ret_of_seq]
  simp only [Term.Eqv.seq, wk1_pair, wk1_var_succ, zero_add, wk1_var0, List.length_cons,
    Fin.zero_eta, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Nat.reduceAdd,
    let1_beta_pure, subst_pair, var_succ_subst0, var0_subst0, wk_res_self, vsubst_let2,
    vsubst_liftn₂_seq, vsubst_br, subst_liftn₂_var_add_2, wk0_var, subst_liftn₂_var_one, ge_iff_le,
    le_refl, subst_liftn₂_var_zero, let2_pair, let1_beta]
  rw [br_zero_eq_ret, wk_res_self]
  apply congrArg
  rw [<-let2_ret, seq_let2_wk0_pure' (a' := var 0 Ctx.Var.shead) (ha := by rfl)]
  apply congrArg
  induction r using Quotient.inductionOn
  apply Eqv.eq_of_reg_eq
  simp only [Set.mem_setOf_eq, InS.vwk_br, Term.InS.wk_pair, Term.InS.wk_var, Ctx.InS.coe_swap02,
    Nat.ofNat_pos, Nat.swap0_lt, Nat.swap0_0, Nat.one_lt_ofNat, Ctx.InS.coe_wk1, Nat.liftWk_succ,
    Nat.succ_eq_add_one, Nat.reduceAdd, zero_add, Nat.liftWk_zero, InS.coe_vwk, InS.coe_lsubst,
    InS.coe_alpha0, InS.coe_br, Term.InS.coe_pair, Term.InS.coe_var, Region.vwk_lsubst,
    InS.coe_vsubst, Term.InS.coe_subst0, Term.Subst.InS.coe_liftn₂, Region.vsubst_lsubst]
  congr
  · funext k; cases k with
    | zero => simp
    | succ => rfl
  · simp only [Region.vwk_vwk]
    simp only [Region.vsubst_vsubst, <-Region.vsubst_fromWk]
    congr
    funext k; cases k <;> rfl

theorem Eqv.triangle {X Y : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc (φ := φ) (Γ := Γ) (L := L) (A := X) (B := Ty.unit) (C := Y) ;; X ⋊ pi_r = pi_l ⋉ Y
  := by simp only [
    ltimes_eq_ret, rtimes_eq_ret, pi_r_eq_ret, pi_l_eq_ret, assoc_eq_ret, <-ret_of_seq,
    Term.Eqv.triangle
  ]

theorem Eqv.pentagon {W X Y Z : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc (φ := φ) (Γ := Γ) (L := L) (A := W.prod X) (B := Y) (C := Z) ;; assoc
  = assoc ⋉ Z ;; assoc ;; W ⋊ assoc
  := by simp only [
    ltimes_eq_ret, rtimes_eq_ret, assoc_eq_ret, <-ret_of_seq, Term.Eqv.pentagon
  ]

theorem Eqv.hexagon {X Y Z : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc (φ := φ) (Γ := Γ) (L := L) (A := X) (B := Y) (C := Z) ;; braid ;; assoc
  = braid ⋉ Z ;; assoc ;; Y ⋊ braid
  := by simp only [
    braid_eq_ret, assoc_eq_ret, ltimes_eq_ret, rtimes_eq_ret, <-ret_of_seq, Term.Eqv.hexagon
  ]
