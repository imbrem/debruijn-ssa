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

-- TODO: proper ltimes?
def Eqv.ltimes {tyIn tyOut : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨tyIn, ⊥⟩::Γ) (tyOut::L)) (tyRight : Ty α)
  : Eqv φ (⟨tyIn.prod tyRight, ⊥⟩::Γ) ((tyOut.prod tyRight)::L)
  := Eqv.braid ;; tyRight ⋊ r ;; Eqv.braid

infixl:70 " ⋉ "  => Eqv.ltimes

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

theorem Eqv.Pure.central_left {A A' B B' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) (A'::L)}
  (hl : l.Pure)
  (r : Eqv φ (⟨B, ⊥⟩::Γ) (B'::L))
  : (l ⋉ B) ;; (A' ⋊ r) = (A ⋊ r) ;; (l ⋉ B') := by
  let ⟨p, hp⟩ := hl;
  simp only [hp, ltimes_eq_ret, Eqv.rtimes, Eqv.vwk1, ret_seq, vwk_let2, wk_var, Set.mem_setOf_eq,
    Ctx.InS.coe_wk1, Nat.liftWk_zero, vsubst_let2, var0_subst0, List.length_cons, id_eq,
    Fin.zero_eta, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, wk_res_self]
  rw [let2_bind, Term.Eqv.ltimes, Term.Eqv.tensor, let1_let2, let2_seq]
  apply congrArg
  simp [
    let1_beta, Eqv.vwk1, let2_pair, <-ltimes_eq_ret, Eqv.ltimes, Eqv.rtimes, vwk_vwk,
    ret_seq, vwk_ret, seq_assoc,
  ]
  simp [let2_seq, br_zero_eq_ret, ret_pair_braid]
  simp [
    Eqv.braid, let2_seq, let2_pair, let1_beta, Eqv.vwk1, vwk_ret, ret_seq, wk_wk,
    br_zero_eq_ret
  ]
  sorry

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

def Eqv.assoc_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨A.prod (B.prod C), ⊥⟩::Γ) ((A.prod B).prod C::L) :=
  let2 (var 0 ⟨by simp, le_refl _⟩) $
  let2 (var 0 ⟨by simp, le_refl _⟩) $
  ret $ pair (pair (var 3 (by simp)) (var 1 (by simp))) (var 0 (by simp))

theorem Eqv.assoc_eq_ret {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.assoc (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L) = Eqv.ret Term.Eqv.assoc := by
  simp only [Eqv.assoc, let2_ret]
  rfl

theorem Eqv.Pure.assoc {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (assoc (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).Pure := ⟨_, assoc_eq_ret⟩

theorem Eqv.assoc_inv_eq_ret {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.assoc_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L) = Eqv.ret Term.Eqv.assoc_inv
  := by simp only [Eqv.assoc_inv, let2_ret]; rfl

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
  : (l ⋉ B) ⋉ C ;; assoc = assoc ;; l ⋉ (B.prod C) := sorry

theorem Eqv.assoc_mid_nat {A B C B' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (m : Eqv φ (⟨B, ⊥⟩::Γ) (B'::L))
  : (A ⋊ m) ⋉ C ;; assoc = assoc ;; A ⋊ (m ⋉ C) := sorry

theorem Eqv.assoc_right_nat {A B C C' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨C, ⊥⟩::Γ) (C'::L))
  : (A.prod B) ⋊ r ;; assoc = assoc ;; A ⋊ (B ⋊ r) := sorry

theorem Eqv.triangle {X Y : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc (φ := φ) (Γ := Γ) (L := L) (A := X) (B := Ty.unit) (C := Y) ;; X ⋊ pi_r
  = pi_l ⋉ Y := sorry

theorem Eqv.pentagon {W X Y Z : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc (φ := φ) (Γ := Γ) (L := L) (A := W.prod X) (B := Y) (C := Z) ;; assoc
  = assoc ⋉ Z ;; assoc ;; W ⋊ assoc
  := sorry

theorem Eqv.hexagon {X Y Z : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc (φ := φ) (Γ := Γ) (L := L) (A := X) (B := Y) (C := Z) ;; braid ;; assoc
  = braid ⋉ Z ;; assoc ;; Y ⋊ braid
  := sorry
