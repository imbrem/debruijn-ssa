import DeBruijnSSA.BinSyntax.Rewrite.Region.LSubst
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Seq
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

theorem Eqv.Pure.rtimes {tyIn tyOut : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (tyLeft : Ty α) {r : Eqv φ (⟨tyIn, ⊥⟩::Γ) (tyOut::L)}
  : Eqv.Pure r → Eqv.Pure (tyLeft ⋊ r) := sorry

def Eqv.braid {left right : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨left.prod right, ⊥⟩::Γ) ((right.prod left)::L)
  := Eqv.let2 (var 0 Ctx.Var.shead) $
  ret (pair (var 0 (by simp)) (var 1 (by simp)))

theorem Eqv.Pure.braid {left right : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.Pure (Eqv.braid (φ := φ) (left := left) (right := right) (Γ := Γ) (L := L)) := sorry

theorem Eqv.repack {left right : Ty α} {rest : Ctx α ε} {targets : LCtx α}
  : Eqv.let2 (var 0 ⟨by simp, le_refl _⟩)
    (Eqv.ret (pair (var 1 (by simp)) (var 0 (by simp))))
  = Eqv.nil (φ := φ) (ty := left.prod right) (rest := rest) (targets := targets) := by
  rw [<-let1_0_nil, <-let2_eta, let1_beta]
  rfl

theorem Eqv.braid_braid {left right : Ty α}
  : Eqv.braid ;; Eqv.braid
  = (Eqv.nil (φ := φ) (ty := left.prod right) (rest := rest) (targets := targets)) := by
  stop
  simp only [
    braid, let2_seq, vwk1, vwk_let2, wk_var, wk_pair, Nat.liftWk, vwk_ret, Ctx.InS.liftn₂,
    Nat.liftnWk, Nat.one_lt_ofNat, Nat.ofNat_pos, ↓reduceIte, ret_seq, vsubst_let2,
    subst_pair, subst_var, Term.Subst.InS.get_0_subst0, let2_pair, let1_beta, vsubst_vsubst
  ]
  apply Eqv.repack

theorem Eqv.rtimes_nil {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (tyLeft : Ty α)
  : tyLeft ⋊ Eqv.nil = (Eqv.nil (φ := φ) (ty := tyLeft.prod ty) (rest := Γ) (targets := L)) := by
  simp only [rtimes, nil_vwk1, nil_seq, repack]

theorem Eqv.rtimes_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (tyLeft : Ty α) (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (s : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : tyLeft ⋊ (r ;; s) = (tyLeft ⋊ r) ;; (tyLeft ⋊ s) := by
  stop
  apply Eq.symm
  rw [rtimes, rtimes, let2_seq, seq_assoc, ret_seq]
  simp only [
    vwk1, vwk_let2, wk_var, Nat.liftWk, vsubst_let2, vwk_vwk, Ctx.InS.liftn₂_comp_liftn₂,
    subst_pair, subst_var, Term.Subst.InS.get_0_subst0, let2_pair, let1_beta,
    vsubst_vsubst
  ]
  apply congrArg
  rw [vwk1_seq, vwk1_seq, seq_assoc]
  congr 1
  . simp [vwk1, vwk_vwk]
  . sorry

def Eqv.ltimes {tyIn tyOut : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨tyIn, ⊥⟩::Γ) (tyOut::L)) (tyRight : Ty α)
  : Eqv φ (⟨tyIn.prod tyRight, ⊥⟩::Γ) ((tyOut.prod tyRight)::L)
  := Eqv.braid ;; tyRight ⋊ r ;; Eqv.braid

infixl:70 " ⋉ "  => Eqv.ltimes

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

theorem Eqv.ltimes_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (s : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : (r ;; s) ⋉ tyRight = (r ⋉ tyRight) ;; (s ⋉ tyRight) := by
  simp only [<-braid_rtimes_braid, rtimes_seq, seq_assoc]
  rw [<-seq_assoc braid braid, braid_braid, nil_seq]

def Eqv.runit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨ty.prod Ty.unit, ⊥⟩::Γ) (ty::L)
  := let2 (var 0 Ctx.Var.shead) (ret $ var 1 (by simp))

def Eqv.runit_inv {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨ty, ⊥⟩::Γ) (ty.prod Ty.unit::L)
  := ret $ (pair (var 0 Ctx.Var.shead) (unit _))

theorem Eqv.Pure.runit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (runit (φ := φ) (ty := ty) (Γ := Γ) (L := L)).Pure := sorry

theorem Eqv.Pure.runit_inv {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (runit_inv (φ := φ) (ty := ty) (Γ := Γ) (L := L)).Pure := sorry

theorem Eqv.runit_runit_inv_helper {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : runit (φ := φ) (ty := ty) (Γ := Γ) (L := L) ;; runit_inv
  = let2 (var 0 ⟨by simp, le_refl _⟩)
    (let1 (unit ⊥) (ret $ pair (var 2 (by simp)) (var 0 (by simp)))) := by
  rw [let1_beta]
  rfl

theorem Eqv.runit_runit_inv {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : runit (φ := φ) (ty := ty) (Γ := Γ) (L := L) ;; runit_inv = nil := by
  rw [runit_runit_inv_helper, terminal _ (var 0 (by simp)), let1_beta]
  apply repack

theorem Eqv.runit_inv_runit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : runit_inv (φ := φ) (ty := ty) (Γ := Γ) (L := L) ;; runit = nil := by
  stop
  simp only [runit_inv, runit, ret_seq]
  rw [vwk1, vwk_let2, vsubst_let2, wk_var, subst_var]
  simp only [Nat.liftWk_zero, Term.Subst.InS.get_0_subst0, Set.mem_setOf_eq]
  rw [let2_pair, let1_beta, let1_beta]
  rfl

theorem Eqv.ltimes_runit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : r ⋉ Ty.unit ;; runit = runit ;; r := sorry

def Eqv.lunit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨Ty.unit.prod ty, ⊥⟩::Γ) (ty::L)
  := let2 (var 0 Ctx.Var.shead) (ret $ var 0 (by simp))

def Eqv.lunit_inv {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨ty, ⊥⟩::Γ) (Ty.unit.prod ty::L)
  := ret $ (pair (unit _) (var 0 Ctx.Var.shead))

theorem Eqv.Pure.lunit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (lunit (φ := φ) (ty := ty) (Γ := Γ) (L := L)).Pure := sorry

theorem Eqv.Pure.lunit_inv {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (lunit_inv (φ := φ) (ty := ty) (Γ := Γ) (L := L)).Pure := sorry

theorem Eqv.lunit_seq_lunit_inv {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : lunit (φ := φ) (ty := ty) (Γ := Γ) (L := L) ;; lunit_inv = nil
  := sorry

theorem Eqv.lunit_inv_lunit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : lunit_inv (φ := φ) (ty := ty) (Γ := Γ) (L := L) ;; lunit = nil
  := sorry

-- TODO: braid ;; lunit = runit, lunit_inv ;; braid = runit_inv, and vice versa...

theorem Eqv.rtimes_lunit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : Ty.unit ⋊ r ;; lunit = lunit ;; r
  := sorry

theorem Eqv.Pure.central_left {A A' B B' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) (A'::L)}
  (hl : l.Pure)
  (r : Eqv φ (⟨B, ⊥⟩::Γ) (B'::L))
  : (l ⋉ B) ;; (A' ⋊ r) = (A ⋊ r) ;; (l ⋉ B') := sorry

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

theorem Eqv.Pure.assoc {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (assoc (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).Pure := sorry

theorem Eqv.Pure.assoc_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (assoc_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).Pure := sorry

theorem Eqv.assoc_assoc_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L) ;; assoc_inv = nil
  := sorry

theorem Eqv.assoc_inv_assoc {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L) ;; assoc = nil
  := sorry

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
  : assoc (φ := φ) (Γ := Γ) (L := L) (A := X) (B := Ty.unit) (C := Y) ;; X ⋊ lunit
  = runit ⋉ Y := sorry

theorem Eqv.pentagon {W X Y Z : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc (φ := φ) (Γ := Γ) (L := L) (A := W.prod X) (B := Y) (C := Z) ;; assoc
  = assoc ⋉ Z ;; assoc ;; W ⋊ assoc
  := sorry

theorem Eqv.hexagon {X Y Z : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc (φ := φ) (Γ := Γ) (L := L) (A := X) (B := Y) (C := Z) ;; braid ;; assoc
  = braid ⋉ Z ;; assoc ;; Y ⋊ braid
  := sorry
