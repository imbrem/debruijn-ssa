import DeBruijnSSA.BinSyntax.Rewrite.Region.LSubst
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Seq
import DeBruijnSSA.BinSyntax.Typing.Region.Compose

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

open Term.Eqv

def Eqv.coprod {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) (C::L)
  := case (var 0 Ctx.Var.shead) l.vwk1 r.vwk1

theorem Eqv.lwk_slift_coprod {A B C : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
  {ρ : L.InS K} {l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)} {r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (l.coprod r).lwk ρ.slift = (l.lwk ρ.slift).coprod (r.lwk ρ.slift)
  := by simp only [coprod, lwk_case, vwk1_lwk]

theorem Eqv.lwk1_coprod {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)} {r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (l.coprod r).lwk1 (inserted := inserted) = (l.lwk1).coprod (r.lwk1)
  := by simp only [lwk1, <-LCtx.InS.slift_wk0, lwk_slift_coprod]

theorem Eqv.vwk_slift_coprod {A B C : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {ρ : Γ.InS Δ}
  {l : Eqv φ (⟨A, ⊥⟩::Δ) (C::L)} {r : Eqv φ (⟨B, ⊥⟩::Δ) (C::L)}
  : (l.coprod r).vwk ρ.slift = (l.vwk ρ.slift).coprod (r.vwk ρ.slift) := by
  simp only [coprod, vwk_case, vwk1, vwk_vwk]
  congr 2 <;> ext k <;> cases k <;> rfl

theorem Eqv.vwk1_coprod {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)} {r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (l.coprod r).vwk1 (inserted := inserted) = l.vwk1.coprod r.vwk1 := by
  simp only [vwk1, <-Ctx.InS.lift_wk0, vwk_slift_coprod]

theorem Eqv.Pure.coprod {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)} (hl : l.Pure)
  {r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)} (hr : r.Pure)
  : (coprod l r).Pure := sorry

theorem Eqv.coprod_seq {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)) (s : Eqv φ (⟨C, ⊥⟩::Γ) (D::L))
  : (coprod l r) ;; s = coprod (l ;; s) (r ;; s)
  := by simp [coprod, case_seq, vwk1_seq]

def Eqv.join {Γ : Ctx α ε} {L : LCtx α} {A : Ty α}
  : Eqv φ (⟨A.coprod A, ⊥⟩::Γ) (A::L)
  := coprod nil nil

def Eqv.zero {Γ : Ctx α ε} {L : LCtx α} {A : Ty α}
  : Eqv φ (⟨Ty.empty, ⊥⟩::Γ) (A::L)
  := ret $ (abort (var 0 Ctx.Var.shead) A)

theorem Eqv.zero_eq {A : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (r s : Eqv φ (⟨Ty.empty, ⊥⟩::Γ) (A::L))
  : r = s
  := by apply Eqv.initial; exact ⟨(Ty.empty, ⊥), by simp, Ty.IsInitial.empty, rfl⟩

theorem Eqv.zero_seq {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : Eqv.zero ;; r = Eqv.zero
  := zero_eq _ _

def Eqv.lzero {Γ : Ctx α ε} {L : LCtx α} {A : Ty α}
  : Eqv φ (⟨Ty.empty.coprod A, ⊥⟩::Γ) (A::L)
  := coprod zero nil

def Eqv.rzero {Γ : Ctx α ε} {L : LCtx α} {A : Ty α}
  : Eqv φ (⟨A.coprod Ty.empty, ⊥⟩::Γ) (A::L)
  := coprod nil zero

def Eqv.inj_l {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨A, ⊥⟩::Γ) (A.coprod B::L)
  := ret (inl (var 0 Ctx.Var.shead))

theorem Eqv.vwk1_inj_l {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (inj_l (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L)).vwk1 (inserted := inserted)
  = inj_l := rfl

theorem Eqv.lwk1_inj_l {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (inj_l (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L)).lwk1 (inserted := inserted)
  = inj_l := rfl

theorem Eqv.ret_seq_inj_l {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) (B, ⊥)}
  : ret (targets := L) a ;; inj_l (B := C) = ret a.inl := by
  rw [inj_l, ret_seq]
  induction a using Quotient.inductionOn;
  rfl

def Eqv.inj_r {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨B, ⊥⟩::Γ) (A.coprod B::L)
  := ret (inr (var 0 Ctx.Var.shead))

theorem Eqv.vwk1_inj_r {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (inj_r (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L)).vwk1 (inserted := inserted)
  = inj_r := rfl

theorem Eqv.lwk1_inj_r {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (inj_r (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L)).lwk1 (inserted := inserted)
  = inj_r := rfl

theorem Eqv.Pure.lzero {Γ : Ctx α ε} {L : LCtx α} {A : Ty α}
  : (lzero (φ := φ) (Γ := Γ) (L := L) (A := A)).Pure := sorry

theorem Eqv.Pure.rzero {Γ : Ctx α ε} {L : LCtx α} {A : Ty α}
  : (rzero (φ := φ) (Γ := Γ) (L := L) (A := A)).Pure := sorry

theorem Eqv.Pure.inj_l {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (inj_l (φ := φ) (Γ := Γ) (L := L) (A := A) (B := B)).Pure
  := ⟨inl (var 0 Ctx.Var.shead), rfl⟩

theorem Eqv.Pure.inj_r {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (inj_r (φ := φ) (Γ := Γ) (L := L) (A := A) (B := B)).Pure
  := ⟨inr (var 0 Ctx.Var.shead), rfl⟩

theorem Eqv.ret_seq_inj_r {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (⟨B, ⊥⟩::Γ) (C, ⊥)}
  : ret (targets := L) a ;; inj_r (A := A) = ret a.inr := by
  rw [inj_r, ret_seq]
  induction a using Quotient.inductionOn;
  rfl

def Eqv.sum {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L))
  : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) ((C.coprod D)::L)
  := coprod (l ;; inj_l) (r ;; inj_r)

theorem Eqv.lwk_slift_sum {A B C D : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
  {ρ : L.InS K} {l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)} {r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L)}
  : (l.sum r).lwk ρ.slift = (l.lwk ρ.slift).sum (r.lwk ρ.slift)
  := by simp only [sum, lwk_slift_coprod, lwk_slift_seq]; rfl

theorem Eqv.lwk1_sum {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)} {r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L)}
  : (l.sum r).lwk1 (inserted := inserted) = (l.lwk1).sum (r.lwk1)
  := by simp only [lwk1, <-LCtx.InS.slift_wk0, lwk_slift_sum]

theorem Eqv.vwk_slift_sum {A B C D : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {ρ : Γ.InS Δ} {l : Eqv φ (⟨A, ⊥⟩::Δ) (C::L)} {r : Eqv φ (⟨B, ⊥⟩::Δ) (D::L)}
  : (l.sum r).vwk ρ.slift = (l.vwk ρ.slift).sum (r.vwk ρ.slift)
  := by simp only [sum, vwk_slift_coprod, vwk_lift_seq]; rfl

theorem Eqv.vwk1_sum {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)} {r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L)}
  : (l.sum r).vwk1 (inserted := inserted) = l.vwk1.sum r.vwk1
  := by simp only [vwk1, <-Ctx.InS.lift_wk0, vwk_slift_sum]

theorem Eqv.Pure.sum {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)} (hl : l.Pure)
  {r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L)} (hr : r.Pure)
  : (sum l r).Pure := coprod (seq hl inj_l) (seq hr inj_r)

theorem Eqv.coprod_inl_inr {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : coprod inj_l inj_r = Eqv.nil (φ := φ) (ty := A.coprod B) (rest := Γ) (targets := L) := by
  -- TODO: case_eta
  sorry

theorem Eqv.sum_nil {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : sum (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L) nil nil = nil := coprod_inl_inr

theorem Eqv.inj_l_coprod {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : inj_l ;; coprod l r = l := by
  stop
  rw [inj_l, coprod, ret_seq, vwk1, vwk_case, vsubst_case]
  simp only [Set.mem_setOf_eq, wk_var, Nat.liftWk_zero, subst_var, Term.Subst.InS.get_0_subst0]
  rw [case_inl, let1_beta, vwk1, vwk_vwk, vsubst_vsubst]
  -- TODO: vwk_vsubst, lore...
  sorry

theorem Eqv.inj_r_coprod {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : inj_r ;; coprod l r = r := by
  stop
  rw [inj_r, coprod, ret_seq, vwk1, vwk_case, vsubst_case]
  simp only [Set.mem_setOf_eq, wk_var, Nat.liftWk_zero, subst_var, Term.Subst.InS.get_0_subst0]
  rw [case_inr, let1_beta, vwk1, vwk_vwk, vsubst_vsubst]
  -- TODO: vwk_vsubst, lore...
  sorry

theorem Eqv.inj_l_rzero
  : inj_l ;; rzero = nil (φ := φ) (ty := A) (rest := Γ) (targets := L) := by
  rw [rzero, inj_l_coprod]

theorem Eqv.inj_r_lzero
  : inj_r ;; lzero = nil (φ := φ) (ty := A) (rest := Γ) (targets := L) := by
  rw [lzero, inj_r_coprod]

theorem Eqv.rzero_inj_l {A : Ty α}
  : rzero ;; inj_l = nil (φ := φ) (ty := A.coprod Ty.empty) (rest := Γ) (targets := L) := by
  rw [rzero, coprod_seq, <-sum_nil, sum]
  congr 1
  apply zero_eq

theorem Eqv.lzero_inj_r {A : Ty α}
  : lzero ;; inj_r = nil (φ := φ) (ty := Ty.empty.coprod A) (rest := Γ) (targets := L) := by
  rw [lzero, coprod_seq, <-sum_nil, sum]
  congr 1
  apply zero_eq

-- TODO: naturality

theorem Eqv.inj_l_join {Γ : Ctx α ε} {L : LCtx α}
  : inj_l ;; join (φ := φ) (A := A) (Γ := Γ) (L := L) = nil := by
  rw [join, inj_l_coprod]

theorem Eqv.inj_r_join {Γ : Ctx α ε} {L : LCtx α}
  : inj_r ;; join (φ := φ) (A := A) (Γ := Γ) (L := L) = nil := by
  rw [join, inj_r_coprod]

-- TODO: sum_nil_zero_join, sum_zero_nil_join for comonoid structure

-- TODO: universal comonoid compatibility, so join merges everything

theorem Eqv.inj_l_seq_sum {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L))
  : inj_l ;; (sum l r) = l ;; inj_l := by rw [sum, inj_l_coprod]

theorem Eqv.inj_r_seq_sum {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L))
  : inj_r ;; (sum l r) = r ;; inj_r := by rw [sum, inj_r_coprod]

theorem Eqv.sum_seq_coprod {A B C D E : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L))
  (s : Eqv φ (⟨C, ⊥⟩::Γ) (E::L)) (t : Eqv φ (⟨D, ⊥⟩::Γ) (E::L))
  : (sum l r) ;; (coprod s t) = coprod (l ;; s) (r ;; t) := by
  rw [sum, coprod_seq, seq_assoc, inj_l_coprod, seq_assoc, inj_r_coprod]

theorem Eqv.sum_seq_sum {A B C D E F : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L))
  (s : Eqv φ (⟨C, ⊥⟩::Γ) (E::L)) (t : Eqv φ (⟨D, ⊥⟩::Γ) (F::L))
  : (sum l r) ;; (sum s t) = sum (l ;; s) (r ;; t) := by
  rw [sum, coprod_seq, seq_assoc, inj_l_seq_sum, seq_assoc, inj_r_seq_sum]
  simp only [<-seq_assoc]; rfl

theorem Eqv.sum_seq_join {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : (sum l r) ;; join = coprod l r := by simp [join, sum_seq_coprod]

theorem Eqv.sum_self_seq_join {A B} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : sum r r ;; join = join ;; r := by rw [sum_seq_join, join, coprod_seq]; simp

def Eqv.braid_sum {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) (B.coprod A::L)
  := coprod inj_r inj_l

theorem Eqv.Pure.braid_sum {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (braid_sum (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L)).Pure := coprod inj_r inj_l

theorem Eqv.braid_sum_seq_braid_sum {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : braid_sum (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L) ;; braid_sum = nil := by
  simp only [braid_sum, coprod_seq, inj_l_coprod, inj_r_coprod, coprod_inl_inr]

theorem Eqv.braid_sum_seq_coprod {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : braid_sum ;; (coprod l r) = coprod r l := by
  rw [braid_sum, coprod_seq, inj_l_coprod, inj_r_coprod]

theorem Eqv.braid_sum_seq_sum {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L))
  : braid_sum ;; (sum l r) = sum r l ;; braid_sum := by
  rw [sum, braid_sum_seq_coprod, braid_sum, sum_seq_coprod]

def Eqv.assoc_sum {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨(A.coprod B).coprod C, ⊥⟩::Γ) (A.coprod (B.coprod C)::L)
  := sorry

def Eqv.assoc_inv_sum {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨A.coprod (B.coprod C), ⊥⟩::Γ) ((A.coprod B).coprod C::L)
  := sorry

theorem Eqv.Pure.assoc_sum {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (assoc_sum (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).Pure := sorry

theorem Eqv.Pure.assoc_inv_sum {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (assoc_inv_sum (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).Pure := sorry

theorem Eqv.assoc_assoc_inv_sum {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc_sum (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L) ;; assoc_inv_sum = nil
  := sorry

theorem Eqv.assoc_inv_assoc_sum {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc_inv_sum (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L) ;; assoc_sum = nil
  := sorry

theorem Eqv.assoc_sum_nat {A B C A' B' C' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (A'::L)) (m : Eqv φ (⟨B, ⊥⟩::Γ) (B'::L)) (r : Eqv φ (⟨C, ⊥⟩::Γ) (C'::L))
  : sum (sum l m) r ;; assoc_sum = assoc_sum ;; sum l (sum m r) := sorry

theorem Eqv.triangle_sum {X Y : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc_sum (φ := φ) (Γ := Γ) (L := L) (A := X) (B := Ty.empty) (C := Y) ;; nil.sum lzero
  = rzero.sum nil := sorry

theorem Eqv.pentagon_sum {W X Y Z : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc_sum (φ := φ) (Γ := Γ) (L := L) (A := W.coprod X) (B := Y) (C := Z) ;; assoc_sum
  = assoc_sum.sum nil ;; assoc_sum ;; nil.sum assoc_sum := sorry

theorem Eqv.hexagon_sum {X Y Z : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc_sum (φ := φ) (Γ := Γ) (L := L) (A := X) (B := Y) (C := Z) ;; braid_sum ;; assoc_sum
  = braid_sum.sum nil ;; assoc_sum ;; nil.sum braid_sum := sorry
