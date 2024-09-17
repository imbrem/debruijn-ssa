import DeBruijnSSA.BinSyntax.Typing.Term.Subst
import DeBruijnSSA.BinSyntax.Typing.Term.Compose
import DeBruijnSSA.BinSyntax.Typing.LCtx

namespace BinSyntax

namespace Term

section Product

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]
  {Γ Δ : Ctx α ε} {σ : Region.Subst φ}

def pack : ℕ → Term φ
  | 0 => unit
  | n + 1 => pair (var 0) (pack n).wk0

theorem Wf.pack_append_sup {Γ Δ : Ctx α ε}
  : Wf (φ := φ) (Γ ++ Δ) (pack Γ.length) (Γ.pack, Γ.sup_effect) := by
  induction Γ with
  | nil => exact Wf.unit _
  | cons V Γ I =>
    simp only [List.cons_append, BinSyntax.Term.pack, Ctx.pack, Ctx.sup_effect, pair_iff, var_iff,
      Ctx.Var.head_iff, ge_iff_le]
    constructor
    constructor
    rfl
    simp
    apply Wf.wk0
    apply Wf.wk_eff _ I
    simp

theorem Wf.pack_sup {Γ : Ctx α ε}
  : Wf (φ := φ) Γ (Term.pack Γ.length) (Γ.pack, Γ.sup_effect) :=
  by convert Wf.pack_append_sup (Δ := []); simp

def InS.pack {Γ : Ctx α ε} (h : ∀i, Γ.effect i ≤ e) : InS φ Γ (Γ.pack, e) := match Γ with
  | [] => unit e
  | V::Γ => pair
    (var 0 (Ctx.Var.head (by constructor; rfl; convert (h 0); simp) _))
    ((pack (Γ := Γ) (λi => by convert h (i + 1) using 1; simp)).wk0)

@[simp]
theorem InS.coe_pack {Γ : Ctx α ε} {h}
  : (InS.pack (φ := φ) (Γ := Γ) (e := e) h : Term φ) = Term.pack Γ.length
  := by induction Γ with
  | nil => rfl
  | cons => simp [pack, Term.pack, *]

abbrev _root_.BinSyntax.Ctx.Pure.pack {Γ : Ctx α ε} (h : Γ.Pure) : InS φ Γ (Γ.pack, ⊥)
  := InS.pack (e := ⊥) (h := λi => by simp [h.effect i])

@[simp]
theorem InS.wk_eff_pack {Γ : Ctx α ε} {h : ∀i, Γ.effect i ≤ lo} {h' : lo ≤ hi}
  : (pack (φ := φ) h).wk_eff h' = pack (λi => (h i).trans h') := by
  ext; simp

def unpack0 (x : ℕ) : Term φ := pl (pr^[x] (var 0))

@[simp]
theorem wk_lift_unpack0 {x : ℕ} : (unpack0 (φ := φ) x).wk (Nat.liftWk ρ) = unpack0 x := by
  simp only [unpack0, wk_pl]
  apply congrArg
  induction x with
  | zero => rfl
  | succ x ih => simp only [wk_pr, Function.iterate_succ_apply', ih]

@[simp]
theorem subst_lift_unpack0 {x : ℕ} {σ : Subst φ} : (unpack0 x).subst σ.lift = unpack0 x := by
  simp only [unpack0, subst_pl]
  apply congrArg
  induction x with
  | zero => rfl
  | succ x ih => simp only [subst_pr, Function.iterate_succ_apply', ih]

@[simp]
theorem wk1_unpack0 {x : ℕ} : (unpack0 (φ := φ) x).wk1 = unpack0 x := wk_lift_unpack0

@[simp]
theorem subst0_nil_pr_unpack0 {x : ℕ} : (unpack0 x).subst nil.pr.subst0 = unpack0 (φ := φ) (x + 1)
  := by
  simp only [unpack0, subst_pl]
  apply congrArg
  induction x with
  | zero => rfl
  | succ x ih => simp only [subst_pr, Function.iterate_succ_apply', ih]

theorem Wf.pack_drop' {Γ Δ : Ctx α ε} {i : ℕ} (hi : i < Γ.length)
  : Wf (φ := φ) ((Γ.pack, ⊥)::Δ) (Term.pr^[i] (Term.var 0))
      ((Γ.get ⟨i, hi⟩).1.prod (Ctx.pack (Γ.drop (i + 1))), e)
  := by induction i generalizing Γ with
  | zero => cases Γ with
    | nil => cases hi
    | cons _ Γ => simp [unpack0, Ctx.pack]
  | succ i I => cases Γ with
    | nil => cases hi
    | cons head Γ =>
      simp only [BinSyntax.Term.unpack0, List.length_cons, Fin.val_succ, Function.iterate_succ',
        Function.comp_apply, List.get_eq_getElem, List.getElem_cons_succ, Ctx.pack]
      apply Wf.pr
      convert I (Γ := head::Γ) (Nat.lt_of_succ_lt hi)
      simp only [List.drop_succ_cons]
      simp only [List.length_cons, add_lt_add_iff_right] at hi
      clear I
      induction Γ generalizing i with
      | nil => cases hi
      | cons head Γ I =>
        cases i with
        | zero => rfl
        | succ i =>
          simp only [List.getElem_cons_succ, List.drop_succ_cons]
          apply I
          exact hi
          simp only [List.length_cons, add_lt_add_iff_right] at hi
          exact hi

theorem Wf.pack_drop {Γ Δ : Ctx α ε} {i : ℕ} (hi : i < Γ.length)
  : Wf (φ := φ) ((Γ.pack, ⊥)::Δ) (Term.pr^[i] (Term.var 0)) (Ctx.pack (Γ.drop i), e)
  := by rw [Ctx.pack_drop hi]; apply Wf.pack_drop' hi

theorem Wf.unpack0 {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : Wf (φ := φ) ((Γ.pack, ⊥)::Δ) (unpack0 i) ((Γ.get i).1, e)
  := Wf.pl (pack_drop' i.prop)

def InS.pack_drop {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : InS φ ((Γ.pack, ⊥)::Δ) (Ctx.pack (Γ.drop i), e)
  := ⟨Term.pr^[i] (Term.var 0), Wf.pack_drop i.prop⟩

@[simp]
theorem InS.coe_pack_drop {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.pack_drop (φ := φ) (Δ := Δ) (e := e) i : Term φ) = Term.pr^[i] (Term.var 0) := rfl

def InS.pack_drop' {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : InS φ ((Γ.pack, ⊥)::Δ) ((Γ.get i).1.prod (Ctx.pack (Γ.drop (i + 1))), e)
  := ⟨Term.pr^[i] (Term.var 0), Wf.pack_drop' i.prop⟩

@[simp]
theorem InS.coe_pack_drop' {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.pack_drop' (φ := φ) (Δ := Δ) (e := e) i : Term φ) = Term.pr^[i] (Term.var 0) := rfl

theorem InS.cast_pack_drop {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.pack_drop (φ := φ) (Δ := Δ) (e := e) i).cast rfl (by rw [Ctx.pack_drop_fin]) = pack_drop' i
  := rfl

theorem InS.cast_pack_drop' {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.pack_drop' (φ := φ) (Δ := Δ) (e := e) i).cast rfl (by rw [<-Ctx.pack_drop_fin])
  = pack_drop i
  := rfl

def InS.pack_drop_succ {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : pack_drop (φ := φ)  (Γ := V::Γ) (Δ := Δ) (e := e) i.succ
  = (pack_drop' (φ := φ) (Γ := V::Γ) (Δ := Δ) (e := e) i.castSucc).pr := by
  ext; simp only [List.length_cons, Fin.val_succ, List.drop_succ_cons, Set.mem_setOf_eq,
    coe_pack_drop, Function.iterate_succ, Function.comp_apply, Term.pr, List.get_eq_getElem,
    Fin.coe_castSucc, coe_pr, coe_pack_drop']
  rw [<-Term.pr, <-Function.iterate_succ_apply, Function.iterate_succ_apply']
  rfl

def InS.unpack0 {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : InS φ ((Γ.pack, ⊥)::Δ) ((Γ.get i).1, e)
  := ⟨Term.unpack0 i, Wf.unpack0⟩

theorem InS.pl_pack_drop' {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.pack_drop' (φ := φ) (Δ := Δ) (e := e) i).pl = unpack0 i := rfl

theorem InS.coe_unpack0 {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.unpack0 (φ := φ) (Δ := Δ) (e := e) i : Term φ) = Term.unpack0 i := rfl

-- TODO: wk_lift unpack0

-- TODO: subst_lift unpack0

@[simp]
theorem InS.wk1_unpack0 {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.unpack0 (φ := φ) (Γ := Γ) (Δ := Δ) (e := e) i).wk1 (inserted := inserted) = unpack0 i := by
  ext; rw [coe_unpack0, coe_wk1, coe_unpack0, Term.wk1_unpack0]

@[simp]
theorem InS.subst0_nil_pr_unpack0 {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.unpack0 (φ := φ) (Γ := Γ) (e := e) i).subst (nil.pr.subst0)
  = unpack0 (φ := φ) (Γ := V::Γ) (Δ := Δ) i.succ := by ext; exact Term.subst0_nil_pr_unpack0

def unpack0' (n : ℕ) (i : ℕ) : Term φ := match n with
| 0 => unit
| n + 1 => let2 (var 0) (match i with | 0 => var 1 | i + 1 => unpack0' n i)

theorem Wf.unpack0' {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : Wf (φ := φ) ((Γ.pack, ⊥)::Δ) (unpack0' Γ.length i) ((Γ.get i).1, e)
  := by induction Γ generalizing Δ with
  | nil => exact i.elim0
  | cons V Γ I =>
    apply Wf.let2
    apply Wf.var (V := (V.1.prod (Ctx.pack Γ), e)); simp [Ctx.pack]
    cases i using Fin.cases with
    | zero => simp
    | succ i =>
      simp only [List.length_cons, Fin.val_succ, List.get_eq_getElem, List.getElem_cons_succ]
      exact I i

def InS.unpack0' {Γ Δ : Ctx α ε} (i : Fin Γ.length) : InS φ ((Γ.pack, ⊥)::Δ) ((Γ.get i).1, e)
  := match Γ with
  | [] => i.elim0
  | V::Γ => let2
    (var (V := (V.1.prod (Ctx.pack Γ), e)) 0 (by simp [Ctx.pack]))
    (i.cases (var 1 (by simp)) (λi => unpack0' (Γ := Γ) i))

@[simp]
theorem InS.coe_unpack0' {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.unpack0' (φ := φ) (Δ := Δ) (e := e) i : Term φ) = Term.unpack0' Γ.length i := by
  induction Γ generalizing Δ with
  | nil => exact i.elim0
  | cons V Γ I =>
    simp only [List.get_eq_getElem, List.length_cons, Set.mem_setOf_eq, unpack0', Fin.val_zero,
      List.getElem_cons_zero, InS.coe_let2, coe_var, Term.unpack0', let2.injEq, true_and]
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact I

theorem InS.unpack0_zero' {Γ Δ : Ctx α ε}
  : InS.unpack0' (φ := φ) (Γ := V::Γ) (Δ := Δ) (e := e) (by simp only [List.length_cons]; exact 0)
  = (by simp only [Ctx.pack]; apply InS.pi_l) := rfl

theorem InS.unpack0_succ' {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : InS.unpack0' (φ := φ) (Γ := V::Γ) (Δ := Δ) (e := e) i.succ
  = let2
    (var (V := (V.1.prod (Ctx.pack Γ), e)) 0 (by simp [Ctx.pack]))
    (unpack0' (Γ := Γ) i) := rfl

def Subst.unpack0 : Subst φ := λi => Term.unpack0 i

theorem Subst.Wf.unpack0 {Γ Δ : Ctx α ε}
  : Subst.Wf (φ := φ) ((Γ.pack, ⊥)::Δ) Γ Subst.unpack0 := λ_ => Term.Wf.unpack0

def Subst.InS.unpack {Γ Δ : Ctx α ε} : Subst.InS φ ((Γ.pack, ⊥)::Δ) Γ := ⟨Subst.unpack0, Wf.unpack0⟩

def Subst.pack (n : ℕ) : Subst φ := λ_ => Term.pack n

theorem Subst.Wf.pack {Γ : Ctx α ε} (h : Γ.Pure)
  : Subst.Wf (φ := φ) Γ [(Γ.pack, ⊥)] (Subst.pack Γ.length)
  := λi => by cases i using Fin.elim1; convert (h.pack (φ := φ)).prop; simp [Subst.pack]

def _root_.BinSyntax.Ctx.Pure.packS {Γ} (h : Γ.Pure) : Subst.InS φ Γ [(Γ.pack, ⊥)]
  := ⟨Subst.pack Γ.length, Subst.Wf.pack h⟩

def InS.packed {Γ Δ : Ctx α ε} (a : InS φ Γ V) : InS φ ((Γ.pack, ⊥)::Δ) V
  := a.subst Subst.InS.unpack

def InS.unpacked {Γ : Ctx α ε} (a : InS φ [(Γ.pack, ⊥)] (A, e)) (h : ∀i, Γ.effect i ≤ e)
  : InS φ Γ (A, e)
  := let1 (pack h) (a.wk_id (by simp [Ctx.Wkn.drop]))

-- TODO: version with appends? or nah?

end Product

section Sum

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [OrderBot ε]
  {Γ Δ : Ctx α ε} {σ : Region.Subst φ}

def pack0 (ℓ : ℕ) : Term φ := inr^[ℓ] (inl (var 0))

@[simp]
theorem wk_lift_pack0 {ℓ : ℕ} : (pack0 ℓ).wk (Nat.liftWk ρ) = pack0 (φ := φ) ℓ := by
  simp only [pack0]
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => simp [ih, -Function.iterate_succ, Function.iterate_succ']

@[simp]
theorem wk1_pack0 : (pack0 ℓ).wk1 = pack0 (φ := φ) ℓ := by
  simp only [wk1, wk_lift_pack0]

@[simp]
theorem subst_lift_pack0 {ℓ : ℕ} {σ : Subst φ} : (pack0 ℓ).subst σ.lift = pack0 (φ := φ) ℓ := by
  simp only [pack0]
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => simp [ih, -Function.iterate_succ, Function.iterate_succ']

@[simp]
theorem Wf.pack0 {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : Term.Wf (φ := φ) ((R.get i, ⊥)::Γ) (pack0 i) (R.pack, ⊥)  := by
  induction R generalizing Γ with
  | nil => exact i.elim0
  | cons _ _ I =>
    cases i using Fin.cases with
    | zero => exact Wf.inl $ Wf.var Ctx.Var.shead
    | succ i =>
      simp only [Fin.val_succ,
        BinSyntax.Term.pack0, Function.iterate_succ', Function.comp_apply, LCtx.pack, Wf.inr_iff]
      apply I

def InS.pack0 {Γ : Ctx α ε} (R : LCtx α) (i : Fin R.length)
  : Term.InS φ ((R.get i, ⊥)::Γ) (R.pack, ⊥) :=
  ⟨Term.pack0 i, Term.Wf.pack0⟩

@[simp]
theorem InS.coe_pack0 {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : (InS.pack0 (φ := φ) (Γ := Γ) (R := R) i : Term φ) = Term.pack0 i := rfl

@[simp]
theorem InS.wk_lift_pack0 {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {ρ : Γ.InS Δ}
  : (InS.pack0 (φ := φ) R i).wk (ρ.lift (le_refl _)) = pack0 R i := by ext; simp

@[simp]
theorem InS.wk_slift_pack0 {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {ρ : Γ.InS Δ}
  : (InS.pack0 (φ := φ) R i).wk (ρ.slift) = pack0 R i := by ext; simp

@[simp]
theorem InS.subst_lift_pack0 {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {σ : Subst.InS φ Γ Δ}
  : (InS.pack0 (φ := φ) R i).subst (σ.lift (le_refl _)) = pack0 R i := by ext; simp

@[simp]
theorem InS.subst_slift_pack0 {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {σ : Subst.InS φ Γ Δ}
  : (InS.pack0 (φ := φ) R i).subst σ.slift = pack0 R i := by ext; simp

@[simp]
theorem InS.wk1_pack0 {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : (InS.pack0 (φ := φ) (Γ := Γ) R i).wk1 (inserted := inserted) = pack0 R i := by ext; simp

end Sum
