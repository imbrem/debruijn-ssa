import DeBruijnSSA.BinSyntax.Typing.Term.Subst
import DeBruijnSSA.BinSyntax.Typing.Term.Compose
import DeBruijnSSA.BinSyntax.Typing.LCtx

namespace BinSyntax

namespace Term

section Product

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]
  {Γ Δ : Ctx α ε}

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

def pi_n (x : ℕ) (e : Term φ) : Term φ :=  pl (pr^[x] e)

-- TODO: pi_n well-formedness lore

def proj_n (x : ℕ) : Term φ := pl (pr^[x] (var 0))

@[simp]
theorem wk_lift_proj_n {x : ℕ} : (proj_n (φ := φ) x).wk (Nat.liftWk ρ) = proj_n x := by
  simp only [proj_n, wk_pl]
  apply congrArg
  induction x with
  | zero => rfl
  | succ x ih => simp only [wk_pr, Function.iterate_succ_apply', ih]

@[simp]
theorem fvi_proj_n {x : ℕ} : fvi (proj_n (φ := φ) x) = 1 := by
  simp only [fvi, Nat.reduceAdd, le_refl, tsub_eq_zero_of_le, zero_le, max_eq_left]
  induction x with
  | zero => rfl
  | succ x ih => simp [Function.iterate_succ_apply', ih]

@[simp]
theorem subst_lift_proj_n {x : ℕ} {σ : Subst φ} : (proj_n x).subst σ.lift = proj_n x := by
  simp only [proj_n, subst_pl]
  apply congrArg
  induction x with
  | zero => rfl
  | succ x ih => simp only [subst_pr, Function.iterate_succ_apply', ih]

@[simp]
theorem wk1_proj_n {x : ℕ} : (proj_n (φ := φ) x).wk1 = proj_n x := wk_lift_proj_n

@[simp]
theorem subst0_nil_pr_proj_n {x : ℕ} : (proj_n x).subst nil.pr.subst0 = proj_n (φ := φ) (x + 1)
  := by
  simp only [proj_n, subst_pl]
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
    | cons _ Γ => simp [proj_n, Ctx.pack]
  | succ i I => cases Γ with
    | nil => cases hi
    | cons head Γ =>
      simp only [BinSyntax.Term.proj_n, List.length_cons, Fin.val_succ, Function.iterate_succ',
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

theorem Wf.proj_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : Wf (φ := φ) ((Γ.pack, ⊥)::Δ) (proj_n i) ((Γ.get i).1, e)
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

def InS.proj_n {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : InS φ ((Γ.pack, ⊥)::Δ) ((Γ.get i).1, e)
  := ⟨Term.proj_n i, Wf.proj_n⟩

theorem InS.pl_pack_drop' {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.pack_drop' (φ := φ) (Δ := Δ) (e := e) i).pl = proj_n i := rfl

theorem InS.coe_proj_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.proj_n (φ := φ) (Δ := Δ) (e := e) i : Term φ) = Term.proj_n i := rfl

-- TODO: wk_lift proj_n

-- TODO: subst_lift proj_n

@[simp]
theorem InS.wk1_proj_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.proj_n (φ := φ) (Γ := Γ) (Δ := Δ) (e := e) i).wk1 (inserted := inserted) = proj_n i := by
  ext; rw [coe_proj_n, coe_wk1, coe_proj_n, Term.wk1_proj_n]

@[simp]
theorem InS.wk_lift_proj_n {Γ Δ : Ctx α ε} {i : Fin Γ.length} {ρ : Γ.InS Δ}
  : (InS.proj_n (φ := φ) (Γ := Γ) (Δ := Δ) (e := e) i).wk (ρ.lift (le_refl _)) = proj_n i := by
  ext; rw [coe_proj_n, coe_wk, coe_proj_n, Ctx.InS.coe_lift, Term.wk_lift_proj_n]

@[simp]
theorem InS.subst_lift_proj_n {Γ Δ Δ' : Ctx α ε} {i : Fin Γ.length} {σ : Subst.InS φ Δ' Δ}
  : (InS.proj_n (φ := φ) (Γ := Γ) (Δ := Δ) (e := e) i).subst (σ.lift (le_refl _)) = proj_n i := by
  ext; rw [coe_proj_n, coe_subst, coe_proj_n, Subst.InS.coe_lift, Term.subst_lift_proj_n]

@[simp]
theorem InS.subst0_nil_pr_proj_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.proj_n (φ := φ) (Γ := Γ) (e := e) i).subst (nil.pr.subst0)
  = proj_n (φ := φ) (Γ := V::Γ) (Δ := Δ) i.succ := by ext; exact Term.subst0_nil_pr_proj_n

def proj_n' (n : ℕ) (i : ℕ) : Term φ := match n with
| 0 => unit
| n + 1 => let2 (var 0) (match i with | 0 => var 1 | i + 1 => proj_n' n i)

theorem Wf.proj_n' {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : Wf (φ := φ) ((Γ.pack, ⊥)::Δ) (proj_n' Γ.length i) ((Γ.get i).1, e)
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

def InS.proj_n' {Γ Δ : Ctx α ε} (i : Fin Γ.length) : InS φ ((Γ.pack, ⊥)::Δ) ((Γ.get i).1, e)
  := match Γ with
  | [] => i.elim0
  | V::Γ => let2
    (var (V := (V.1.prod (Ctx.pack Γ), e)) 0 (by simp [Ctx.pack]))
    (i.cases (var 1 (by simp)) (λi => proj_n' (Γ := Γ) i))

@[simp]
theorem InS.coe_proj_n' {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.proj_n' (φ := φ) (Δ := Δ) (e := e) i : Term φ) = Term.proj_n' Γ.length i := by
  induction Γ generalizing Δ with
  | nil => exact i.elim0
  | cons V Γ I =>
    simp only [List.get_eq_getElem, List.length_cons, Set.mem_setOf_eq, proj_n', Fin.val_zero,
      List.getElem_cons_zero, InS.coe_let2, coe_var, Term.proj_n', let2.injEq, true_and]
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact I

theorem InS.proj_n_zero' {Γ Δ : Ctx α ε}
  : InS.proj_n' (φ := φ) (Γ := V::Γ) (Δ := Δ) (e := e) (by simp only [List.length_cons]; exact 0)
  = (by simp only [Ctx.pack]; apply InS.pi_l) := rfl

theorem InS.proj_n_succ' {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : InS.proj_n' (φ := φ) (Γ := V::Γ) (Δ := Δ) (e := e) i.succ
  = let2
    (var (V := (V.1.prod (Ctx.pack Γ), e)) 0 (by simp [Ctx.pack]))
    (proj_n' (Γ := Γ) i) := rfl

def Subst.proj_n : Subst φ := λi => Term.proj_n i

theorem Subst.Wf.proj_n {Γ Δ : Ctx α ε}
  : Subst.Wf (φ := φ) ((Γ.pack, ⊥)::Δ) Γ Subst.proj_n := λ_ => Term.Wf.proj_n

def Subst.InS.unpack {Γ Δ : Ctx α ε} : Subst.InS φ ((Γ.pack, ⊥)::Δ) Γ := ⟨Subst.proj_n, Wf.proj_n⟩

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
  {Γ Δ : Ctx α ε}

def inj (ℓ : ℕ) (e : Term φ) : Term φ := inr^[ℓ] (inl e)

@[simp]
theorem wk_inj {ℓ : ℕ} {e : Term φ} : (inj ℓ e).wk ρ = inj ℓ (e.wk ρ) := by
  simp only [inj]
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => simp [ih, -Function.iterate_succ, Function.iterate_succ']

@[simp]
theorem wk0_inj {ℓ : ℕ} {e : Term φ} : (inj ℓ e).wk0 = inj ℓ (e.wk0) := by
  simp only [wk0, wk_inj]

@[simp]
theorem wk1_inj {ℓ : ℕ} {e : Term φ} : (inj ℓ e).wk1 = inj ℓ (e.wk1) := by
  simp only [wk1, wk_inj]

@[simp]
theorem wk2_inj {ℓ : ℕ} {e : Term φ} : (inj ℓ e).wk2 = inj ℓ (e.wk2) := by
  simp only [wk2, wk_inj]

@[simp]
theorem subst_inj {ℓ : ℕ} {e : Term φ} : (inj ℓ e).subst σ = inj ℓ (e.subst σ) := by
  simp only [inj]
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => simp [ih, -Function.iterate_succ, Function.iterate_succ']

theorem Wf.inj {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {a : Term φ}
  (h : a.Wf Γ (R.get i, e)) : Term.Wf (φ := φ) Γ (inj i a) (R.pack, e)  := by
  induction R generalizing Γ with
  | nil => exact i.elim0
  | cons _ _ I =>
    cases i using Fin.cases with
    | zero => exact Wf.inl $ h
    | succ i =>
      simp only [
        Fin.val_succ, Function.iterate_succ', Function.comp_apply, LCtx.pack,
        Wf.inr_iff, BinSyntax.Term.inj
      ]
      apply I
      apply h

def InS.inj {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} (a : Term.InS φ Γ (R.get i, e))
  : Term.InS φ Γ (R.pack, e) := ⟨a.val.inj i, a.prop.inj⟩

@[simp]
theorem InS.coe_inj {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {a : Term.InS φ Γ (R.get i, e)}
  : (InS.inj (φ := φ) (Γ := Γ) (R := R) a : Term φ) = Term.inj i a := rfl

def inj_n (ℓ : ℕ) : Term φ := inj ℓ nil

@[simp]
theorem wk_lift_inj_n {ℓ : ℕ} : (inj_n ℓ).wk (Nat.liftWk ρ) = inj_n (φ := φ) ℓ := by
  simp only [inj_n, wk_inj, wk, Nat.liftWk_zero]; rfl

@[simp]
theorem wk1_inj_n : (inj_n ℓ).wk1 = inj_n (φ := φ) ℓ := by
  simp only [wk1, wk_lift_inj_n]

@[simp]
theorem wk2_inj_n : (inj_n ℓ).wk2 = inj_n (φ := φ) ℓ := by
  simp only [inj_n, wk2_inj]; rfl

@[simp]
theorem subst_lift_inj_n {ℓ : ℕ} {σ : Subst φ} : (inj_n ℓ).subst σ.lift = inj_n (φ := φ) ℓ := by
  simp only [inj_n, subst_inj, subst, Subst.lift_zero]; rfl

@[simp]
theorem Wf.inj_n {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : Term.Wf (φ := φ) ((R.get i, ⊥)::Γ) (inj_n i) (R.pack, ⊥)  := by
  induction R generalizing Γ with
  | nil => exact i.elim0
  | cons _ _ I =>
    cases i using Fin.cases with
    | zero => exact Wf.inl $ Wf.var Ctx.Var.shead
    | succ i =>
      simp only [
        Fin.val_succ, BinSyntax.Term.inj_n, Function.iterate_succ', Function.comp_apply, LCtx.pack,
        Wf.inr_iff, BinSyntax.Term.inj
      ]
      apply I

def InS.inj_n {Γ : Ctx α ε} (R : LCtx α) (i : Fin R.length)
  : Term.InS φ ((R.get i, ⊥)::Γ) (R.pack, ⊥) :=
  ⟨Term.inj_n i, Term.Wf.inj_n⟩

@[simp]
theorem InS.coe_inj_n {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : (InS.inj_n (φ := φ) (Γ := Γ) (R := R) i : Term φ) = Term.inj_n i := rfl

@[simp]
theorem InS.wk_lift_inj_n {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {ρ : Γ.InS Δ}
  : (InS.inj_n (φ := φ) R i).wk (ρ.lift (le_refl _)) = inj_n R i := by ext; simp

@[simp]
theorem InS.wk_slift_inj_n {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {ρ : Γ.InS Δ}
  : (InS.inj_n (φ := φ) R i).wk (ρ.slift) = inj_n R i := by ext; simp

@[simp]
theorem InS.subst_lift_inj_n {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {σ : Subst.InS φ Γ Δ}
  : (InS.inj_n (φ := φ) R i).subst (σ.lift (le_refl _)) = inj_n R i := by ext; simp

@[simp]
theorem InS.subst_slift_inj_n {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {σ : Subst.InS φ Γ Δ}
  : (InS.inj_n (φ := φ) R i).subst σ.slift = inj_n R i := by ext; simp

@[simp]
theorem InS.wk1_inj_n {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : (InS.inj_n (φ := φ) (Γ := Γ) R i).wk1 (inserted := inserted) = inj_n R i := by ext; simp

end Sum
