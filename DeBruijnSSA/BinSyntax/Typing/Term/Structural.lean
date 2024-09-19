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
  | n + 1 => pair (pack n).wk0 (var 0)

theorem Wf.pack_append_sup {Γ Δ : Ctx α ε}
  : Wf (φ := φ) (Γ ++ Δ) (pack Γ.length) (Γ.pack, Γ.sup_effect) := by
  induction Γ with
  | nil => exact Wf.unit _
  | cons V Γ I =>
    simp only [List.cons_append, BinSyntax.Term.pack, Ctx.pack, Ctx.sup_effect, pair_iff, var_iff,
      Ctx.Var.head_iff, ge_iff_le]
    constructor
    apply Wf.wk0
    apply Wf.wk_eff _ I
    simp
    constructor
    rfl
    simp

theorem Wf.pack_sup {Γ : Ctx α ε}
  : Wf (φ := φ) Γ (Term.pack Γ.length) (Γ.pack, Γ.sup_effect) :=
  by convert Wf.pack_append_sup (Δ := []); simp

def InS.pack {Γ : Ctx α ε} (h : ∀i, Γ.effect i ≤ e) : InS φ Γ (Γ.pack, e) := match Γ with
  | [] => unit e
  | V::Γ => pair
    ((pack (Γ := Γ) (λi => by convert h (i + 1) using 1; simp)).wk0)
    (var 0 (Ctx.Var.head (by constructor; rfl; convert (h 0); simp) _))

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

def pn (x : ℕ) (e : Term φ) : Term φ :=  pr (pl^[x] e)

@[simp]
theorem wk_pn {x : ℕ} {e : Term φ} : (pn x e).wk ρ = pn x (e.wk ρ) := by
  simp only [pn, wk_pr]
  apply congrArg
  induction x with
  | zero => rfl
  | succ x ih => simp only [wk_pl, Function.iterate_succ_apply', ih]

@[simp]
theorem subst_pn {x : ℕ} {e : Term φ} : (pn x e).subst σ = pn x (e.subst σ) := by
  simp only [pn, subst_pr]
  apply congrArg
  induction x with
  | zero => rfl
  | succ x ih => simp only [subst_pl, Function.iterate_succ_apply', ih]

theorem wk0_pn {x : ℕ} {e : Term φ} : (pn x e).wk0 = pn x (e.wk0) := by
  simp only [wk0, wk_pn]

theorem wk1_pn {x : ℕ} {e : Term φ} : (pn x e).wk1 = pn x (e.wk1) := by
  simp only [wk1, wk_pn]

theorem wk2_pn {x : ℕ} {e : Term φ} : (pn x e).wk2 = pn x (e.wk2) := by
  simp only [wk2, wk_pn]

@[simp]
theorem fvi_pn {x : ℕ} {e : Term φ} : fvi (pn x e) = fvi e := by
  simp only [fvi, zero_add, Nat.one_le_ofNat, tsub_eq_zero_of_le, zero_le, max_eq_left]
  induction x with
  | zero => rfl
  | succ x ih => simp [Function.iterate_succ_apply', ih]

-- theorem Wf.pn {Γ Δ : Ctx α ε} {i : Fin Δ.length} {a : Term φ}
--   (h : a.Wf Γ (Δ.pack, ⊥)) : Term.Wf (φ := φ) Γ (pn i a) (Δ.get i)  := by
--   induction R generalizing Γ with
--   | nil => exact i.elim0
--   | cons _ _ I =>
--     cases i using Fin.cases with
--     | zero => apply Wf.pl; convert h using 1; simp only [List.get_eq_getElem, List.length_cons,
--       Fin.val_zero, List.getElem_cons_zero, LCtx.pack]
--     | succ i => sorry

def pi_n (x : ℕ) : Term φ := pn x nil

@[simp]
theorem wk_lift_pi_n {x : ℕ} : (pi_n (φ := φ) x).wk (Nat.liftWk ρ) = pi_n x := by
  simp only [pi_n, wk_pn]; rfl

@[simp]
theorem fvi_pi_n {x : ℕ} : fvi (pi_n (φ := φ) x) = 1 := by
  simp only [pi_n, fvi_pn]; rfl

@[simp]
theorem subst_lift_pi_n {x : ℕ} {σ : Subst φ} : (pi_n x).subst σ.lift = pi_n x := by
  simp only [pi_n, subst_pn]; rfl

@[simp]
theorem wk1_pi_n {x : ℕ} : (pi_n (φ := φ) x).wk1 = pi_n x := wk_lift_pi_n

@[simp]
theorem subst0_nil_pl_pi_n {x : ℕ} : (pi_n x).subst nil.pl.subst0 = pi_n (φ := φ) (x + 1)
  := by
  simp only [pi_n, nil, pn, subst_pr]
  apply congrArg
  induction x with
  | zero => rfl
  | succ x ih => simp only [subst_pl, Function.iterate_succ_apply', ih]

def drop (x : ℕ) (e : Term φ) : Term φ := pl^[x] e

theorem Wf.pack_drop' {Γ Δ : Ctx α ε} {i : ℕ} (hi : i < Γ.length)
  : Wf (φ := φ) ((Γ.pack, ⊥)::Δ) (Term.pl^[i] (Term.var 0))
      ((Ctx.pack (Γ.drop (i + 1))).prod (Γ.get ⟨i, hi⟩).1, e)
  := by induction i generalizing Γ with
  | zero => cases Γ with
    | nil => cases hi
    | cons _ Γ => simp [pi_n, Ctx.pack]
  | succ i I => cases Γ with
    | nil => cases hi
    | cons head Γ =>
      simp only [BinSyntax.Term.pi_n, List.length_cons, Fin.val_succ, Function.iterate_succ',
        Function.comp_apply, List.get_eq_getElem, List.getElem_cons_succ, Ctx.pack]
      apply Wf.pl
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
  : Wf (φ := φ) ((Γ.pack, ⊥)::Δ) (Term.pl^[i] (Term.var 0)) (Ctx.pack (Γ.drop i), e)
  := by rw [Ctx.pack_drop hi]; apply Wf.pack_drop' hi

theorem Wf.pi_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : Wf (φ := φ) ((Γ.pack, ⊥)::Δ) (pi_n i) ((Γ.get i).1, e)
  := Wf.pr (pack_drop' i.prop)

def InS.pack_drop {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : InS φ ((Γ.pack, ⊥)::Δ) (Ctx.pack (Γ.drop i), e)
  := ⟨Term.pl^[i] (Term.var 0), Wf.pack_drop i.prop⟩

@[simp]
theorem InS.coe_pack_drop {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.pack_drop (φ := φ) (Δ := Δ) (e := e) i : Term φ) = Term.pl^[i] (Term.var 0) := rfl

def InS.pack_drop' {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : InS φ ((Γ.pack, ⊥)::Δ) ((Ctx.pack (Γ.drop (i + 1))).prod (Γ.get i).1, e)
  := ⟨Term.pl^[i] (Term.var 0), Wf.pack_drop' i.prop⟩

@[simp]
theorem InS.coe_pack_drop' {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.pack_drop' (φ := φ) (Δ := Δ) (e := e) i : Term φ) = Term.pl^[i] (Term.var 0) := rfl

theorem InS.cast_pack_drop {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.pack_drop (φ := φ) (Δ := Δ) (e := e) i).cast rfl (by rw [Ctx.pack_drop_fin]) = pack_drop' i
  := rfl

theorem InS.cast_pack_drop' {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.pack_drop' (φ := φ) (Δ := Δ) (e := e) i).cast rfl (by rw [<-Ctx.pack_drop_fin])
  = pack_drop i
  := rfl

def InS.pack_drop_succ {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : pack_drop (φ := φ)  (Γ := V::Γ) (Δ := Δ) (e := e) i.succ
  = (pack_drop' (φ := φ) (Γ := V::Γ) (Δ := Δ) (e := e) i.castSucc).pl := by
  ext; simp only [List.length_cons, Fin.val_succ, List.drop_succ_cons, Set.mem_setOf_eq,
    coe_pack_drop, Function.iterate_succ, Function.comp_apply, Term.pl, List.get_eq_getElem,
    Fin.coe_castSucc, coe_pl, coe_pack_drop']
  rw [<-Term.pl, <-Function.iterate_succ_apply, Function.iterate_succ_apply']
  rfl

def InS.pi_n {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : InS φ ((Γ.pack, ⊥)::Δ) ((Γ.get i).1, e)
  := ⟨Term.pi_n i, Wf.pi_n⟩

theorem InS.pl_pack_drop' {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.pack_drop' (φ := φ) (Δ := Δ) (e := e) i).pr = pi_n i := rfl

theorem InS.coe_pi_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.pi_n (φ := φ) (Δ := Δ) (e := e) i : Term φ) = Term.pi_n i := rfl

-- TODO: wk_lift pi_n

-- TODO: subst_lift pi_n

@[simp]
theorem InS.wk1_pi_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.pi_n (φ := φ) (Γ := Γ) (Δ := Δ) (e := e) i).wk1 (inserted := inserted) = pi_n i := by
  ext; rw [coe_pi_n, coe_wk1, coe_pi_n, Term.wk1_pi_n]

@[simp]
theorem InS.wk_lift_pi_n {Γ Δ : Ctx α ε} {i : Fin Γ.length} {ρ : Γ.InS Δ}
  : (InS.pi_n (φ := φ) (Γ := Γ) (Δ := Δ) (e := e) i).wk (ρ.lift (le_refl _)) = pi_n i := by
  ext; rw [coe_pi_n, coe_wk, coe_pi_n, Ctx.InS.coe_lift, Term.wk_lift_pi_n]

@[simp]
theorem InS.subst_lift_pi_n {Γ Δ Δ' : Ctx α ε} {i : Fin Γ.length} {σ : Subst.InS φ Δ' Δ}
  : (InS.pi_n (φ := φ) (Γ := Γ) (Δ := Δ) (e := e) i).subst (σ.lift (le_refl _)) = pi_n i := by
  ext; rw [coe_pi_n, coe_subst, coe_pi_n, Subst.InS.coe_lift, Term.subst_lift_pi_n]

@[simp]
theorem InS.subst0_nil_pl_pi_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (InS.pi_n (φ := φ) (Γ := Γ) (e := e) i).subst (nil.pl.subst0)
  = pi_n (φ := φ) (Γ := V::Γ) (Δ := Δ) i.succ := by ext; exact Term.subst0_nil_pl_pi_n

def pi_n' (n : ℕ) (i : ℕ) : Term φ := match n with
| 0 => unit
| n + 1 => let2 (var 0) (match i with | 0 => var 1 | i + 1 => pi_n' n i)

-- theorem Wf.pi_n' {Γ Δ : Ctx α ε} (i : Fin Γ.length)
--   : Wf (φ := φ) ((Γ.pack, ⊥)::Δ) (pi_n' Γ.length i) ((Γ.get i).1, e)
--   := by induction Γ generalizing Δ with
--   | nil => exact i.elim0
--   | cons V Γ I =>
--     apply Wf.let2
--     apply Wf.var (V := (V.1.prod (Ctx.pack Γ), e)); simp [Ctx.pack]
--     cases i using Fin.cases with
--     | zero => simp
--     | succ i =>
--       simp only [List.length_cons, Fin.val_succ, List.get_eq_getElem, List.getElem_cons_succ]
--       exact I i

-- def InS.pi_n' {Γ Δ : Ctx α ε} (i : Fin Γ.length) : InS φ ((Γ.pack, ⊥)::Δ) ((Γ.get i).1, e)
--   := match Γ with
--   | [] => i.elim0
--   | V::Γ => let2
--     (var (V := (V.1.prod (Ctx.pack Γ), e)) 0 (by simp [Ctx.pack]))
--     (i.cases (var 1 (by simp)) (λi => pi_n' (Γ := Γ) i))

-- @[simp]
-- theorem InS.coe_pi_n' {Γ Δ : Ctx α ε} {i : Fin Γ.length}
--   : (InS.pi_n' (φ := φ) (Δ := Δ) (e := e) i : Term φ) = Term.pi_n' Γ.length i := by
--   induction Γ generalizing Δ with
--   | nil => exact i.elim0
--   | cons V Γ I =>
--     simp only [List.get_eq_getElem, List.length_cons, Set.mem_setOf_eq, pi_n', Fin.val_zero,
--       List.getElem_cons_zero, InS.coe_let2, coe_var, Term.pi_n', let2.injEq, true_and]
--     cases i using Fin.cases with
--     | zero => rfl
--     | succ i => exact I

-- theorem InS.pi_n_zero' {Γ Δ : Ctx α ε}
--   : InS.pi_n' (φ := φ) (Γ := V::Γ) (Δ := Δ) (e := e) (by simp only [List.length_cons]; exact 0)
--   = (by simp only [Ctx.pack]; apply InS.pi_l) := rfl

-- theorem InS.pi_n_succ' {Γ Δ : Ctx α ε} {i : Fin Γ.length}
--   : InS.pi_n' (φ := φ) (Γ := V::Γ) (Δ := Δ) (e := e) i.succ
--   = let2
--     (var (V := (V.1.prod (Ctx.pack Γ), e)) 0 (by simp [Ctx.pack]))
--     (pi_n' (Γ := Γ) i) := rfl

def Subst.pi_n : Subst φ := λi => Term.pi_n i

theorem Subst.Wf.pi_n {Γ Δ : Ctx α ε}
  : Subst.Wf (φ := φ) ((Γ.pack, ⊥)::Δ) Γ Subst.pi_n := λ_ => Term.Wf.pi_n

def Subst.InS.unpack {Γ Δ : Ctx α ε} : Subst.InS φ ((Γ.pack, ⊥)::Δ) Γ := ⟨Subst.pi_n, Wf.pi_n⟩

@[simp]
theorem Subst.InS.coe_unpack {Γ Δ : Ctx α ε}
  : (Subst.InS.unpack (φ := φ) (Γ := Γ) (Δ := Δ) : Subst φ) = Subst.pi_n := rfl

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

def inj (ℓ : ℕ) (e : Term φ) : Term φ := inl^[ℓ] (inr e)

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
    | zero => exact Wf.inr $ h
    | succ i =>
      simp only [
        Fin.val_succ, Function.iterate_succ', Function.comp_apply, LCtx.pack,
        Wf.inl_iff, BinSyntax.Term.inj
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
  : Term.Wf (φ := φ) ((R.get i, ⊥)::Γ) (inj_n i) (R.pack, e)  := by
  induction R generalizing Γ with
  | nil => exact i.elim0
  | cons _ _ I =>
    cases i using Fin.cases with
    | zero => exact Wf.inr $ Wf.var Ctx.Var.bhead
    | succ i =>
      simp only [
        Fin.val_succ, BinSyntax.Term.inj_n, Function.iterate_succ', Function.comp_apply, LCtx.pack,
        Wf.inl_iff, BinSyntax.Term.inj
      ]
      apply I

def InS.inj_n {Γ : Ctx α ε} (R : LCtx α) (i : Fin R.length)
  : Term.InS φ ((R.get i, ⊥)::Γ) (R.pack, e) :=
  ⟨Term.inj_n i, Term.Wf.inj_n⟩

@[simp]
theorem InS.coe_inj_n {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : (InS.inj_n (φ := φ) (Γ := Γ) (R := R) (e := e) i : Term φ) = Term.inj_n i := rfl

@[simp]
theorem InS.wk_lift_inj_n {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {ρ : Γ.InS Δ}
  : (InS.inj_n (φ := φ) (e := e) R i).wk (ρ.lift (le_refl _)) = inj_n R i := by ext; simp

@[simp]
theorem InS.wk_slift_inj_n {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {ρ : Γ.InS Δ}
  : (InS.inj_n (φ := φ) (e := e) R i).wk (ρ.slift) = inj_n R i := by ext; simp

@[simp]
theorem InS.subst_lift_inj_n {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {σ : Subst.InS φ Γ Δ}
  : (InS.inj_n (φ := φ) (e := e) R i).subst (σ.lift (le_refl _)) = inj_n R i := by ext; simp

@[simp]
theorem InS.subst_slift_inj_n {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {σ : Subst.InS φ Γ Δ}
  : (InS.inj_n (φ := φ) (e := e) R i).subst σ.slift = inj_n R i := by ext; simp

@[simp]
theorem InS.wk1_inj_n {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : (InS.inj_n (φ := φ) (Γ := Γ) (e := e) R i).wk1 (inserted := inserted) = inj_n R i
  := by ext; simp

end Sum

-- section Arrow

-- def arr : Term φ → Term φ
-- | var x => pi_n x
-- | op f a => a.arr.seq (op f nil)
-- | let1 a b => let1 a.arr sorry
-- | pair a b => sorry
-- | let2 a b => sorry
-- | inl a => sorry
-- | inr a => sorry
-- | case a l r => sorry
-- | unit => sorry
-- | abort a => sorry

-- end Arrow
