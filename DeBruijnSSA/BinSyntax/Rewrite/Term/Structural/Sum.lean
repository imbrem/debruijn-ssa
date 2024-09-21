import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Sum
import DeBruijnSSA.BinSyntax.Typing.Term.Structural


namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

set_option linter.unusedVariables false in
def Eqv.inj'
  {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} (a : Eqv φ Γ (R.get i, e)) : Eqv φ Γ (R.pack, e)
  := match R with
  | [] => i.elim0
  | _::R => by cases i using Fin.cases with | zero => exact a.inr | succ i => exact inl (inj' a)

@[simp]
theorem Eqv.inj_quot' {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {a : InS φ Γ (R.get i, e)}
  : Eqv.inj' ⟦a⟧ = ⟦Term.InS.inj a⟧ := by
  induction R generalizing Γ with
  | nil => exact i.elim0
  | cons _ _ I =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      simp only [inj', I, inl_quot, Fin.cases_succ]
      apply congrArg
      ext
      simp [Term.inj, Term.Wf.inj, -Function.iterate_succ, Function.iterate_succ']

def Eqv.inj
  {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} (a : Eqv φ Γ (R.get i, e)) : Eqv φ Γ (R.pack, e)
  := Quotient.liftOn a (λa => ⟦a.inj⟧) (λ_ _ h => by simp [<-Eqv.inj_quot', Quotient.sound h])

@[simp]
theorem Eqv.inj_quot {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {a : InS φ Γ (R.get i, e)}
  : Eqv.inj ⟦a⟧ = ⟦a.inj⟧ := rfl

theorem Eqv.inj_eq_inj' {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length} {a : Eqv φ Γ (R.get i, e)}
  : a.inj = Eqv.inj' a := by induction a using Quotient.inductionOn; rw [inj_quot']; rfl

@[simp]
theorem Eqv.wk_inj {Γ Δ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  {a : Eqv φ Δ (R.get i, e)} {ρ : Γ.InS Δ}
  : a.inj.wk ρ = (a.wk ρ).inj := by
  induction a using Quotient.inductionOn
  simp only [inj_quot, wk_quot]
  congr; ext; simp

@[simp]
theorem Eqv.wk0_inj {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  {a : Eqv φ Γ (R.get i, e)} : a.inj.wk0 (head := head) = (a.wk0).inj := wk_inj

@[simp]
theorem Eqv.wk1_inj {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  {a : Eqv φ (V::Γ) (R.get i, e)} : a.inj.wk1 (inserted := inserted) = (a.wk1).inj := wk_inj

@[simp]
theorem Eqv.subst_inj {Γ Δ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  {a : Eqv φ Δ (R.get i, e)} {σ : Subst.Eqv φ Γ Δ}
  : a.inj.subst σ = (a.subst σ).inj := by
  induction a using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  simp only [inj_quot, subst_quot]
  congr; ext; simp

@[simp]
theorem Eqv.inj_zero {Γ : Ctx α ε} {R : LCtx α}
  {a : Eqv φ Γ (List.get (A::R) (0 : Fin (R.length + 1)), e)}
  : a.inj = a.inr := rfl

theorem Eqv.inj_succ {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  {a : Eqv φ Γ (List.get (A::R) i.succ, e)}
  : a.inj = (a.inj (R := R)).inl := by rw [inj_eq_inj', inj_eq_inj']; rfl

def Eqv.inj_n {Γ : Ctx α ε} (R : LCtx α) (i : Fin R.length) : Eqv φ ((R.get i, ⊥)::Γ) (R.pack, e)
  := match R with
  | [] => i.elim0
  | _::R => i.cases (inr nil) (λi => inl (inj_n R i))

theorem Eqv.inj_n_def {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : Eqv.inj_n (φ := φ) (Γ := Γ) (e := e) R i = ⟦Term.InS.inj_n R i⟧ := by
  induction R generalizing Γ with
  | nil => exact i.elim0
  | cons _ _ I =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      simp only [inj_n, I, inl_quot, Fin.cases_succ]
      apply congrArg
      ext
      simp [Term.inj_n, Term.inj, Term.Wf.inj_n, -Function.iterate_succ, Function.iterate_succ']

theorem Eqv.inj_n_def' {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : Eqv.inj_n (φ := φ) (Γ := Γ) (e := e) R i = nil.inj := by rw [inj_n_def, nil, var, inj_quot]; rfl

theorem Eqv.wk1_inj_n {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : (inj_n (φ := φ) (Γ := Γ) (e := e) R i).wk1 (inserted := inserted) = inj_n R i := by
  rw [inj_n_def', wk1_inj, wk1_nil, inj_n_def']

theorem Eqv.seq_inj_n  {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  {a : Eqv φ ((X, ⊥)::Γ) (R.get i, e)}
  : a ;;' Eqv.inj_n R i = a.inj := by
  rw [seq, wk1_inj_n]
  induction R generalizing Γ with
  | nil => exact i.elim0
  | cons _ _ I =>
    cases i using Fin.cases with
    | zero => simp [inj_n, <-inr_let1, nil, let1_eta]
    | succ i => simp [inj_n, <-inl_let1, I, inj_succ]

def Eqv.pack_app_inr {Γ : Ctx α ε} {L R : LCtx α} : Eqv φ ((L.pack, ⊥)::Γ) ((L ++ R).pack, e)
  := match L with
  | [] => zero
  | _::_ => coprod (pack_app_inr ;;' inj_l) inj_r

def Eqv.pack_app_inl {Γ : Ctx α ε} {L R : LCtx α} : Eqv φ ((R.pack, ⊥)::Γ) ((L ++ R).pack, e)
  := match L with
  | [] => nil
  | _::_ => pack_app_inl ;;' inj_l

def Eqv.pack_app {Γ : Ctx α ε} {L R : LCtx α}
  : Eqv φ (((L ++ R).pack, ⊥)::Γ) (R.pack.coprod L.pack, e)
  := match L with
  | [] => inj_l
  | _::L => coprod (pack_app (L := L) ;;' sum nil inj_l) (inj_r ;;' inj_r)

@[simp]
theorem Eqv.wk_lift_pack_app {Γ Δ : Ctx α ε} {L R : LCtx α} {ρ : Γ.InS Δ}
  : (pack_app (φ := φ) (Γ := Δ) (L := L) (R := R) (e := e)).wk ρ.slift = pack_app := by
  induction L generalizing R with
  | nil => rfl
  | cons A L I => simp [pack_app, wk_lift_seq, Term.Eqv.wk_lift_coprod, Term.Eqv.sum, I]

@[simp]
theorem Eqv.wk1_pack_app {Γ : Ctx α ε} {L R : LCtx α}
  : (pack_app (φ := φ) (Γ := Γ) (L := L) (R := R) (e := e)).wk1 (inserted := inserted) = pack_app
  := by rw [wk1, <-Ctx.InS.lift_wk0, wk_lift_pack_app]

theorem Eqv.pack_app_coprod {Γ : Ctx α ε} {L R : LCtx α}
  : pack_app (φ := φ) (Γ := Γ) (L := L) (R := R) (e := e) ;;' coprod pack_app_inl pack_app_inr = nil
  := by induction L generalizing R with
  | nil => simp [pack_app, pack_app_inl, inj_l_coprod]
  | cons A L I =>
    simp only [List.cons_append, LCtx.pack.eq_2, pack_app, List.append_eq, coprod_seq, ← seq_assoc,
      sum_coprod, nil_seq, inj_r_coprod]
    simp [
      pack_app_inl, pack_app_inr, inj_l_coprod, inj_r_coprod, <-coprod_seq, seq_assoc, I,
      coprod_inl_inr
    ]

theorem Eqv.pack_app_inl_pack_app {Γ : Ctx α ε} {L R : LCtx α}
  : pack_app_inl ;;' pack_app (φ := φ) (Γ := Γ) (L := L) (R := R) (e := e) = inj_l
  := by induction L generalizing R with
  | nil => simp [pack_app_inl, pack_app, inj_l_coprod]
  | cons A L I =>
    simp only [LCtx.pack.eq_2, List.cons_append, pack_app_inl, pack_app, List.append_eq, ←
      seq_assoc, inj_l_coprod]
    rw [seq_assoc, I, sum, inj_l_coprod, nil_seq]

theorem Eqv.pack_app_inr_pack_app {Γ : Ctx α ε} {L R : LCtx α}
  : pack_app_inr ;;' pack_app (φ := φ) (Γ := Γ) (L := L) (R := R) (e := e) = inj_r
  := by induction L generalizing R with
  | nil => apply zero_eq
  | cons A L I =>
    simp [pack_app_inr, pack_app, coprod_seq, <-seq_assoc, inj_l_coprod, inj_r_coprod]
    rw [seq_assoc, I, sum, inj_r_coprod, <-coprod_seq, coprod_inl_inr, nil_seq]

theorem Eqv.coprod_pack_app {Γ : Ctx α ε} {L R : LCtx α}
  : coprod pack_app_inl pack_app_inr ;;' pack_app (φ := φ) (Γ := Γ) (L := L) (R := R) (e := e) = nil
  := by simp [coprod_seq, pack_app_inl_pack_app, pack_app_inr_pack_app, coprod_inl_inr]

end Term
