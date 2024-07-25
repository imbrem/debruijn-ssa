import DeBruijnSSA.BinSyntax.Typing.Region.LSubst
import DeBruijnSSA.BinSyntax.Syntax.Compose.Region

namespace BinSyntax

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [OrderBot ε]
  {Γ Δ : Ctx α ε} {σ : Region.Subst φ}

namespace Region

theorem Wf.ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  {t : Term φ} (ht : t.Wf (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : (Region.ret t).Wf (⟨tyIn, ⊥⟩::rest) (tyOut::targets) := Wf.br ⟨by simp, le_refl _⟩ ht

def InS.ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (t : Term.InS φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : InS φ (⟨tyIn, ⊥⟩::rest) (tyOut::targets) := InS.br 0 t ⟨by simp, le_refl _⟩

theorem InS.ret_eq {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (t : Term.InS φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : InS.ret (targets := targets) t = ⟨Region.ret t, Wf.ret t.prop⟩ := rfl

theorem InS.vwk_ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (ρ : Ctx.InS (⟨tyIn, ⊥⟩::rest') _)
  (t : Term.InS φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : (InS.ret (targets := targets) t).vwk ρ = InS.ret (t.wk ρ) := rfl

theorem InS.vwk1_ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (t : Term.InS φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : (InS.ret (targets := targets) t).vwk1 (inserted := inserted)
  = InS.ret (t.wk ⟨Nat.liftWk Nat.succ, by simp⟩) := rfl

@[simp]
theorem InS.coe_ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (t : Term.InS φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : (InS.ret (targets := targets) t : Region φ) = Region.ret (t : Term φ) := rfl

theorem InS.vsubst_ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (σ : Term.Subst.InS φ (⟨tyIn, ⊥⟩::Γ) _)
  (t : Term.InS φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : (InS.ret (targets := targets) t).vsubst σ = InS.ret (t.subst σ) := rfl

theorem Wf.nil {ty : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  : Region.nil.Wf (φ := φ) (⟨ty, ⊥⟩::rest) (ty::targets) := Wf.ret (by simp)

def InS.nil {ty : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  : InS φ (⟨ty, ⊥⟩::rest) (ty::targets)  := InS.ret (Term.InS.var 0 (by simp))

theorem InS.nil_eq {ty : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  : InS.nil (φ := φ) (ty := ty) (rest := rest) (targets := targets) = ⟨Region.nil, Wf.nil⟩ := rfl

@[simp]
theorem InS.nil_vwk_lift (ρ : Ctx.InS rest _)
  : (InS.nil (φ := φ) (ty := ty) (rest := rest') (targets := targets)).vwk (ρ.lift h) = InS.nil
  := rfl

@[simp]
theorem InS.nil_vwk1
  : (InS.nil (φ := φ) (ty := ty) (rest := rest) (targets := targets)).vwk1 (inserted := inserted)
  = InS.nil := rfl

@[simp]
theorem InS.coe_nil {ty : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  : (InS.nil (φ := φ) (ty := ty) (rest := rest) (targets := targets) : Region φ)
  = Region.nil := rfl

def Wf.alpha0 {Γ : Ctx α ε} {L : LCtx α} {r : Region φ} (hr : r.Wf (⟨A, ⊥⟩::Γ) (B::L))
  : (r.alpha 0).Wf Γ (A::L) (B::L)
  := Fin.cases hr (λi => Wf.br ⟨Nat.succ_lt_succ i.prop, le_refl _⟩ (by simp))

def InS.alpha0 {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} (r : InS φ (⟨A, ⊥⟩::Γ) (B::L))
  : Subst.InS φ Γ (A::L) (B::L)
  := ⟨(r : Region φ).alpha 0, r.prop.alpha0⟩

@[simp]
theorem InS.coe_alpha0 {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} (r : InS φ (⟨A, ⊥⟩::Γ) (B::L))
  : (r.alpha0 : Region.Subst φ) = (r : Region φ).alpha 0 := rfl

theorem InS.vlift_alpha0 {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} (r : InS φ (⟨A, ⊥⟩::Γ) (B::L))
  : (InS.alpha0 r).vlift = InS.alpha0 (r.vwk1 (inserted := X)) := by
  simp only [Subst.InS.vlift, Set.mem_setOf_eq, alpha0, vlift_alpha]
  rfl

theorem InS.vsubst_alpha0 {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} (σ : Term.Subst.InS φ Γ Δ)
  (r : InS φ (⟨A, ⊥⟩::Δ) (B::L))
  : r.alpha0.vsubst σ = (r.vsubst (σ.lift (le_refl _))).alpha0
  := by ext k; cases k <;> rfl

def InS.seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) (C::L)) : InS φ (⟨A, ⊥⟩::Γ) (C::L)
  := left.lsubst right.vwk1.alpha0

instance InS.instHAppend {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : HAppend (InS φ (⟨A, ⊥⟩::Γ) (B::L)) (InS φ (⟨B, ⊥⟩::Γ) (C::L)) (InS φ (⟨A, ⊥⟩::Γ) (C::L)) where
  hAppend := InS.seq

theorem InS.append_def {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) (C::L))
  : left ++ right = left.lsubst right.vwk1.alpha0 := rfl

theorem InS.seq_def {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) (C::L))
  : left.seq right = left.lsubst right.vwk1.alpha0 := rfl

theorem InS.append_eq_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) (C::L))
  : left ++ right = left.seq right := rfl

theorem Wf.append {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l r : Region φ} (hl : l.Wf (⟨A, ⊥⟩::Γ) (B::L)) (hr : r.Wf (⟨B, ⊥⟩::Γ) (C::L))
  : (l ++ r).Wf (⟨A, ⊥⟩::Γ) (C::L)
  := (HAppend.hAppend (self := InS.instHAppend) (⟨l, hl⟩ : InS φ _ _) (⟨r, hr⟩ : InS φ _ _)).prop

theorem InS.append_mk {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l r : Region φ} (hl : l.Wf (⟨A, ⊥⟩::Γ) (B::L)) (hr : r.Wf (⟨B, ⊥⟩::Γ) (C::L))
  : HAppend.hAppend (self := InS.instHAppend) (⟨l, hl⟩ : InS φ _ _) (⟨r, hr⟩ : InS φ _ _)
  = ⟨l ++ r, hl.append hr⟩ := rfl

theorem InS.seq_mk {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l r : Region φ} (hl : l.Wf (⟨A, ⊥⟩::Γ) (B::L)) (hr : r.Wf (⟨B, ⊥⟩::Γ) (C::L))
  : seq ⟨l, hl⟩ ⟨r, hr⟩
  = ⟨l.seq r, hl.append hr⟩ := rfl

@[simp]
theorem InS.append_nil {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : InS φ (⟨A, ⊥⟩::Γ) (B::L)}
  : (l ++ InS.nil (φ := φ) (ty := B) (rest := Γ) (targets := L)) = l := by
  cases l; simp [nil_eq, append_mk, Region.append_nil]

@[simp]
theorem InS.seq_nil {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : InS φ (⟨A, ⊥⟩::Γ) (B::L)}
  : (l.seq (InS.nil (φ := φ) (ty := B) (rest := Γ) (targets := L))) = l := InS.append_nil

@[simp]
theorem InS.nil_append {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : InS φ (⟨A, ⊥⟩::Γ) (B::L)}
  : (InS.nil (φ := φ) (ty := A) (rest := Γ) (targets := L) ++ l) = l := by
  cases l; simp [nil_eq, append_mk, Region.nil_append]

@[simp]
theorem InS.nil_seq {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : InS φ (⟨A, ⊥⟩::Γ) (B::L)}
  : (InS.nil (φ := φ) (ty := A) (rest := Γ) (targets := L).seq l) = l := InS.nil_append

theorem InS.append_assoc {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L))
  (middle : InS φ (⟨B, ⊥⟩::Γ) (C::L))
  (right : InS φ (⟨C, ⊥⟩::Γ) (D::L))
  : (left ++ middle) ++ right = left ++ (middle ++ right) := by
  cases left; cases middle; cases right;
  simp [append_mk, Region.append_assoc]

theorem InS.seq_assoc {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L))
  (middle : InS φ (⟨B, ⊥⟩::Γ) (C::L))
  (right : InS φ (⟨C, ⊥⟩::Γ) (D::L))
  : (left.seq middle).seq right = left.seq (middle.seq right) := InS.append_assoc left middle right

@[simp]
theorem InS.coe_seq {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : InS φ (⟨A, ⊥⟩::Γ) (B::L)} {r : InS φ (⟨B, ⊥⟩::Γ) (C::L)}
  : ((l.seq r) : Region φ) = (l : Region φ).seq (r : Region φ) := rfl

@[simp]
theorem InS.coe_append {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : InS φ (⟨A, ⊥⟩::Γ) (B::L)} {r : InS φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (((l : InS φ (⟨A, ⊥⟩::Γ) (B::L)) ++ (r : InS φ (⟨B, ⊥⟩::Γ) (C::L))) : Region φ)
  = (l : Region φ) ++ (r : Region φ) := rfl

theorem Wf.left_exit {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
    : left_exit.Wf (φ := φ) (⟨A.coprod B, e⟩::Γ) (B::A::L) :=
  case (Term.Wf.var Ctx.Var.shead)
    (br (by simp) (Term.Wf.var Ctx.Var.shead))
    (br (by simp) (Term.Wf.var Ctx.Var.shead))

def InS.left_exit {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
    : InS φ (⟨A.coprod B, e⟩::Γ) (B::A::L)
  := case (Term.InS.var 0 Ctx.Var.shead)
    (br 1 (Term.InS.var 0 Ctx.Var.shead) (by simp))
    (br 0 (Term.InS.var 0 Ctx.Var.shead) (by simp))

@[simp]
theorem InS.coe_left_exit {Γ : Ctx α ε} {L : LCtx α} {A B : Ty α}
    : (InS.left_exit (φ := φ) (Γ := Γ) (L := L) (A := A) (B := B) (e := e) : Region φ)
    = Region.left_exit := rfl

theorem Wf.fixpoint {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} {r : Region φ}
  (hr : r.Wf (⟨A, ⊥⟩::Γ) ((B.coprod A)::L)) : (fixpoint r).Wf (⟨A, ⊥⟩::Γ) (B::L)
  := cfg 1 [A] rfl nil (Fin.elim1 (hr.vwk1.lwk1.append left_exit))

def InS.fixpoint {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} (r : InS φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  : InS φ (⟨A, ⊥⟩::Γ) (B::L) := cfg [A] nil (Fin.elim1 (r.vwk1.lwk1.seq left_exit))

@[simp]
theorem InS.coe_fixpoint {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {r : InS φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L)}
  : (r.fixpoint : Region φ) = (r : Region φ).fixpoint := by
  simp only [Set.mem_setOf_eq, fixpoint, List.append_eq, List.nil_append, List.length_singleton,
    List.get_eq_getElem, List.singleton_append, coe_cfg, coe_nil, Region.fixpoint, cfg.injEq,
    heq_eq_eq, true_and]
  ext i; cases i using Fin.elim1; rfl

theorem InS.vwk_fixpoint {A B : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {r : InS φ (⟨A, ⊥⟩::Δ) ((B.coprod A)::L)}
  {ρ : Ctx.InS Γ Δ}
  : r.fixpoint.vwk ρ.slift = (r.vwk ρ.slift).fixpoint := by
  ext
  sorry
