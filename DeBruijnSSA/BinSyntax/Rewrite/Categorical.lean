import DeBruijnSSA.BinSyntax.Rewrite.Subst
import DeBruijnSSA.BinSyntax.Syntax.Compose.Region

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

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

abbrev Eqv.ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (t : Term.InS φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : Eqv φ (⟨tyIn, ⊥⟩::rest) (tyOut::targets) := ⟦InS.ret t⟧

theorem Eqv.vwk_ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (ρ : Ctx.InS (⟨tyIn, ⊥⟩::rest') _)
  (t : Term.InS φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : (Eqv.ret (targets := targets) t).vwk ρ = Eqv.ret (t.wk ρ) := rfl

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
  : (InS.nil (φ := φ) (ty := ty) (rest := rest) (targets := targets)).vwk1 (right := right)
  = InS.nil := rfl

-- theorem InS.coe_nil {ty : Ty α} {rest: Ctx α ε} {targets : LCtx α}
--   : (InS.nil (ty := ty) (rest := rest) (targets := targets) : Region φ) = Region.nil := rfl

abbrev Eqv.nil {ty : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  : Eqv φ (⟨ty, ⊥⟩::rest) (ty::targets) := ⟦InS.nil⟧

@[simp]
theorem Eqv.nil_vwk_lift (ρ : Ctx.InS rest _)
  : (Eqv.nil (φ := φ) (ty := ty) (rest := rest') (targets := targets)).vwk (ρ.lift h) = Eqv.nil
  := rfl

@[simp]
theorem Eqv.nil_vwk_liftn₂ (ρ : Ctx.InS rest _)
  : (Eqv.nil (φ := φ) (ty := ty) (rest := (head'::rest')) (targets := targets)).vwk (ρ.liftn₂ h h')
  = Eqv.nil
  := rfl

theorem Eqv.nil_vwk1 {Γ : Ctx α ε} {L : LCtx α}
  : (Eqv.nil (φ := φ) (ty := ty) (rest := Γ) (targets := L)).vwk1 (inserted := inserted)
  = Eqv.nil := rfl

theorem Eqv.let1_0_nil
  : Eqv.let1 (Term.InS.var 0 ⟨by simp, le_refl _⟩) Eqv.nil
  = Eqv.nil (φ := φ) (ty := ty) (rest := rest) (targets := targets)
  := by rw [let1_beta]; rfl

def Wf.lsubst0 {Γ : Ctx α ε} {L : LCtx α} {r : Region φ} (hr : r.Wf (⟨A, ⊥⟩::Γ) L)
  : r.lsubst0.Wf Γ (A::L) L
  := Fin.cases hr (λi => Wf.br ⟨i.prop, le_refl _⟩ (by simp))

def InS.lsubst0 {A : Ty α} {Γ : Ctx α ε} {L : LCtx α} (r : InS φ (⟨A, ⊥⟩::Γ) L)
  : Subst.InS φ Γ (A::L) L
  := ⟨(r : Region φ).lsubst0, r.prop.lsubst0⟩

theorem InS.lsubst0_congr {A : Ty α} {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ (⟨A, ⊥⟩::Γ) L}
  (h : r ≈ r') : InS.lsubst0 r ≈ InS.lsubst0 r'
  := sorry

def Eqv.lsubst0 {A : Ty α} {Γ : Ctx α ε} {L : LCtx α} (r : Eqv φ (⟨A, ⊥⟩::Γ) L)
  : Subst.Eqv φ Γ (A::L) L
  := Quot.liftOn r (λr => ⟦InS.lsubst0 r⟧) (λ_ _ h => Quotient.sound $ InS.lsubst0_congr h)

def Wf.alpha0 {Γ : Ctx α ε} {L : LCtx α} {r : Region φ} (hr : r.Wf (⟨A, ⊥⟩::Γ) (B::L))
  : (r.alpha 0).Wf Γ (A::L) (B::L)
  := Fin.cases hr (λi => Wf.br ⟨Nat.succ_lt_succ i.prop, le_refl _⟩ (by simp))

def InS.alpha0 {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} (r : InS φ (⟨A, ⊥⟩::Γ) (B::L))
  : Subst.InS φ Γ (A::L) (B::L)
  := ⟨(r : Region φ).alpha 0, r.prop.alpha0⟩

theorem InS.alpha0_congr {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ (⟨A, ⊥⟩::Γ) (B::L)}
  (h : r ≈ r') : InS.alpha0 r ≈ InS.alpha0 r'
  := sorry

theorem InS.vlift_alpha0 {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} (r : InS φ (⟨A, ⊥⟩::Γ) (B::L))
  : (InS.alpha0 r).vlift = InS.alpha0 (r.vwk1 (right := X)) := by
  simp only [Subst.InS.vlift, Set.mem_setOf_eq, alpha0, vlift_alpha]
  rfl

def Eqv.alpha0 {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : Subst.Eqv φ Γ (A::L) (B::L)
  := Quot.liftOn r (λr => ⟦InS.alpha0 r⟧) (λ_ _ h => Quotient.sound $ InS.alpha0_congr h)

@[simp]
theorem Eqv.alpha0_quot {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} (r : InS φ (⟨A, ⊥⟩::Γ) (B::L))
  : Eqv.alpha0 ⟦r⟧ = ⟦InS.alpha0 r⟧ := rfl

theorem Eqv.vlift_alpha0 {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : (Eqv.alpha0 r).vlift = Eqv.alpha0 (r.vwk1 (inserted := X)) := by
  induction r using Quotient.inductionOn;
  rw [alpha0_quot, Subst.Eqv.vlift_quot, InS.vlift_alpha0]
  rfl

def InS.seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) (C::L)) : InS φ (⟨A, ⊥⟩::Γ) (C::L)
  := left.lsubst right.vwk1.alpha0

instance InS.instHAppend {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : HAppend (InS φ (⟨A, ⊥⟩::Γ) (B::L)) (InS φ (⟨B, ⊥⟩::Γ) (C::L)) (InS φ (⟨A, ⊥⟩::Γ) (C::L)) where
  hAppend := InS.seq

theorem InS.append_def {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) (C::L))
  : left ++ right = left.lsubst right.vwk1.alpha0 := rfl

theorem Wf.append {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l r : Region φ} (hl : l.Wf (⟨A, ⊥⟩::Γ) (B::L)) (hr : r.Wf (⟨B, ⊥⟩::Γ) (C::L))
  : (l ++ r).Wf (⟨A, ⊥⟩::Γ) (C::L)
  := (HAppend.hAppend (self := InS.instHAppend) (⟨l, hl⟩ : InS φ _ _) (⟨r, hr⟩ : InS φ _ _)).prop

theorem InS.append_mk {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l r : Region φ} (hl : l.Wf (⟨A, ⊥⟩::Γ) (B::L)) (hr : r.Wf (⟨B, ⊥⟩::Γ) (C::L))
  : HAppend.hAppend (self := InS.instHAppend) (⟨l, hl⟩ : InS φ _ _) (⟨r, hr⟩ : InS φ _ _)
  = ⟨l ++ r, hl.append hr⟩ := rfl

@[simp]
theorem InS.append_nil {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : InS φ (⟨A, ⊥⟩::Γ) (B::L)}
  : (l ++ InS.nil (φ := φ) (ty := B) (rest := Γ) (targets := L)) = l := by
  cases l; simp [nil_eq, append_mk, Region.append_nil]

@[simp]
theorem InS.nil_append {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : InS φ (⟨A, ⊥⟩::Γ) (B::L)}
  : (InS.nil (φ := φ) (ty := A) (rest := Γ) (targets := L) ++ l) = l := by
  cases l; simp [nil_eq, append_mk, Region.nil_append]

theorem InS.append_assoc {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L))
  (middle : InS φ (⟨B, ⊥⟩::Γ) (C::L))
  (right : InS φ (⟨C, ⊥⟩::Γ) (D::L))
  : (left ++ middle) ++ right = left ++ (middle ++ right) := by
  cases left; cases middle; cases right;
  simp [append_mk, Region.append_assoc]

-- theorem InS.let1_seq {Γ : Ctx α ε} {L : LCtx α}
--   (a : Term.InS φ (⟨A, ⊥⟩::Γ) ⟨X, e⟩)
--   (r : InS φ (⟨X, ⊥⟩::⟨A, ⊥⟩::Γ) (B::L)) (s : InS φ (⟨B, ⊥⟩::Γ) (C::L))
--   : (let1 a r) ++ s = let1 a (r ++ (s.vwk1 (right := ⟨X, ⊥⟩))) := by
--   induction r using Quotient.inductionOn;
--   induction s using Quotient.inductionOn;
--   sorry

def Eqv.seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)) : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)
  := left.lsubst right.vwk1.alpha0

instance Eqv.instHAppend {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : HAppend (Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (Eqv φ (⟨B, ⊥⟩::Γ) (C::L)) (Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) where
  hAppend := Eqv.seq

infixl:65 " ;; "  => Eqv.seq

theorem Eqv.seq_def {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : left ;; right = left.lsubst right.vwk1.alpha0 := rfl

@[simp]
theorem Eqv.seq_quot {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) (C::L))
  : ⟦left⟧ ;; ⟦right⟧ = ⟦left ++ right⟧
  := rfl

@[simp]
theorem InS.append_q {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) (C::L))
  : left.q ++ right.q = (left ++ right).q
  := rfl

@[simp]
theorem InS.seq_q {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) (C::L))
  : left.q ;; right.q = (left ++ right).q
  := rfl

theorem Eqv.seq_nil {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : left ;; Eqv.nil = left := by
  induction left using Quotient.inductionOn;
  simp [nil]

theorem Eqv.nil_seq {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : Eqv.nil ;; left = left := by
  induction left using Quotient.inductionOn;
  simp [nil]

theorem Eqv.seq_assoc {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  (middle : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  (right : Eqv φ (⟨C, ⊥⟩::Γ) (D::L))
  : (left ;; middle) ;; right = left ;; (middle ;; right) := by
  induction left using Quotient.inductionOn;
  induction middle using Quotient.inductionOn;
  induction right using Quotient.inductionOn;
  simp [InS.append_assoc]

theorem Eqv.ret_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩)
  (r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : (Eqv.ret a) ;; r = r.vwk1.vsubst a.subst0 := by
  induction r using Quotient.inductionOn;
  simp only [ret, seq_def, vwk1_quot, alpha0_quot, lsubst_quot, vsubst_quot]
  rfl

theorem Eqv.ret_seq_let {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩)
  (r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : (Eqv.ret a) ;; r = let1 a r.vwk1 := by rw [ret_seq, let1_beta]

theorem Eqv.let1_seq {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ (⟨A, ⊥⟩::Γ) ⟨X, e⟩)
  (r : Eqv φ (⟨X, ⊥⟩::⟨A, ⊥⟩::Γ) (B::L)) (s : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : (Eqv.let1 a r) ;; s = Eqv.let1 a (r ;; s.vwk1) := by
  simp only [seq_def, lsubst_let1, vlift_alpha0]

theorem Eqv.let2_seq {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ (⟨A, ⊥⟩::Γ) ⟨X.prod Y, e⟩)
  (r : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::⟨A, ⊥⟩::Γ) (C::L)) (s : Eqv φ (⟨C, ⊥⟩::Γ) (D::L))
  : (Eqv.let2 a r) ;; s = Eqv.let2 a (r ;; s.vwk1.vwk1) := by
  simp only [seq_def, lsubst_let2, Subst.Eqv.vliftn₂_eq_vlift_vlift, vlift_alpha0]

theorem Eqv.case_seq {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.InS φ (⟨A, ⊥⟩::Γ) ⟨X.coprod Y, e⟩)
  (r : Eqv φ (⟨X, ⊥⟩::⟨A, ⊥⟩::Γ) (B::L)) (s : Eqv φ (⟨Y, ⊥⟩::⟨A, ⊥⟩::Γ) (B::L))
  (t : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : (Eqv.case a r s) ;; t = Eqv.case a (r ;; t.vwk1) (s ;; t.vwk1) := by
  simp only [seq_def, lsubst_case, vlift_alpha0]

theorem Eqv.vwk_lift_seq {A B C : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  (ρ : Ctx.InS Γ Δ)
  (left : Eqv φ (⟨A, ⊥⟩::Δ) (B::L))
  (right : Eqv φ (⟨B, ⊥⟩::Δ) (C::L))
  : (left ;; right).vwk (ρ.lift (le_refl _))
  = left.vwk (ρ.lift (le_refl _)) ;; right.vwk (ρ.lift (le_refl _)) := by
  induction left using Quotient.inductionOn;
  induction right using Quotient.inductionOn;
  sorry

theorem Eqv.vwk_liftn₂_seq {A B C : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  (ρ : Ctx.InS Γ Δ)
  (left : Eqv φ (⟨A, ⊥⟩::X::Δ) (B::L))
  (right : Eqv φ (⟨B, ⊥⟩::X::Δ) (C::L))
  : (left ;; right).vwk (ρ.liftn₂ (le_refl _) (le_refl _))
  = left.vwk (ρ.liftn₂ (le_refl _) (le_refl _)) ;; right.vwk (ρ.liftn₂ (le_refl _) (le_refl _))
  := by simp only [<-Ctx.InS.lift_lift, vwk_lift_seq]

theorem Eqv.vwk1_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  (right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : (left ;; right).vwk1 (inserted := inserted)
  = left.vwk1 ;; right.vwk1 := vwk_lift_seq ⟨Nat.succ, (by simp)⟩ left right

theorem Eqv.vsubst_lift_seq {A B C : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  (σ : Term.Subst.InS φ Γ Δ)
  (left : Eqv φ (⟨A, ⊥⟩::Δ) (B::L))
  (right : Eqv φ (⟨B, ⊥⟩::Δ) (C::L))
  : (left ;; right).vsubst (σ.lift (le_refl _))
  = left.vsubst (σ.lift (le_refl _)) ;; right.vsubst (σ.lift (le_refl _)) := by
  induction left using Quotient.inductionOn;
  induction right using Quotient.inductionOn;
  sorry

theorem Eqv.vsubst_liftn₂_seq {A B C : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  (σ : Term.Subst.InS φ Γ Δ)
  (left : Eqv φ (⟨A, ⊥⟩::X::Δ) (B::L))
  (right : Eqv φ (⟨B, ⊥⟩::X::Δ) (C::L))
  : (left ;; right).vsubst (σ.liftn₂ (le_refl _) (le_refl _))
  = left.vsubst (σ.liftn₂ (le_refl _) (le_refl _)) ;; right.vsubst (σ.liftn₂ (le_refl _) (le_refl _))
  := by simp only [<-Term.Subst.InS.lift_lift, vsubst_lift_seq]

open Term.InS

def Eqv.rtimes {tyIn tyOut : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (tyLeft : Ty α) (r : Eqv φ (⟨tyIn, ⊥⟩::Γ) (tyOut::L))
  : Eqv φ (⟨tyLeft.prod tyIn, ⊥⟩::Γ) ((tyLeft.prod tyOut)::L)
  := Eqv.let2 (var 0 Ctx.Var.shead) $
  r.vwk1.vwk1 ;;
  ret (pair (var 1 (by simp)) (var 0 (by simp)))

def Eqv.swap {left right : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨left.prod right, ⊥⟩::Γ) ((right.prod left)::L)
  := Eqv.let2 (var 0 Ctx.Var.shead) $
  ret (pair (var 0 (by simp)) (var 1 (by simp)))

theorem Eqv.repack {left right : Ty α} {rest : Ctx α ε} {targets : LCtx α}
  : Eqv.let2 (Term.InS.var 0 ⟨by simp, le_refl _⟩)
    (Eqv.ret (Term.InS.pair (Term.InS.var 1 (by simp)) (Term.InS.var 0 (by simp))))
  = Eqv.nil (φ := φ) (ty := left.prod right) (rest := rest) (targets := targets) := by
  rw [<-let1_0_nil, <-let2_eta, let1_beta]
  rfl

theorem Eqv.swap_swap {left right : Ty α}
  : Eqv.swap ;; Eqv.swap
  = (Eqv.nil (φ := φ) (ty := left.prod right) (rest := rest) (targets := targets)) := by
  simp only [
    swap, let2_seq, vwk1, vwk_let2, wk_var, wk_pair, Nat.liftWk, vwk_ret, Ctx.InS.liftn₂,
    Nat.liftnWk, Nat.one_lt_ofNat, Nat.ofNat_pos, ↓reduceIte, ret_seq, vsubst_let2,
    subst_pair, subst_var, Term.Subst.InS.get_0_subst0, let2_pair, let1_beta, vsubst_vsubst
  ]
  apply Eqv.repack

infixl:70 " ⋊ "  => Eqv.rtimes

theorem Eqv.rtimes_nil {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (tyLeft : Ty α)
  : tyLeft ⋊ Eqv.nil = (Eqv.nil (φ := φ) (ty := tyLeft.prod ty) (rest := Γ) (targets := L)) := by
  simp only [rtimes, nil_vwk1, nil_seq, repack]

theorem Eqv.rtimes_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (tyLeft : Ty α) (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (s : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : tyLeft ⋊ (r ;; s) = (tyLeft ⋊ r) ;; (tyLeft ⋊ s) := by
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
  := Eqv.swap ;; tyRight ⋊ r ;; Eqv.swap

infixl:70 " ⋉ "  => Eqv.ltimes

theorem Eqv.swap_rtimes_swap {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : Eqv.swap ;; C ⋊ r ;; Eqv.swap = r ⋉ C
  := rfl

theorem Eqv.swap_ltimes {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : Eqv.swap ;; r ⋉ C = C ⋊ r ;; Eqv.swap
  := by rw [<-swap_rtimes_swap, <-seq_assoc, <-seq_assoc, swap_swap, nil_seq]

theorem Eqv.swap_ltimes_swap {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : Eqv.swap ;; r ⋉ C ;; Eqv.swap = C ⋊ r
  := by rw [
    ltimes, seq_assoc, seq_assoc, swap_swap, seq_assoc, seq_nil, <-seq_assoc, swap_swap, nil_seq]

theorem Eqv.ltimes_nil {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.nil ⋉ tyRight = (Eqv.nil (φ := φ) (ty := ty.prod tyRight) (rest := Γ) (targets := L))
  := by rw [<-swap_rtimes_swap, rtimes_nil, seq_nil, swap_swap]

theorem Eqv.ltimes_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (s : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : (r ;; s) ⋉ tyRight = (r ⋉ tyRight) ;; (s ⋉ tyRight) := by
  simp only [<-swap_rtimes_swap, rtimes_seq, seq_assoc]
  rw [<-seq_assoc swap swap, swap_swap, nil_seq]

end Region

end BinSyntax
