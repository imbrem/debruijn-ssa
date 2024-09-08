import DeBruijnSSA.BinSyntax.Rewrite.Region.LSubst
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Seq
import DeBruijnSSA.BinSyntax.Typing.Region.Compose

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

abbrev Eqv.ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (t : Term.Eqv φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : Eqv φ (⟨tyIn, ⊥⟩::rest) (tyOut::targets)
  := Eqv.br 0 t (by simp)

theorem Eqv.vwk_ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (ρ : Ctx.InS (⟨tyIn', ⊥⟩::rest') _)
  (t : Term.Eqv φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : (Eqv.ret (targets := targets) t).vwk ρ = Eqv.ret (t.wk ρ) := by
  induction t using Quotient.inductionOn
  rfl

theorem Eqv.vwk1_ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (t : Term.Eqv φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : (ret (targets := targets) t).vwk1 (inserted := inserted) = ret t.wk1 := by
  induction t using Quotient.inductionOn
  rfl

theorem Eqv.vsubst_ret {tyIn tyIn' tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (σ : Term.Subst.Eqv φ (⟨tyIn, ⊥⟩::Γ) _)
  (t : Term.Eqv φ (⟨tyIn', ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : (ret (targets := targets) t).vsubst σ = ret (t.subst σ) := by
  induction σ using Quotient.inductionOn
  induction t using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.lwk_lift_ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (ρ : LCtx.InS targets targets')
  (t : Term.Eqv φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : (ret (targets := targets) t).lwk ρ.slift = ret t := by
  induction t using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.lwk1_ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (t : Term.Eqv φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : (ret (targets := targets) t).lwk1 (inserted := inserted) = ret t := by
  induction t using Quotient.inductionOn
  rfl

theorem Eqv.br_zero_eq_ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (t : Term.Eqv φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  (hℓ : LCtx.Trg (tyOut'::targets) 0 tyOut)
  : br 0 t hℓ = ret (t.wk_res (by simp [hℓ.get0]))
  := by induction t using Quotient.inductionOn; rfl

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

@[simp]
theorem Eqv.nil_lwk1 {Γ : Ctx α ε} {L : LCtx α}
  : (Eqv.nil (φ := φ) (ty := ty) (rest := Γ) (targets := L)).lwk1 (inserted := inserted)
  = Eqv.nil := rfl

theorem Eqv.let1_0_nil
  : Eqv.let1 (Term.Eqv.var 0 ⟨by simp, le_refl _⟩) Eqv.nil
  = Eqv.nil (φ := φ) (ty := ty) (rest := rest) (targets := targets)
  := by rw [let1_beta]; rfl

theorem InS.lsubst0_congr {A : Ty α} {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ (⟨A, ⊥⟩::Γ) L}
  (h : r ≈ r') : InS.lsubst0 r ≈ InS.lsubst0 r'
  | ⟨0, _⟩ => by simp [Subst.InS.get, InS.lsubst0, Region.lsubst0, h]
  | ⟨n + 1, h⟩ =>  by simp [Subst.InS.get, InS.lsubst0, Region.lsubst0, Setoid.refl]

def Eqv.lsubst0 {A : Ty α} {Γ : Ctx α ε} {L : LCtx α} (r : Eqv φ (⟨A, ⊥⟩::Γ) L)
  : Subst.Eqv φ Γ (A::L) L
  := Quot.liftOn r (λr => ⟦InS.lsubst0 r⟧) (λ_ _ h => Quotient.sound $ InS.lsubst0_congr h)

theorem InS.alpha0_congr {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ (⟨A, ⊥⟩::Γ) (B::L)}
  (h : r ≈ r') : InS.alpha0 r ≈ InS.alpha0 r'
  | ⟨0, _⟩ => by simp [Subst.InS.get, Region.alpha, h]
  | ⟨n + 1, h⟩ =>  by simp [Subst.InS.get, Region.alpha, Setoid.refl]

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

theorem Eqv.get_alpha0 {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) {i}
  : (Eqv.alpha0 r).get i = Fin.cases r (λi => Eqv.br (i + 1) Term.Eqv.nil ⟨by simp, by simp⟩) i
    := by induction r using Quotient.inductionOn; cases i using Fin.cases <;> rfl

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

@[simp]
theorem Eqv.seq_nil {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : left ;; Eqv.nil = left := by
  induction left using Quotient.inductionOn;
  simp [nil]

@[simp]
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
  (a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩)
  (r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : (Eqv.ret a) ;; r = r.vwk1.vsubst a.subst0 := by
  induction a using Quotient.inductionOn;
  induction r using Quotient.inductionOn;
  simp only [ret, seq_def, vwk1_quot, alpha0_quot, lsubst_quot, vsubst_quot]
  rfl

theorem Eqv.ret_seq_let {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩)
  (r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : (Eqv.ret a) ;; r = let1 a r.vwk1 := by rw [ret_seq, let1_beta]

theorem Eqv.let1_seq {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨X, e⟩)
  (r : Eqv φ (⟨X, ⊥⟩::⟨A, ⊥⟩::Γ) (B::L)) (s : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : (Eqv.let1 a r) ;; s = Eqv.let1 a (r ;; s.vwk1) := by
  simp only [seq_def, lsubst_let1, vlift_alpha0]

theorem Eqv.let2_seq {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨X.prod Y, e⟩)
  (r : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::⟨A, ⊥⟩::Γ) (C::L)) (s : Eqv φ (⟨C, ⊥⟩::Γ) (D::L))
  : (Eqv.let2 a r) ;; s = Eqv.let2 a (r ;; s.vwk1.vwk1) := by
  simp only [seq_def, lsubst_let2, Subst.Eqv.vliftn₂_eq_vlift_vlift, vlift_alpha0]

theorem Eqv.case_seq {Γ : Ctx α ε} {L : LCtx α}
  (a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨X.coprod Y, e⟩)
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
  apply Eqv.eq_of_reg_eq
  simp only [Set.mem_setOf_eq, InS.coe_vwk, Ctx.InS.coe_lift, InS.coe_lsubst, InS.coe_alpha0,
    Ctx.InS.coe_wk1, vwk_liftWk_lsubst_alpha, Region.vwk_vwk]
  congr
  apply congrArg
  congr
  funext k
  cases k <;> rfl

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

theorem Eqv.vwk2_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : Eqv φ (⟨A, ⊥⟩::X::Γ) (B::L))
  (right : Eqv φ (⟨B, ⊥⟩::X::Γ) (C::L))
  : (left ;; right).vwk2 (inserted := inserted)
  = left.vwk2 ;; right.vwk2 := by
  simp only [vwk2, <-Ctx.InS.lift_wk1, vwk_lift_seq]

theorem Eqv.vsubst_lift_seq {A B C : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  (σ : Term.Subst.Eqv φ Γ Δ)
  (left : Eqv φ (⟨A, ⊥⟩::Δ) (B::L))
  (right : Eqv φ (⟨B, ⊥⟩::Δ) (C::L))
  : (left ;; right).vsubst (σ.lift (le_refl _))
  = left.vsubst (σ.lift (le_refl _)) ;; right.vsubst (σ.lift (le_refl _)) := by
  induction left using Quotient.inductionOn;
  induction right using Quotient.inductionOn;
  induction σ using Quotient.inductionOn;
  apply Eqv.eq_of_reg_eq
  simp only [Set.mem_setOf_eq, InS.coe_vsubst, Term.Subst.InS.coe_lift, InS.coe_lsubst,
    InS.coe_alpha0, InS.coe_vwk, Ctx.InS.coe_wk1, vsubst_lift_lsubst_alpha,
    <-Region.vsubst_fromWk, Region.vsubst_vsubst]
  congr
  apply congrArg
  congr
  funext k
  cases k with
  | zero => rfl
  | succ k => simp [Term.Subst.comp, Term.subst_fromWk, Term.wk_wk, Term.Subst.liftn]

theorem Eqv.vsubst_liftn₂_seq {A B C : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  (σ : Term.Subst.Eqv φ Γ Δ)
  (left : Eqv φ (⟨A, ⊥⟩::X::Δ) (B::L))
  (right : Eqv φ (⟨B, ⊥⟩::X::Δ) (C::L))
  : (left ;; right).vsubst (σ.liftn₂ (le_refl _) (le_refl _))
  = left.vsubst (σ.liftn₂ (le_refl _) (le_refl _))
  ;; right.vsubst (σ.liftn₂ (le_refl _) (le_refl _)) := by
  simp only [<-Term.Subst.Eqv.lift_lift, vsubst_lift_seq]

theorem Eqv.let1_ret {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩} {b : Term.Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, ⊥⟩}
  : let1 a (ret (targets := L) b) = ret (Term.Eqv.let1 a b) := let1_br

theorem Eqv.let2_ret
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B.prod C, ⊥⟩} {b : Term.Eqv φ (⟨C, ⊥⟩::⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨D, ⊥⟩}
  : let2 a (ret (targets := L) b) = ret (Term.Eqv.let2 a b) := let2_br

theorem Eqv.case_ret
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B.coprod C, ⊥⟩}
  {l : Term.Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨D, ⊥⟩}
  {r : Term.Eqv φ (⟨C, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨D, ⊥⟩}
  : case a (ret (targets := L) l) (ret r) = ret (Term.Eqv.case a l r) := case_br

theorem Eqv.ret_br {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩} {b : Term.Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, ⊥⟩} {hℓ : LCtx.Trg (D::L) ℓ C}
  : ret (targets := L) a ;; br ℓ b hℓ = br ℓ (a ;;' b) hℓ := by
  rw [ret_seq, Term.Eqv.seq, Term.Eqv.let1_beta_pure, vwk1_br, vsubst_br]

theorem Eqv.br_of_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩} {b : Term.Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, ⊥⟩} {hℓ : LCtx.Trg (D::L) ℓ C}
  : br ℓ (a ;;' b) hℓ = ret (targets := L) a ;; br ℓ b hℓ := ret_br.symm

@[simp]
theorem Eqv.br_succ_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩} {hℓ : LCtx.Trg (C::L) (ℓ + 1) B}
  {r : Eqv φ (⟨C, ⊥⟩::Γ) (D::L)}
  : br (ℓ + 1) a hℓ ;; r = br (ℓ + 1) a hℓ.tail.step
  := by
  induction a using Quotient.inductionOn;
  induction r using Quotient.inductionOn;
  rfl

theorem Eqv.br_succ_seq_eq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩} {hℓ : LCtx.Trg (C::L) (ℓ + 1) B}
  {r r' : Eqv φ (⟨C, ⊥⟩::Γ) (D::L)}
  : br (ℓ + 1) a hℓ ;; r = br (ℓ + 1) a hℓ ;; r'
  := by rw [br_succ_seq, br_succ_seq]

theorem Eqv.ret_ret {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩}
  {b : Term.Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, ⊥⟩}
  : ret (targets := L) a ;; ret b = ret (a ;;' b) := ret_br

theorem Eqv.ret_of_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩}
  {b : Term.Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, ⊥⟩}
  : ret (a ;;' b) = ret (targets := L) a ;; ret b := ret_ret.symm

theorem Eqv.ret_nil : ret Term.Eqv.nil = nil (φ := φ) (ty := A) (rest := Γ) (targets := L)  := rfl

theorem Eqv.ret_var_zero {Γ : Ctx α ε} {L : LCtx α}
  : ret (Term.Eqv.var 0 ⟨by simp, le_refl _⟩)
  = nil (φ := φ) (ty := A) (rest := Γ) (targets := L) := rfl

@[simp]
theorem Eqv.ret_lsubst_slift
   {σ : Subst.Eqv φ _ targets targets'} {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩}
  : (Eqv.ret a (targets := targets)).lsubst σ.slift = Eqv.ret a
  := by induction a using Quotient.inductionOn; induction σ using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.nil_lsubst_slift (σ : Subst.Eqv φ _ targets targets')
  : (Eqv.nil (φ := φ) (ty := ty) (rest := rest) (targets := targets)).lsubst σ.slift = Eqv.nil
  := by rw [<-ret_nil, ret_lsubst_slift]; rfl

def Eqv.wseq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)) : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)
  := cfg [B] left.lwk1 (Fin.elim1 right.lwk0.vwk1)

@[simp]
theorem Eqv.wseq_quot {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) (C::L))
  : wseq ⟦left⟧ ⟦right⟧ = ⟦left.wseq right⟧ := cfg1_quot

def Eqv.wrseq {B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : Eqv φ Γ (B::L)) (right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)) : Eqv φ Γ (C::L)
  := cfg [B] left.lwk1 (Fin.elim1 right.lwk0)

@[simp]
theorem Eqv.wrseq_quot {B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ Γ (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) (C::L))
  : wrseq ⟦left⟧ ⟦right⟧ = ⟦left.wrseq right⟧ := cfg1_quot

theorem Eqv.wseq_eq_wrseq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)} {right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : left.wseq right = left.wrseq right.vwk1 := by
  induction left using Quotient.inductionOn;
  induction right using Quotient.inductionOn;
  simp [InS.wseq_eq_wrseq]

def Eqv.wthen {B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : Eqv φ Γ (B::L)) (right : Eqv φ (⟨B, ⊥⟩::Γ) L) : Eqv φ Γ L
  := cfg [B] left (Fin.elim1 right.lwk0)

@[simp]
theorem Eqv.wthen_quot {B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ Γ (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ)  L)
  : wthen ⟦left⟧ ⟦right⟧ = ⟦left.wthen right⟧ := cfg1_quot

theorem Eqv.wseq_eq_wthen {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)} {right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : left.wseq right = left.lwk1.wthen right.vwk1 := by
  induction left using Quotient.inductionOn;
  induction right using Quotient.inductionOn;
  simp [InS.wseq_eq_wthen]

theorem Eqv.wrseq_eq_wthen {B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {left : Eqv φ Γ (B::L)} {right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : left.wrseq right = left.lwk1.wthen right := by
  induction left using Quotient.inductionOn;
  induction right using Quotient.inductionOn;
  simp [InS.wrseq_eq_wthen]

theorem Eqv.vwk_lift_wseq {A B C : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {ρ : Ctx.InS Γ Δ}
  {left : Eqv φ (⟨A, ⊥⟩::Δ) (B::L)}
  {right : Eqv φ (⟨B, ⊥⟩::Δ) (C::L)}
  : (left.wseq right).vwk (ρ.lift (le_refl _))
  = (left.vwk (ρ.lift (le_refl _))).wseq (right.vwk (ρ.lift (le_refl _))) := by
  induction left using Quotient.inductionOn;
  induction right using Quotient.inductionOn;
  simp only [wseq_quot, vwk_quot, seq_quot, InS.vwk_lift_wseq]

theorem Eqv.vwk_slift_wseq {A B C : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {ρ : Ctx.InS Γ Δ}
  {left : Eqv φ (⟨A, ⊥⟩::Δ) (B::L)}
  {right : Eqv φ (⟨B, ⊥⟩::Δ) (C::L)}
  : (left.wseq right).vwk ρ.slift
  = (left.vwk ρ.slift).wseq (right.vwk ρ.slift) := vwk_lift_wseq

theorem Eqv.lwk_lift_wseq {A B C : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
  {ρ : LCtx.InS L K}
  {left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)}
  {right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (left.wseq right).lwk (ρ.lift (le_refl _))
  = (left.lwk (ρ.lift (le_refl _))).wseq (right.lwk (ρ.lift (le_refl _))) := by
  induction left using Quotient.inductionOn;
  induction right using Quotient.inductionOn;
  simp only [wseq_quot, lwk_quot, seq_quot, InS.lwk_lift_wseq]

theorem Eqv.lwk_slift_wseq {A B C : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
  {ρ : LCtx.InS L K}
  {left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)}
  {right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (left.wseq right).lwk ρ.slift
  = (left.lwk ρ.slift).wseq (right.lwk ρ.slift) := lwk_lift_wseq

theorem Eqv.vwk_wrseq {B C : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {ρ : Ctx.InS Γ Δ}
  {left : Eqv φ Δ (B::L)}
  {right : Eqv φ (⟨B, ⊥⟩::Δ) (C::L)}
  : (left.wrseq right).vwk ρ
  = (left.vwk ρ).wrseq (right.vwk ρ.slift) := by
  induction left using Quotient.inductionOn;
  induction right using Quotient.inductionOn;
  simp only [wrseq_quot, vwk_quot, InS.vwk_wrseq]

theorem Eqv.lwk_lift_wrseq {B C : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
  {ρ : LCtx.InS L K}
  {left : Eqv φ Γ (B::L)}
  {right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (left.wrseq right).lwk (ρ.lift (le_refl _))
  = (left.lwk (ρ.lift (le_refl _))).wrseq (right.lwk (ρ.lift (le_refl _))) := by
  induction left using Quotient.inductionOn;
  induction right using Quotient.inductionOn;
  simp only [wrseq_quot, lwk_quot, InS.lwk_lift_wrseq]

theorem Eqv.lwk_slift_wrseq {B C : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
  {ρ : LCtx.InS L K}
  {left : Eqv φ Γ (B::L)}
  {right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (left.wrseq right).lwk ρ.slift
  = (left.lwk ρ.slift).wrseq (right.lwk ρ.slift) := lwk_lift_wrseq

theorem Eqv.vwk_wthen {B : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {ρ : Ctx.InS Γ Δ}
  {left : Eqv φ Δ (B::L)}
  {right : Eqv φ (⟨B, ⊥⟩::Δ) L}
  : (left.wthen right).vwk ρ
  = (left.vwk ρ).wthen (right.vwk ρ.slift) := by
  induction left using Quotient.inductionOn;
  induction right using Quotient.inductionOn;
  simp only [wthen_quot, vwk_quot, InS.vwk_wthen]

theorem Eqv.lwk_wthen {B : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
  {ρ : LCtx.InS L K}
  {left : Eqv φ Γ (B::L)}
  {right : Eqv φ (⟨B, ⊥⟩::Γ) L}
  : (left.wthen right).lwk ρ
  = (left.lwk ρ.slift).wthen (right.lwk ρ) := by
  induction left using Quotient.inductionOn;
  induction right using Quotient.inductionOn;
  simp only [wthen_quot, lwk_quot, InS.lwk_wthen]

theorem Eqv.wseq_eq_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)} {right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : left.wseq right = left ;; right := by
  rw [wseq, cfg_eq_ucfg', ucfg', seq, lwk1, <-lsubst_toSubstE, lsubst_lsubst]
  congr
  ext k
  cases k using Fin.cases with
  | zero =>
    simp only [List.get_eq_getElem, List.length_cons, Fin.val_zero, List.getElem_cons_zero,
      List.singleton_append, List.length_singleton, Subst.Eqv.get_comp, Subst.Eqv.get_toSubstE,
      Set.mem_setOf_eq, LCtx.InS.coe_wk1, Nat.liftWk_zero, lsubst_br, id_eq, Fin.zero_eta,
      Subst.Eqv.get_vlift, cfgSubst'_get, zero_lt_one, ↓reduceDIte, vwk1_cfg, vwk1_br,
      Term.Eqv.wk1_var0, vwk_id_eq, vsubst_cfg, vsubst_br, Term.Eqv.var0_subst0,
      Term.Eqv.wk_res_self, List.length_nil, Nat.zero_add, get_alpha0, Fin.cases_zero]
    rw [cfg_br_lt (hℓ' := by simp), let1_beta, cfg_eq_ucfg', ucfg']
    simp only [List.singleton_append, Nat.reduceAdd, List.length_singleton, Nat.zero_eq,
      Fin.zero_eta, Fin.isValue, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
      Fin.elim1_zero, vwk_id_eq, vwk1_vwk2]
    simp only [vwk1_lwk0, vsubst_lwk0]
    simp only [lwk0, <-lsubst_toSubstE, lsubst_lsubst]
    rw [lsubst_id']
    induction right using Quotient.inductionOn
    apply Eqv.eq_of_reg_eq
    simp only [Set.mem_setOf_eq, InS.coe_vsubst, Term.InS.coe_subst0, Term.InS.coe_var,
      Term.Subst.InS.coe_lift, InS.coe_vwk, Ctx.InS.coe_wk1, Region.vwk_vwk]
    simp only [<-Region.vsubst_fromWk, Region.vsubst_vsubst]
    congr
    funext k
    cases k <;> rfl
    ext i
    simp only [List.get_eq_getElem, List.length_cons, Subst.Eqv.get_comp, Subst.Eqv.get_toSubstE,
      Set.mem_setOf_eq, LCtx.InS.coe_wk0, Nat.succ_eq_add_one, lsubst_br, id_eq,
      List.getElem_cons_succ, Subst.Eqv.get_vlift, cfgSubst'_get, List.length_singleton,
      add_lt_iff_neg_right, not_lt_zero', ↓reduceDIte, List.singleton_append, add_tsub_cancel_right,
      vwk1_br, Term.Eqv.wk1_var0, Fin.zero_eta, Fin.val_zero, List.getElem_cons_zero, vwk_id_eq,
      vsubst_br, Term.Eqv.var0_subst0, Term.Eqv.wk_res_self]
    rfl
  | succ k => simp [Subst.Eqv.get_comp, cfgSubst'_get, get_alpha0, Term.Eqv.nil]

theorem Eqv.lwk_lift_seq {A B C : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
  {ρ : LCtx.InS L K}
  {left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)}
  {right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (left ;; right).lwk (ρ.lift (le_refl _))
  = (left.lwk (ρ.lift (le_refl _))) ;; (right.lwk (ρ.lift (le_refl _))) := by
  simp only [<-wseq_eq_seq, lwk_lift_wseq]

theorem Eqv.lwk_slift_seq {A B C : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
  {ρ : LCtx.InS L K}
  {left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)}
  {right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (left ;; right).lwk ρ.slift
  = (left.lwk ρ.slift) ;; (right.lwk ρ.slift) := lwk_lift_seq

theorem Eqv.lwk1_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)}
  {right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (left ;; right).lwk1 (inserted := inserted) = left.lwk1 ;; right.lwk1 := by
  simp only [lwk1, <-LCtx.InS.slift_wk0, lwk_slift_seq]

theorem Eqv.lsubst_vlift_slift_seq {A B C : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
  {σ : Subst.Eqv φ Γ L K}
  {left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)}
  {right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (left ;; right).lsubst σ.slift.vlift
  = left.lsubst σ.slift.vlift ;; right.lsubst σ.slift.vlift := by
  induction left using Quotient.inductionOn
  induction right using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  simp only [
    Subst.Eqv.slift_quot, Subst.Eqv.vlift_quot, seq_quot, lsubst_quot,
    InS.append_def
  ]
  congr 1
  ext
  simp only [Set.mem_setOf_eq, InS.coe_lsubst, Subst.InS.coe_vlift, Subst.InS.coe_slift,
    InS.coe_alpha0, InS.coe_vwk1, Region.lsubst_lsubst]
  congr
  funext k
  cases k with
  | zero =>
    simp only [Subst.comp, Subst.vlift, alpha, Function.update_same, Region.lsubst, Term.wk,
      Nat.liftWk_zero, vwk1_lsubst, Function.comp_apply, Region.vsubst_lsubst,
      Region.vsubst0_var0_vwk1]
    congr
    funext k
    cases k with
    | zero => rfl
    | succ k =>
      simp only [Function.comp_apply, Subst.lift, vwk2_vwk1]
      simp only [Region.vwk1_lwk, vsubst_lwk]
      congr
      simp only [Region.vwk1, Region.vwk_vwk]
      simp only [<-Region.vsubst_fromWk, Region.vsubst_vsubst]
      congr
      funext k; cases k <;> rfl
  | succ k =>
    simp only [
      Region.Subst.comp, Region.lsubst, Region.Subst.vlift, Function.comp_apply, Region.Subst.lift,
      Region.vwk1_lwk, Region.vsubst_lwk, Region.vsubst0_var0_vwk1, Region.alpha, Region.vwk1_lsubst
    ]
    simp only [<-Region.lsubst_fromLwk, Region.lsubst_lsubst]
    rfl

-- theorem Eqv.lsubst_slift_vlift_seq {A B C : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
--   {σ : Subst.Eqv φ Γ L K}
--   {left : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)}
--   {right : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
--   : (left ;; right).lsubst σ.vlift.slift
--   = left.lsubst σ.vlift.slift ;; right.lsubst σ.vlift.slift
--   := sorry

-- theorem Eqv.wrseq_assoc {B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
--   (left : Eqv φ Γ (B::L)) (middle : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)) (right : Eqv φ (⟨C, ⊥⟩::Γ) (D::L))
--   : (left.wrseq middle).wrseq right = left.wrseq (middle ;; right) := by
--   simp only [<-wseq_eq_seq, wrseq, wseq]
--   sorry

def Eqv.Pure {Γ : Ctx α ε} {L : LCtx α} (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) : Prop
  := ∃a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩, r = ret a

theorem Eqv.Pure.nil {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.Pure (Eqv.nil (φ := φ) (ty := ty) (rest := Γ) (targets := L))
  := ⟨Term.Eqv.var 0 (by simp), rfl⟩

theorem Eqv.Pure.ret {Γ : Ctx α ε} {L : LCtx α} {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩}
  : Eqv.Pure (Eqv.ret (targets := L) a) := ⟨a, rfl⟩

theorem Eqv.Pure.seq {Γ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)} {s : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : r.Pure → s.Pure → (r ;; s).Pure
  | ⟨pr, hpr⟩, ⟨ps, hps⟩ => by
    rw [hpr, hps, ret_seq, vwk1_ret, vsubst_ret]
    exact ⟨_, rfl⟩

theorem Eqv.Pure.case' {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨X.coprod Y, ⊥⟩}
  {l : Eqv φ (⟨X, ⊥⟩::⟨A, ⊥⟩::Γ) (B::L)}
  {r : Eqv φ (⟨Y, ⊥⟩::⟨A, ⊥⟩::Γ) (B::L)}
  : l.Pure → r.Pure → (Eqv.case a l r).Pure
  | ⟨pl, hpl⟩, ⟨pr, hpr⟩ => by
    rw [hpl, hpr, Eqv.case_ret]
    exact ⟨_, rfl⟩

theorem Eqv.Pure.case {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨X.coprod Y, e⟩}
  {l : Eqv φ (⟨X, ⊥⟩::⟨A, ⊥⟩::Γ) (B::L)}
  {r : Eqv φ (⟨Y, ⊥⟩::⟨A, ⊥⟩::Γ) (B::L)}
  : a.Pure → l.Pure → r.Pure → (Eqv.case a l r).Pure
  | ⟨pa, hpa⟩, hl, hr => by
    rw [hpa]
    simp [case', hl, hr]

theorem Eqv.Pure.let1' {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨X, ⊥⟩}
  {r : Eqv φ (⟨X, ⊥⟩::⟨A, ⊥⟩::Γ) (B::L)}
  : r.Pure → (Eqv.let1 a r).Pure
  | ⟨pr, hpr⟩ => by
    rw [hpr, Eqv.let1_ret]
    exact ⟨_, rfl⟩

theorem Eqv.Pure.let1 {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨X, e⟩}
  {r : Eqv φ (⟨X, ⊥⟩::⟨A, ⊥⟩::Γ) (B::L)}
  : a.Pure → r.Pure → (Eqv.let1 a r).Pure
  | ⟨pa, hpa⟩, hr => by
    rw [hpa]
    simp [let1', hr]

theorem Eqv.Pure.let2' {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨X.prod Y, ⊥⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::⟨A, ⊥⟩::Γ) (C::L)}
  : r.Pure → (Eqv.let2 a r).Pure
  | ⟨pr, hpr⟩ => by
    rw [hpr, Eqv.let2_ret]
    exact ⟨_, rfl⟩

theorem Eqv.Pure.let2 {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨X.prod Y, e⟩}
  {r : Eqv φ (⟨Y, ⊥⟩::⟨X, ⊥⟩::⟨A, ⊥⟩::Γ) (C::L)}
  : a.Pure → r.Pure → (Eqv.let2 a r).Pure
  | ⟨pa, hpa⟩, hr => by
    rw [hpa]
    simp [let2', hr]

theorem Eqv.Pure.vwk {Γ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨A', ⊥⟩::Δ) (B::L)} {ρ : Ctx.InS (⟨A, ⊥⟩::Γ) (⟨A', ⊥⟩::Δ)}
  : r.Pure → (r.vwk ρ).Pure
  | ⟨pr, hpr⟩ => by
    rw [hpr, Eqv.vwk_ret]
    exact ⟨_, rfl⟩

theorem Eqv.Pure.vwk1 {L : LCtx α}
  {r : Eqv φ (⟨A', ⊥⟩::Δ) (B::L)}
  : r.Pure → (r.vwk1 (inserted := inserted)).Pure
  | ⟨pr, hpr⟩ => by
    rw [hpr, Eqv.vwk1_ret]
    exact ⟨_, rfl⟩

theorem Eqv.vsubst_alpha0 {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} (σ : Term.Subst.Eqv φ Γ Δ)
  (r : Eqv φ (⟨A, ⊥⟩::Δ) (B::L))
  : r.alpha0.vsubst σ = (r.vsubst (σ.lift (le_refl _))).alpha0 := by
  induction r using Quotient.inductionOn;
  induction σ using Quotient.inductionOn;
  simp [InS.vsubst_alpha0]

-- TODO: lwk lift, vsubst, lsubst lift

theorem Eqv.wthen_cfg {B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ Γ (B::L)) (g : Eqv φ (⟨B, ⊥⟩::Γ) (R ++ L))
  (G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : f.wthen (cfg R g (λi => (G i).vwk1))
  = cfg R
    ((f.lwk (LCtx.InS.add_left_append _ _).slift).wthen g)
    (λi => (G i))
  := by
  simp only [wthen, cfg_eq_ucfg, ucfg, lsubst_lsubst, <-lsubst_toSubst]
  congr
  ext i
  simp only [
    Subst.Eqv.get_comp, Subst.Eqv.get_toSubst, lsubst_br,
    LCtx.InS.coe_slift, LCtx.InS.coe_add_left_append
  ]
  cases i using Fin.cases with
  | zero =>
    simp only [
      Subst.Eqv.get_vlift, vwk_id_eq, cfgSubst_get, Fin.val_zero, Nat.liftWk, vwk1_cfg, vsubst_cfg,
      lsubst_cfg, vwk1_br, vsubst_br, lsubst_br
    ]
    congr
    · simp [-Subst.Eqv.liftn_append_singleton]
    · funext i
      cases i using Fin.elim1
      simp only [Fin.elim1_zero, vwk1_vwk2]
      simp only [
        vwk1_lwk0, vsubst_lwk0, Subst.Eqv.liftn_append_singleton, Subst.Eqv.vlift_slift,
        lsubst_slift_lwk0, <-vlift_cfgSubst, Subst.Eqv.vwk1_lsubst_vlift
      ]
      congr
      simp only [vwk1, vwk_vwk]
      simp only [<-vsubst_toSubst, vsubst_vsubst]
      congr
      ext
      funext k
      cases k <;> rfl
  | succ i =>
    simp only [List.singleton_append, List.append_eq, List.nil_append, List.get_eq_getElem,
      List.length_cons, Fin.val_succ, List.getElem_cons_succ, List.length_singleton,
      Nat.liftWk_succ, Set.mem_setOf_eq, Subst.Eqv.get_vlift]
    rw [cfgSubst_get_ge (by simp), cfgSubst_get_ge (by simp)]
    simp only [add_tsub_cancel_right, vwk1_br,
      Term.Eqv.wk1_var0, vwk_id_br,
      Term.Eqv.wk_id_var, vsubst_br, Term.Eqv.var0_subst0, List.append_eq, List.nil_append,
      Nat.liftWk_succ, LCtx.InS.coe_slift, LCtx.InS.coe_add_left_append, id_eq,
      Term.Eqv.wk_res_var, lsubst_br, Nat.add_succ_sub_one, Nat.add_zero,
      Int.reduceNeg, eq_mpr_eq_cast, cast_eq, Subst.Eqv.get_vlift, vwk_id_eq]
    rw [cfgSubst_get_ge (by simp), vwk1_br, vsubst_br]
    simp
    rfl

theorem Eqv.wrseq_cfg {B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ Γ (B::L)) (g : Eqv φ (⟨B, ⊥⟩::Γ) (R ++ C::L))
  (G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ C::L))
  : f.wrseq (cfg R g (λi => (G i).vwk1))
  = cfg R
    (((f.lwk LCtx.InS.shf.slift).wrseq g.shf).ushf)
    (λi => (G i))
  := by
  simp only [wrseq_eq_wthen, wthen_cfg]
  congr
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  simp only [lwk1_quot, lwk_quot, wthen_quot, shf_quot, ushf_quot]
  apply congrArg
  ext
  simp only [Set.mem_setOf_eq, InS.coe_wthen, InS.coe_lwk, LCtx.InS.coe_slift,
    LCtx.InS.coe_add_left_append, InS.coe_lwk1, Region.lwk1, InS.coe_ushf, LCtx.InS.coe_shf,
    InS.coe_shf, Region.lwk_lwk]
  congr
  funext k
  cases k <;> simp_arith

theorem Eqv.wseq_cfg {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (g : Eqv φ (⟨B, ⊥⟩::Γ) (R ++ C::L))
  (G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ C::L))
  : f.wseq (cfg R g (λi => (G i).vwk1))
  = cfg R
    (((f.lwk LCtx.InS.shf.slift).wseq g.shf).ushf)
    (λi => (G i).vwk1)
  := by simp only [wseq_eq_wrseq, vwk1_cfg, vwk1_vwk2, wrseq_cfg, vwk1_shf]

theorem Eqv.seq_cfg {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (g : Eqv φ (⟨B, ⊥⟩::Γ) (R ++ C::L))
  (G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ C::L))
  : f ;; cfg R g (λi => (G i).vwk1)
  = cfg R
    ((f.lwk LCtx.InS.shf.slift ;; g.shf).ushf)
    (λi => (G i).vwk1)
  := by simp only [<-wseq_eq_seq, wseq_cfg]

theorem Eqv.seq_cont {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (g : Eqv φ (⟨B, ⊥⟩::Γ) (C::D::L))
  (h : Eqv φ (⟨C, ⊥⟩::Γ) (C::D::L))
  : f ;; cfg [C] g (Fin.elim1 h.vwk1) = cfg [C] (f.lwk1 ;; g) (Fin.elim1 h.vwk1)
  := by
  have hc := Eqv.seq_cfg (R := [C]) f g (Fin.elim1 h)
  convert hc
  · rename Fin 1 => i; cases i using Fin.elim1; rfl
  · induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    induction h using Quotient.inductionOn
    apply Eqv.eq_of_reg_eq
    rfl
  · rename Fin 1 => i; cases i using Fin.elim1; rfl

theorem Eqv.let2_eta_nil {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : let2 (Term.Eqv.var 0 Ctx.Var.shead)
    (ret $ (Term.Eqv.var 1 Ctx.Var.shead.step).pair (Term.Eqv.var 0 Ctx.Var.shead))
  = nil (φ := φ) (ty := A.prod B) (rest := Γ) (targets := L) := by
  rw [let2_ret, Term.Eqv.let2_eta]; rfl

theorem Eqv.let2_eta_ret {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ ((A, ⊥)::Γ) (B.prod C, ⊥)}
  : let2 a
    (ret $ (Term.Eqv.var 1 Ctx.Var.shead.step).pair (Term.Eqv.var 0 Ctx.Var.shead))
  = ret (targets := L) a := by
  rw [let2_ret, Term.Eqv.let2_eta]

theorem Eqv.let2_eta_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Eqv φ ((A.prod B, ⊥)::Γ) (C::L)}
  : let2 (Term.Eqv.var 0 Ctx.Var.shead)
    ((ret $ (Term.Eqv.var 1 Ctx.Var.shead.step).pair (Term.Eqv.var 0 Ctx.Var.shead))
      ;; f.vwk1.vwk1)
  = f := by rw [<-let2_seq, let2_eta_nil, nil_seq]

theorem Eqv.uniform_wseq {Γ : Ctx α ε} {L : LCtx α}
  {β : Eqv φ Γ (A::L)} {e : Term.Eqv φ ((A, ⊥)::Γ) (B, ⊥)}
  {r : Eqv φ ((B, ⊥)::Γ) (B::L)} {s : Eqv φ ((A, ⊥)::Γ) (A::L)}
  (hrs : (ret e).wseq r = s.wseq (ret e))
  : cfg [B] (β.wrseq (ret e)) (Fin.elim1 r) = cfg [A] β (Fin.elim1 s) := by
  induction β using Quotient.inductionOn with
  | h β => induction e using Quotient.inductionOn with
  | h e => induction r using Quotient.inductionOn with
  | h r => induction s using Quotient.inductionOn with
  | h s =>
    simp only [
      br_quot, wrseq_quot, List.length_singleton, List.get_eq_getElem, List.singleton_append
    ]
    apply Quotient.sound
    simp only [br_quot, wseq_quot] at hrs
    convert InS.uniform (β := β) (e := e) (r := r) (s := s) (Quotient.exact hrs) using 2
    <;> funext i <;> cases i using Fin.elim1 <;> rfl

theorem Eqv.uniform {Γ : Ctx α ε} {L : LCtx α}
  {β : Eqv φ Γ (A::L)} {e : Term.Eqv φ ((A, ⊥)::Γ) (B, ⊥)}
  {r : Eqv φ ((B, ⊥)::Γ) (B::L)} {s : Eqv φ ((A, ⊥)::Γ) (A::L)}
  (hrs : (ret e) ;; r = s ;; (ret e))
  : cfg [B] (β.wrseq (ret e)) (Fin.elim1 r) = cfg [A] β (Fin.elim1 s) := by
  simp only [<-wseq_eq_seq] at hrs
  exact Eqv.uniform_wseq hrs

theorem Eqv.codiagonal {Γ : Ctx α ε} {L : LCtx α}
  {β : Eqv φ Γ (A::L)} {G : Eqv φ (⟨A, ⊥⟩::Γ) (A::A::L)}
  : cfg [A] β (Fin.elim1 (cfg [A] nil (Fin.elim1 G.vwk1)))
  = cfg [A] β (Fin.elim1 (G.lsubst nil.lsubst0)) := by
  induction β using Quotient.inductionOn with
  | h β => induction G using Quotient.inductionOn with
  | h G =>
    have h := Quotient.sound $ InS.codiagonal (β := β) (G := G)
    simp only [<-cfg_quot] at h
    convert h using 2 <;> funext i <;> cases i using Fin.elim1
    · simp only [Fin.isValue, List.get_eq_getElem, List.length_singleton, Fin.val_zero,
      List.getElem_cons_zero, List.singleton_append, List.append_eq, List.nil_append, vwk1_quot,
      Fin.elim1_zero, <-cfg_quot]
      congr
      funext i; cases i using Fin.elim1; rfl
    · rfl

def Eqv.loop {Γ : Ctx α ε} {L : LCtx α} : Eqv φ Γ L
  := cfg [Ty.unit] (Eqv.br 0 (Term.Eqv.unit _) LCtx.Trg.shead) (Fin.elim1 nil)

theorem Eqv.loop_def {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.loop (φ := φ) (Γ := Γ) (L := L) = ⟦InS.loop⟧ := by
  simp only [loop, Term.Eqv.unit_quot, Term.InS.unit, br_quot, nil]
  apply Eq.trans cfg1_quot
  apply Eqv.eq_of_reg_eq
  simp only [List.length_singleton, InS.coe_cfg, InS.coe_br, Region.loop, cfg.injEq, heq_eq_eq,
    true_and, InS.coe_loop]
  funext i
  cases i using Fin.elim1
  rfl

@[simp]
theorem Eqv.vwk_loop {Γ Δ : Ctx α ε} {L : LCtx α} {ρ : Ctx.InS Γ Δ}
  : Eqv.loop.vwk ρ = Eqv.loop (φ := φ) (L := L) := by simp [loop_def]

@[simp]
theorem Eqv.vsubst_loop {Γ Δ : Ctx α ε} {L : LCtx α} {σ : Term.Subst.Eqv φ Γ Δ}
  : loop.vsubst σ = loop (φ := φ) (L := L) := by
  induction σ using Quotient.inductionOn
  simp [loop_def]

@[simp]
theorem Eqv.lwk_loop {Γ : Ctx α ε} {L K : LCtx α} {ρ : LCtx.InS L K}
  : loop.lwk ρ = loop (φ := φ) (Γ := Γ) := by simp [loop_def]

@[simp]
theorem Eqv.lsubst_loop {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.Eqv φ Γ L K}
  : loop.lsubst σ = loop (φ := φ) := by
  induction σ using Quotient.inductionOn
  simp [loop_def]

@[simp]
theorem Eqv.loop_seq {Γ : Ctx α ε} {L : LCtx α} {r : Eqv φ ((B, ⊥)::Γ) (C::L)}
  : loop (Γ := (A, ⊥)::Γ) (L := B::L) ;; r = loop := by
  induction r using Quotient.inductionOn
  simp [loop_def, Region.InS.append_def]
