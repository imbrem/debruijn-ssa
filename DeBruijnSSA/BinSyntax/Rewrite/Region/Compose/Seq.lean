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
  (ρ : Ctx.InS (⟨tyIn, ⊥⟩::rest') _)
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
  : Eqv.let1 (Term.Eqv.var 0 ⟨by simp, le_refl _⟩) Eqv.nil
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

theorem InS.alpha0_congr {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ (⟨A, ⊥⟩::Γ) (B::L)}
  (h : r ≈ r') : InS.alpha0 r ≈ InS.alpha0 r'
  := sorry

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
  simp only [Set.mem_setOf_eq, InS.coe_vsubst, Term.Subst.coe_lift, InS.coe_lsubst, InS.coe_alpha0,
    InS.coe_vwk, Ctx.InS.coe_wk1, vsubst_lift_lsubst_alpha,
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

theorem Eqv.ret_ret {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩}
  {b : Term.Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, ⊥⟩}
  : ret (targets := L) a ;; ret b = ret (a ;;' b) := ret_br

theorem Eqv.ret_of_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩}
  {b : Term.Eqv φ (⟨B, ⊥⟩::Γ) ⟨C, ⊥⟩}
  : ret (a ;;' b) = ret (targets := L) a ;; ret b := ret_ret.symm

theorem Eqv.ret_nil : ret Term.Eqv.nil = nil (φ := φ) (ty := A) (rest := Γ) (targets := L)  := rfl

-- TODO: centrality lore...

-- inductive PureTree : (Γ : ℕ → ε) → Region φ → Prop
--   | ret a : PureTree Γ (ret a)
--   | case e l r
--     : e.effect Γ = ⊥
--       → PureTree (Nat.liftBot Γ) l
--       → PureTree (Nat.liftBot Γ) r
--       → PureTree Γ (case e l r)
--   | let1 e r
--     : e.effect Γ = ⊥
--       → PureTree (Nat.liftBot Γ) r
--       → PureTree Γ (let1 e r)
--   | let2 e r
--     : e.effect Γ = ⊥
--       → PureTree (Nat.liftBot Γ) r
--       → PureTree Γ (let2 e r)

-- def InS.PureTree {Γ : Ctx α ε} {L : LCtx α} (r : InS φ Γ L) : Prop
--   := Region.PureTree (φ := φ) Γ.effect r

def Eqv.Pure {Γ : Ctx α ε} {L : LCtx α} (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) : Prop
  := ∃a : Term.Eqv φ (⟨A, ⊥⟩::Γ) ⟨B, ⊥⟩, r = ret a

-- TODO: ret, case, let1, let2

-- TODO: closed under vwk, lwk (lift), vsubst, lsubst (pure), ltimes, rtimes...

theorem Eqv.Pure.nil {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.Pure (Eqv.nil (φ := φ) (ty := ty) (rest := Γ) (targets := L)) := sorry

theorem Eqv.Pure.seq {Γ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)} {s : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  (hr : r.Pure) (hs : s.Pure) : (r ;; s).Pure := sorry

-- TODO: ret, case, let1, let2

-- TODO: closed under vwk, lwk (lift), vsubst, lsubst (pure), append...
