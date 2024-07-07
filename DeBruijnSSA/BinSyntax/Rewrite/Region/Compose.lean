import DeBruijnSSA.BinSyntax.Rewrite.Region.LSubst
import DeBruijnSSA.BinSyntax.Typing.Region.Compose

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

abbrev Eqv.ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (t : Term.Eqv φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : Eqv φ (⟨tyIn, ⊥⟩::rest) (tyOut::targets)
  := Quotient.liftOn t (λt => ⟦InS.ret t⟧) (λ_ _ h => Quotient.sound $ InS.br_congr _ h (by simp))

theorem Eqv.vwk_ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (ρ : Ctx.InS (⟨tyIn, ⊥⟩::rest') _)
  (t : Term.Eqv φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : (Eqv.ret (targets := targets) t).vwk ρ = Eqv.ret (t.wk ρ) := by
  induction t using Quotient.inductionOn
  rfl

theorem Eqv.vwk1_ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (t : Term.Eqv φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : (Eqv.ret (targets := targets) t).vwk1 (inserted := inserted)
  = Eqv.ret (t.wk ⟨Nat.liftWk Nat.succ, by simp⟩) := by
  induction t using Quotient.inductionOn
  rfl

theorem Eqv.vsubst_ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (σ : Term.Subst.Eqv φ (⟨tyIn, ⊥⟩::Γ) _)
  (t : Term.Eqv φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : (Eqv.ret (targets := targets) t).vsubst σ = Eqv.ret (t.subst σ) := by
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
  (σ : Term.Subst.Eqv φ Γ Δ)
  (left : Eqv φ (⟨A, ⊥⟩::Δ) (B::L))
  (right : Eqv φ (⟨B, ⊥⟩::Δ) (C::L))
  : (left ;; right).vsubst (σ.lift (le_refl _))
  = left.vsubst (σ.lift (le_refl _)) ;; right.vsubst (σ.lift (le_refl _)) := by
  induction left using Quotient.inductionOn;
  induction right using Quotient.inductionOn;
  sorry

theorem Eqv.vsubst_liftn₂_seq {A B C : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  (σ : Term.Subst.Eqv φ Γ Δ)
  (left : Eqv φ (⟨A, ⊥⟩::X::Δ) (B::L))
  (right : Eqv φ (⟨B, ⊥⟩::X::Δ) (C::L))
  : (left ;; right).vsubst (σ.liftn₂ (le_refl _) (le_refl _))
  = left.vsubst (σ.liftn₂ (le_refl _) (le_refl _)) ;; right.vsubst (σ.liftn₂ (le_refl _) (le_refl _))
  := by stop simp only [<-Term.Subst.InS.lift_lift, vsubst_lift_seq]

open Term.Eqv

-- TODO: centrality lore...

inductive PureTree : (Γ : ℕ → ε) → Region φ → Prop
  | ret a : PureTree Γ (ret a)
  | case e l r
    : e.effect Γ = ⊥
      → PureTree (Nat.liftBot Γ) l
      → PureTree (Nat.liftBot Γ) r
      → PureTree Γ (case e l r)
  | let1 e r
    : e.effect Γ = ⊥
      → PureTree (Nat.liftBot Γ) r
      → PureTree Γ (let1 e r)
  | let2 e r
    : e.effect Γ = ⊥
      → PureTree (Nat.liftBot Γ) r
      → PureTree Γ (let2 e r)

def InS.PureTree {Γ : Ctx α ε} {L : LCtx α} (r : InS φ Γ L) : Prop
  := Region.PureTree (φ := φ) Γ.effect r

-- TODO: ret, case, let1, let2

-- TODO: closed under vwk, lwk (lift), vsubst, lsubst (pure), append...

def Eqv.IsPure {Γ : Ctx α ε} {L : LCtx α} (r : Eqv φ Γ L) : Prop
  := ∃r' : InS φ Γ L, ⟦r'⟧ = r ∧ r'.PureTree

-- TODO: ret, case, let1, let2

-- TODO: closed under vwk, lwk (lift), vsubst, lsubst (pure), ltimes, rtimes...

theorem Eqv.IsPure.nil {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.IsPure (Eqv.nil (φ := φ) (ty := ty) (rest := Γ) (targets := L)) := sorry

theorem Eqv.IsPure.seq {Γ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)} {s : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  (hr : r.IsPure) (hs : s.IsPure) : (r ;; s).IsPure := sorry

def Eqv.rtimes {tyIn tyOut : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (tyLeft : Ty α) (r : Eqv φ (⟨tyIn, ⊥⟩::Γ) (tyOut::L))
  : Eqv φ (⟨tyLeft.prod tyIn, ⊥⟩::Γ) ((tyLeft.prod tyOut)::L)
  := Eqv.let2 (var 0 Ctx.Var.shead) $
  r.vwk1.vwk1 ;;
  ret (pair (var 1 (by simp)) (var 0 (by simp)))

infixl:70 " ⋊ "  => Eqv.rtimes

theorem Eqv.IsPure.rtimes {tyIn tyOut : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (tyLeft : Ty α) {r : Eqv φ (⟨tyIn, ⊥⟩::Γ) (tyOut::L)}
  : Eqv.IsPure r → Eqv.IsPure (tyLeft ⋊ r) := sorry

def Eqv.swap {left right : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨left.prod right, ⊥⟩::Γ) ((right.prod left)::L)
  := Eqv.let2 (var 0 Ctx.Var.shead) $
  ret (pair (var 0 (by simp)) (var 1 (by simp)))

theorem Eqv.IsPure.swap {left right : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.IsPure (Eqv.swap (φ := φ) (left := left) (right := right) (Γ := Γ) (L := L)) := sorry

theorem Eqv.repack {left right : Ty α} {rest : Ctx α ε} {targets : LCtx α}
  : Eqv.let2 (var 0 ⟨by simp, le_refl _⟩)
    (Eqv.ret (pair (var 1 (by simp)) (var 0 (by simp))))
  = Eqv.nil (φ := φ) (ty := left.prod right) (rest := rest) (targets := targets) := by
  rw [<-let1_0_nil, <-let2_eta, let1_beta]
  rfl

theorem Eqv.swap_swap {left right : Ty α}
  : Eqv.swap ;; Eqv.swap
  = (Eqv.nil (φ := φ) (ty := left.prod right) (rest := rest) (targets := targets)) := by
  stop
  simp only [
    swap, let2_seq, vwk1, vwk_let2, wk_var, wk_pair, Nat.liftWk, vwk_ret, Ctx.InS.liftn₂,
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
  := Eqv.swap ;; tyRight ⋊ r ;; Eqv.swap

infixl:70 " ⋉ "  => Eqv.ltimes

theorem Eqv.IsPure.ltimes {tyIn tyOut : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {r : Eqv φ (⟨tyIn, ⊥⟩::Γ) (tyOut::L)} (hr : r.IsPure) (tyRight : Ty α)
  : IsPure (r ⋉ tyRight) := seq (seq swap (hr.rtimes _)) swap

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

theorem Eqv.swap_rtimes {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : Eqv.swap ;; C ⋊ r = r ⋉ C ;; Eqv.swap
  := by rw [<-swap_ltimes_swap, <-seq_assoc, <-seq_assoc, swap_swap, nil_seq]

theorem Eqv.ltimes_nil {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv.nil ⋉ tyRight = (Eqv.nil (φ := φ) (ty := ty.prod tyRight) (rest := Γ) (targets := L))
  := by rw [<-swap_rtimes_swap, rtimes_nil, seq_nil, swap_swap]

theorem Eqv.ltimes_seq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)) (s : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : (r ;; s) ⋉ tyRight = (r ⋉ tyRight) ;; (s ⋉ tyRight) := by
  simp only [<-swap_rtimes_swap, rtimes_seq, seq_assoc]
  rw [<-seq_assoc swap swap, swap_swap, nil_seq]

def Eqv.runit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨ty.prod Ty.unit, ⊥⟩::Γ) (ty::L)
  := let2 (var 0 Ctx.Var.shead) (ret $ var 1 (by simp))

def Eqv.runit_inv {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨ty, ⊥⟩::Γ) (ty.prod Ty.unit::L)
  := ret $ (pair (var 0 Ctx.Var.shead) (unit _))

theorem Eqv.IsPure.runit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (runit (φ := φ) (ty := ty) (Γ := Γ) (L := L)).IsPure := sorry

theorem Eqv.IsPure.runit_inv {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (runit_inv (φ := φ) (ty := ty) (Γ := Γ) (L := L)).IsPure := sorry

theorem Eqv.runit_seq_runit_inv_helper {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : runit (φ := φ) (ty := ty) (Γ := Γ) (L := L) ;; runit_inv
  = let2 (var 0 ⟨by simp, le_refl _⟩)
    (let1 (unit ⊥) (ret $ pair (var 2 (by simp)) (var 0 (by simp)))) := by
  rw [let1_beta]
  rfl

theorem Eqv.runit_seq_runit_inv {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : runit (φ := φ) (ty := ty) (Γ := Γ) (L := L) ;; runit_inv = nil := by
  rw [runit_seq_runit_inv_helper, terminal _ (var 0 (by simp)), let1_beta]
  apply repack

theorem Eqv.runit_inv_seq_runit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : runit_inv (φ := φ) (ty := ty) (Γ := Γ) (L := L) ;; runit = nil := by
  stop
  simp only [runit_inv, runit, ret_seq]
  rw [vwk1, vwk_let2, vsubst_let2, wk_var, subst_var]
  simp only [Nat.liftWk_zero, Term.Subst.InS.get_0_subst0, Set.mem_setOf_eq]
  rw [let2_pair, let1_beta, let1_beta]
  rfl

theorem Eqv.ltimes_seq_runit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : r ⋉ Ty.unit ;; runit = runit ;; r := sorry

def Eqv.lunit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨Ty.unit.prod ty, ⊥⟩::Γ) (ty::L)
  := let2 (var 0 Ctx.Var.shead) (ret $ var 0 (by simp))

def Eqv.lunit_inv {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨ty, ⊥⟩::Γ) (Ty.unit.prod ty::L)
  := ret $ (pair (unit _) (var 0 Ctx.Var.shead))

theorem Eqv.IsPure.lunit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (lunit (φ := φ) (ty := ty) (Γ := Γ) (L := L)).IsPure := sorry

theorem Eqv.IsPure.lunit_inv {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (lunit_inv (φ := φ) (ty := ty) (Γ := Γ) (L := L)).IsPure := sorry

theorem Eqv.lunit_seq_lunit_inv {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : lunit (φ := φ) (ty := ty) (Γ := Γ) (L := L) ;; lunit_inv = nil
  := sorry

theorem Eqv.lunit_inv_seq_lunit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : lunit_inv (φ := φ) (ty := ty) (Γ := Γ) (L := L) ;; lunit = nil
  := sorry

-- TODO: swap ;; lunit = runit, lunit_inv ;; swap = runit_inv, and vice versa...

theorem Eqv.rtimes_seq_lunit {ty : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : Ty.unit ⋊ r ;; lunit = lunit ;; r
  := sorry

theorem Eqv.IsPure.central_left {A A' B B' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) (A'::L)}
  (hl : l.IsPure)
  (r : Eqv φ (⟨B, ⊥⟩::Γ) (B'::L))
  : (l ⋉ B) ;; (A' ⋊ r) = (A ⋊ r) ;; (l ⋉ B') := sorry

theorem Eqv.IsPure.central_right {A A' B B' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (A'::L))
  {r : Eqv φ (⟨B, ⊥⟩::Γ) (B'::L)}
  (hr : r.IsPure)
  : (A ⋊ r) ;; (l ⋉ B') = (l ⋉ B) ;; (A' ⋊ r) := by
  rw [
    <-swap_rtimes_swap, <-seq_assoc, <-seq_assoc, <-swap_ltimes, seq_assoc Eqv.swap,
    hr.central_left, <-seq_assoc, swap_rtimes, seq_assoc (l ⋉ B), swap_ltimes,
    seq_assoc, seq_assoc (A' ⋊ r), swap_swap, seq_nil
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

theorem Eqv.IsPure.assoc {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (assoc (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).IsPure := sorry

theorem Eqv.IsPure.assoc_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (assoc_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).IsPure := sorry

theorem Eqv.assoc_seq_assoc_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : assoc (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L) ;; assoc_inv = nil
  := sorry

theorem Eqv.assoc_inv_seq_assoc {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
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
  : assoc (φ := φ) (Γ := Γ) (L := L) (A := X) (B := Y) (C := Z) ;; swap ;; assoc
  = swap ⋉ Z ;; assoc ;; Y ⋊ swap
  := sorry

def Eqv.coprod {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) (C::L)
  := case (var 0 Ctx.Var.shead) l.vwk1 r.vwk1

theorem Eqv.IsPure.coprod {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)} (hl : l.IsPure)
  {r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)} (hr : r.IsPure)
  : (coprod l r).IsPure := sorry

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

def Eqv.ret_inl {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨A, ⊥⟩::Γ) (A.coprod B::L)
  := ret $ (inl (var 0 Ctx.Var.shead))

def Eqv.ret_inr {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨B, ⊥⟩::Γ) (A.coprod B::L)
  := ret $ (inr (var 0 Ctx.Var.shead))

theorem Eqv.IsPure.lzero {Γ : Ctx α ε} {L : LCtx α} {A : Ty α}
  : (lzero (φ := φ) (Γ := Γ) (L := L) (A := A)).IsPure := sorry

theorem Eqv.IsPure.rzero {Γ : Ctx α ε} {L : LCtx α} {A : Ty α}
  : (rzero (φ := φ) (Γ := Γ) (L := L) (A := A)).IsPure := sorry

theorem Eqv.IsPure.ret_inl {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (ret_inl (φ := φ) (Γ := Γ) (L := L) (A := A) (B := B)).IsPure := sorry

theorem Eqv.IsPure.ret_inr {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (ret_inr (φ := φ) (Γ := Γ) (L := L) (A := A) (B := B)).IsPure := sorry

def Eqv.sum {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L))
  : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) ((C.coprod D)::L)
  := coprod (l ;; ret_inl) (r ;; ret_inr)

theorem Eqv.IsPure.sum {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)} (hl : l.IsPure)
  {r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L)} (hr : r.IsPure)
  : (sum l r).IsPure := coprod (seq hl ret_inl) (seq hr ret_inr)

theorem Eqv.coprod_inl_inr {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : coprod ret_inl ret_inr = Eqv.nil (φ := φ) (ty := A.coprod B) (rest := Γ) (targets := L) := by
  -- TODO: case_eta
  sorry

theorem Eqv.sum_nil {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : sum (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L) nil nil = nil := coprod_inl_inr

theorem Eqv.ret_inl_seq_coprod {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : ret_inl ;; coprod l r = l := by
  stop
  rw [ret_inl, coprod, ret_seq, vwk1, vwk_case, vsubst_case]
  simp only [Set.mem_setOf_eq, wk_var, Nat.liftWk_zero, subst_var, Term.Subst.InS.get_0_subst0]
  rw [case_inl, let1_beta, vwk1, vwk_vwk, vsubst_vsubst]
  -- TODO: vwk_vsubst, lore...
  sorry

theorem Eqv.ret_inr_seq_coprod {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : ret_inr ;; coprod l r = r := by
  stop
  rw [ret_inr, coprod, ret_seq, vwk1, vwk_case, vsubst_case]
  simp only [Set.mem_setOf_eq, wk_var, Nat.liftWk_zero, subst_var, Term.Subst.InS.get_0_subst0]
  rw [case_inr, let1_beta, vwk1, vwk_vwk, vsubst_vsubst]
  -- TODO: vwk_vsubst, lore...
  sorry

theorem Eqv.ret_inl_seq_rzero
  : ret_inl ;; rzero = nil (φ := φ) (ty := A) (rest := Γ) (targets := L) := by
  rw [rzero, ret_inl_seq_coprod]

theorem Eqv.ret_inr_seq_lzero
  : ret_inr ;; lzero = nil (φ := φ) (ty := A) (rest := Γ) (targets := L) := by
  rw [lzero, ret_inr_seq_coprod]

theorem Eqv.rzero_seq_ret_inl {A : Ty α}
  : rzero ;; ret_inl = nil (φ := φ) (ty := A.coprod Ty.empty) (rest := Γ) (targets := L) := by
  rw [rzero, coprod_seq, <-sum_nil, sum]
  congr 1
  apply zero_eq

theorem Eqv.lzero_seq_ret_inr {A : Ty α}
  : lzero ;; ret_inr = nil (φ := φ) (ty := Ty.empty.coprod A) (rest := Γ) (targets := L) := by
  rw [lzero, coprod_seq, <-sum_nil, sum]
  congr 1
  apply zero_eq

-- TODO: naturality

theorem Eqv.ret_inl_seq_join {Γ : Ctx α ε} {L : LCtx α}
  : ret_inl ;; join (φ := φ) (A := A) (Γ := Γ) (L := L) = nil := by
  rw [join, ret_inl_seq_coprod]

theorem Eqv.ret_inr_seq_join {Γ : Ctx α ε} {L : LCtx α}
  : ret_inr ;; join (φ := φ) (A := A) (Γ := Γ) (L := L) = nil := by
  rw [join, ret_inr_seq_coprod]

theorem Eqv.ret_inl_seq_sum {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L))
  : ret_inl ;; (sum l r) = l ;; ret_inl := by rw [sum, ret_inl_seq_coprod]

theorem Eqv.ret_inr_seq_sum {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L))
  : ret_inr ;; (sum l r) = r ;; ret_inr := by rw [sum, ret_inr_seq_coprod]

theorem Eqv.sum_seq_coprod {A B C D E : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L))
  (s : Eqv φ (⟨C, ⊥⟩::Γ) (E::L)) (t : Eqv φ (⟨D, ⊥⟩::Γ) (E::L))
  : (sum l r) ;; (coprod s t) = coprod (l ;; s) (r ;; t) := by
  rw [sum, coprod_seq, seq_assoc, ret_inl_seq_coprod, seq_assoc, ret_inr_seq_coprod]

theorem Eqv.sum_seq_sum {A B C D E F : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L))
  (s : Eqv φ (⟨C, ⊥⟩::Γ) (E::L)) (t : Eqv φ (⟨D, ⊥⟩::Γ) (F::L))
  : (sum l r) ;; (sum s t) = sum (l ;; s) (r ;; t) := by
  rw [sum, coprod_seq, seq_assoc, ret_inl_seq_sum, seq_assoc, ret_inr_seq_sum]
  simp only [<-seq_assoc]; rfl

theorem Eqv.sum_seq_join {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : (sum l r) ;; join = coprod l r := by simp [join, sum_seq_coprod]

theorem Eqv.sum_self_seq_join {A B} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : sum r r ;; join = join ;; r := by rw [sum_seq_join, join, coprod_seq]; simp

def Eqv.aswap {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) (B.coprod A::L)
  := coprod ret_inr ret_inl

theorem Eqv.IsPure.aswap {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (aswap (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L)).IsPure := coprod ret_inr ret_inl

theorem Eqv.aswap_seq_aswap {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : aswap (φ := φ) (A := A) (B := B) (Γ := Γ) (L := L) ;; aswap = nil := by
  simp only [aswap, coprod_seq, ret_inl_seq_coprod, ret_inr_seq_coprod, coprod_inl_inr]

theorem Eqv.aswap_seq_coprod {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : aswap ;; (coprod l r) = coprod r l := by
  rw [aswap, coprod_seq, ret_inl_seq_coprod, ret_inr_seq_coprod]

theorem Eqv.aswap_seq_sum {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)) (r : Eqv φ (⟨B, ⊥⟩::Γ) (D::L))
  : aswap ;; (sum l r) = sum r l ;; aswap := by
  rw [sum, aswap_seq_coprod, aswap, sum_seq_coprod]

def Eqv.aassoc {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨(A.coprod B).coprod C, ⊥⟩::Γ) (A.coprod (B.coprod C)::L)
  := sorry

def Eqv.aassoc_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨A.coprod (B.coprod C), ⊥⟩::Γ) ((A.coprod B).coprod C::L)
  := sorry

theorem Eqv.IsPure.aassoc {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (aassoc (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).IsPure := sorry

theorem Eqv.IsPure.aassoc_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (aassoc_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).IsPure := sorry

theorem Eqv.aassoc_seq_aassoc_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : aassoc (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L) ;; aassoc_inv = nil
  := sorry

theorem Eqv.aassoc_inv_seq_aassoc {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : aassoc_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L) ;; aassoc = nil
  := sorry

theorem Eqv.aassoc_left_nat {A B C A' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (l : Eqv φ (⟨A, ⊥⟩::Γ) (A'::L))
  : (l.sum (nil (ty := B))).sum (nil (ty := C)) ;; aassoc
  = aassoc ;; l.sum (nil (ty := B.coprod C)) := sorry

theorem Eqv.aassoc_mid_nat {A B C B' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (m : Eqv φ (⟨B, ⊥⟩::Γ) (B'::L))
  : (A ⋊ m) ⋉ C ;; assoc = assoc ;; A ⋊ (m ⋉ C) := sorry

theorem Eqv.aassoc_right_nat {A B C C' : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (r : Eqv φ (⟨C, ⊥⟩::Γ) (C'::L))
  : (A.prod B) ⋊ r ;; assoc = assoc ;; A ⋊ (B ⋊ r) := sorry

theorem Eqv.atriangle {X Y : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : aassoc (φ := φ) (Γ := Γ) (L := L) (A := X) (B := Ty.empty) (C := Y) ;; nil.sum lzero
  = rzero.sum nil := sorry

theorem Eqv.apentagon {W X Y Z : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : aassoc (φ := φ) (Γ := Γ) (L := L) (A := W.coprod X) (B := Y) (C := Z) ;; aassoc
  = aassoc.sum nil ;; aassoc ;; nil.sum aassoc
  := sorry

theorem Eqv.ahexagon {X Y Z : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : aassoc (φ := φ) (Γ := Γ) (L := L) (A := X) (B := Y) (C := Z) ;; aswap ;; aassoc
  = aswap.sum nil ;; aassoc ;; nil.sum aswap
  := sorry

def Eqv.distl {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨(A.prod B).coprod (A.prod C), ⊥⟩::Γ) (A.prod (B.coprod C)::L) :=
  coprod (A ⋊ ret_inl) (A ⋊ ret_inr)

def Eqv.distl_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨A.prod (B.coprod C), ⊥⟩::Γ) ((A.prod B).coprod (A.prod C)::L) :=
  let2 (var 0 Ctx.Var.shead) $
  case (var 0 Ctx.Var.shead)
    (ret $ inl (pair (var 2 (by simp)) (var 0 Ctx.Var.shead)))
    (ret $ inr (pair (var 2 (by simp)) (var 0 Ctx.Var.shead)))

theorem Eqv.IsPure.distl {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (distl (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).IsPure := sorry

theorem Eqv.IsPure.distl_inv {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : (distl_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (L := L)).IsPure := sorry

-- TODO: "naturality"

def Eqv.control {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  : Eqv φ (⟨A.coprod B, ⊥⟩::Γ) (B::A::L) :=
  case (var 0 Ctx.Var.shead)
    (br 1 (var 0 (by simp)) ⟨by simp, le_refl _⟩)
    (ret (var 0 (by simp)))

def Eqv.fixpoint {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  : Eqv φ (⟨A, ⊥⟩::Γ) (B::L)
  := cfg [A] nil (λ| ⟨0, _⟩ => (f.vwk1.lwk ⟨Nat.liftWk Nat.succ, sorry⟩) ;; control)

theorem Eqv.fixpoint_iter {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  : fixpoint f = f ;; coprod nil (fixpoint f) := sorry

theorem Eqv.fixpoint_naturality {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  (g : Eqv φ (⟨B, ⊥⟩::Γ) (C::L))
  : fixpoint (f ;; sum g nil) = (fixpoint f) ;; g := sorry

theorem Eqv.fixpoint_dinaturality {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod C)::L))
  (g : Eqv φ (⟨C, ⊥⟩::Γ) ((B.coprod A)::L))
  : fixpoint (f ;; coprod ret_inl g) = f ;; coprod nil (fixpoint (g ;; coprod ret_inl f)) := sorry

theorem Eqv.fixpoint_codiagonal {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) (((B.coprod A).coprod A)::L))
  : fixpoint (f ;; coprod nil ret_inr) = fixpoint (fixpoint f) := sorry

theorem Eqv.fixpoint_uniformity {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L)) (g : Eqv φ (⟨C, ⊥⟩::Γ) ((B.coprod C)::L))
  (h : Eqv φ (⟨C, ⊥⟩::Γ) (A::L)) (hh : h.IsPure)
  (hfg : h ;; f = g ;; sum nil h)
  : h ;; (fixpoint f) = fixpoint g := sorry

theorem Eqv.fixpoint_strong_left {X A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L))
  : X ⋊ fixpoint f = fixpoint (X ⋊ f ;; distl_inv) := sorry

end Region

end BinSyntax
