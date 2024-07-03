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
  : InS φ (⟨tyIn, ⊥⟩::rest) (tyOut::targets) := ⟨Region.ret t, Wf.ret t.prop⟩

abbrev Eqv.ret {tyIn tyOut : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  (t : Term.InS φ (⟨tyIn, ⊥⟩::rest) ⟨tyOut, ⊥⟩)
  : Eqv φ (⟨tyIn, ⊥⟩::rest) (tyOut::targets) := ⟦InS.ret t⟧

theorem Wf.nil {ty : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  : Region.nil.Wf (φ := φ) (⟨ty, ⊥⟩::rest) (ty::targets) := Wf.ret (by simp)

def InS.nil {ty : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  : InS φ (⟨ty, ⊥⟩::rest) (ty::targets)  := ⟨Region.nil, Wf.nil⟩

-- theorem InS.coe_nil {ty : Ty α} {rest: Ctx α ε} {targets : LCtx α}
--   : (InS.nil (ty := ty) (rest := rest) (targets := targets) : Region φ) = Region.nil := rfl

abbrev Eqv.nil {ty : Ty α} {rest: Ctx α ε} {targets : LCtx α}
  : Eqv φ (⟨ty, ⊥⟩::rest) (ty::targets) := ⟦InS.nil⟧

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

def Eqv.alpha0 {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α} (r : Eqv φ (⟨A, ⊥⟩::Γ) (B::L))
  : Subst.Eqv φ Γ (A::L) (B::L)
  := Quot.liftOn r (λr => ⟦InS.alpha0 r⟧) (λ_ _ h => Quotient.sound $ InS.alpha0_congr h)

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
  cases l; simp [InS.nil, append_mk, Region.append_nil]

@[simp]
theorem InS.nil_append {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : InS φ (⟨A, ⊥⟩::Γ) (B::L)}
  : (InS.nil (φ := φ) (ty := A) (rest := Γ) (targets := L) ++ l) = l := by
  cases l; simp [InS.nil, append_mk, Region.nil_append]

theorem InS.append_assoc {A B C D : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L))
  (middle : InS φ (⟨B, ⊥⟩::Γ) (C::L))
  (right : InS φ (⟨C, ⊥⟩::Γ) (D::L))
  : (left ++ middle) ++ right = left ++ (middle ++ right) := by
  cases left; cases middle; cases right;
  simp [append_mk, Region.append_assoc]

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

theorem Eqv.swap_swap {left right : Ty α}
  : Eqv.swap ;; Eqv.swap
  = (Eqv.nil (φ := φ) (ty := left.prod right) (rest := rest) (targets := targets)) := by
  rw [Eqv.seq_def, swap, vwk1, swap]
  sorry

infixl:70 " ⋊ "  => Eqv.rtimes

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
