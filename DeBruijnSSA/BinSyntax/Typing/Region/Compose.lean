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

def InS.wseq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) (C::L)) : InS φ (⟨A, ⊥⟩::Γ) (C::L)
  := cfg [B] left.lwk1 (Fin.elim1 right.lwk0.vwk1)

@[simp]
theorem InS.coe_wseq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {left : InS φ (⟨A, ⊥⟩::Γ) (B::L)} {right : InS φ (⟨B, ⊥⟩::Γ) (C::L)}
  : ((left.wseq right) : Region φ) = (left : Region φ).wseq (right : Region φ) := by
  simp only [wseq, coe_cfg, coe_lwk1]
  congr
  funext i
  cases i using Fin.elim1
  rfl

theorem Wf.wseq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α} {left right : Region φ}
  (hleft : Region.Wf (⟨A, ⊥⟩::Γ) left (B::L)) (hright : Region.Wf (⟨B, ⊥⟩::Γ) right (C::L))
  : (left.wseq right).Wf (⟨A, ⊥⟩::Γ) (C::L)
  := by
  have h := (InS.wseq ⟨left, hleft⟩ ⟨right, hright⟩).prop
  simp at h
  exact h

def InS.wrseq {B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ Γ (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) (C::L)) : InS φ Γ (C::L)
  := cfg [B] left.lwk1 (Fin.elim1 right.lwk0)

@[simp]
theorem InS.coe_wrseq {B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {left : InS φ Γ (B::L)} {right : InS φ (⟨B, ⊥⟩::Γ) (C::L)}
  : ((left.wrseq right) : Region φ) = (left : Region φ).wrseq (right : Region φ) := by
  simp only [wrseq, coe_cfg, coe_lwk1]
  congr
  funext i
  cases i using Fin.elim1
  rfl

theorem Wf.wrseq {B C : Ty α} {Γ : Ctx α ε} {L : LCtx α} {left right : Region φ}
  (hleft : Region.Wf Γ left (B::L)) (hright : Region.Wf (⟨B, ⊥⟩::Γ) right (C::L))
  : (left.wrseq right).Wf Γ (C::L)
  := by
  have h := (InS.wrseq ⟨left, hleft⟩ ⟨right, hright⟩).prop
  simp at h
  exact h

def InS.wthen {B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ Γ (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) L) : InS φ Γ L
  := cfg [B] left (Fin.elim1 right.lwk0)

@[simp]
theorem InS.coe_wthen {B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {left : InS φ Γ (B::L)} {right : InS φ (⟨B, ⊥⟩::Γ) L}
  : ((left.wthen right) : Region φ) = (left : Region φ).wthen (right : Region φ) := by
  simp only [wthen, coe_cfg]
  congr
  funext i
  cases i using Fin.elim1
  rfl

theorem Wf.wthen {B : Ty α} {Γ : Ctx α ε} {L : LCtx α} {left right : Region φ}
  (hleft : Region.Wf Γ left (B::L)) (hright : Region.Wf (⟨B, ⊥⟩::Γ) right L)
  : (left.wthen right).Wf Γ L
  := by
  have h := (InS.wthen ⟨left, hleft⟩ ⟨right, hright⟩).prop
  simp at h
  exact h

theorem InS.wseq_eq_wrseq {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) (C::L))
  : left.wseq right = left.wrseq right.vwk1 := by ext; simp [Region.wseq_eq_wrseq]

theorem InS.wseq_eq_wthen {A B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ (⟨A, ⊥⟩::Γ) (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) (C::L))
  : left.wseq right = left.lwk1.wthen right.vwk1 := by ext; simp [Region.wseq_eq_wthen]

theorem InS.wrseq_eq_wthen {B C : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  (left : InS φ Γ (B::L)) (right : InS φ (⟨B, ⊥⟩::Γ) (C::L))
  : left.wrseq right = left.lwk1.wthen right := by ext; simp [Region.wrseq_eq_wthen]

theorem InS.vwk_lift_wseq {A B C : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {ρ : Ctx.InS Γ Δ}
  {left : InS φ (⟨A, ⊥⟩::Δ) (B::L)}
  {right : InS φ (⟨B, ⊥⟩::Δ) (C::L)}
  : (left.wseq right).vwk (ρ.lift (le_refl _))
  = (left.vwk (ρ.lift (le_refl _))).wseq (right.vwk (ρ.lift (le_refl _))) := by
  ext; simp only [coe_vwk, coe_wseq, Ctx.InS.coe_lift, Region.vwk_lift_wseq]

theorem InS.vwk_slift_wseq {A B C : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {ρ : Ctx.InS Γ Δ}
  {left : InS φ (⟨A, ⊥⟩::Δ) (B::L)}
  {right : InS φ (⟨B, ⊥⟩::Δ) (C::L)}
  : (left.wseq right).vwk ρ.slift
  = (left.vwk ρ.slift).wseq (right.vwk ρ.slift) := vwk_lift_wseq

theorem InS.lwk_lift_wseq {A B C : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
  {ρ : LCtx.InS L K}
  {left : InS φ (⟨A, ⊥⟩::Γ) (B::L)}
  {right : InS φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (left.wseq right).lwk (ρ.lift (le_refl _))
  = (left.lwk (ρ.lift (le_refl _))).wseq (right.lwk (ρ.lift (le_refl _))) := by
  ext; simp only [coe_lwk, coe_wseq, LCtx.InS.coe_lift, Region.lwk_lift_wseq]

theorem InS.lwk_slift_wseq {A B C : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
  {ρ : LCtx.InS L K}
  {left : InS φ (⟨A, ⊥⟩::Γ) (B::L)}
  {right : InS φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (left.wseq right).lwk ρ.slift
  = (left.lwk ρ.slift).wseq (right.lwk ρ.slift) := lwk_lift_wseq

theorem InS.vwk_wrseq {B C : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {ρ : Ctx.InS Γ Δ}
  {left : InS φ Δ (B::L)}
  {right : InS φ (⟨B, ⊥⟩::Δ) (C::L)}
  : (left.wrseq right).vwk ρ
  = (left.vwk ρ).wrseq (right.vwk ρ.slift) := by
  ext; simp only [coe_vwk, coe_wrseq, Ctx.InS.coe_lift, Region.vwk_wrseq]

theorem InS.lwk_lift_wrseq {B C : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
  {ρ : LCtx.InS L K}
  {left : InS φ Γ (B::L)}
  {right : InS φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (left.wrseq right).lwk (ρ.lift (le_refl _))
  = (left.lwk (ρ.lift (le_refl _))).wrseq (right.lwk (ρ.lift (le_refl _))) := by
  ext; simp only [coe_lwk, coe_wrseq, LCtx.InS.coe_lift, Region.lwk_lift_wrseq]

theorem InS.lwk_slift_wrseq {B C : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
  {ρ : LCtx.InS L K}
  {left : InS φ Γ (B::L)}
  {right : InS φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (left.wrseq right).lwk ρ.slift
  = (left.lwk ρ.slift).wrseq (right.lwk ρ.slift) := lwk_lift_wrseq

theorem InS.vwk_wthen {B : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {ρ : Ctx.InS Γ Δ}
  {left : InS φ Δ (B::L)}
  {right : InS φ (⟨B, ⊥⟩::Δ) L}
  : (left.wthen right).vwk ρ
  = (left.vwk ρ).wthen (right.vwk ρ.slift) := by
  ext; simp only [coe_vwk, coe_wthen, Ctx.InS.coe_lift, Region.vwk_wthen]

theorem InS.lwk_wthen {B : Ty α} {Γ : Ctx α ε} {L K : LCtx α}
  {ρ : LCtx.InS L K}
  {left : InS φ Γ (B::L)}
  {right : InS φ (⟨B, ⊥⟩::Γ) L}
  : (left.wthen right).lwk ρ
  = (left.lwk ρ.slift).wthen (right.lwk ρ) := by
  ext; simp only [coe_lwk, coe_wthen, LCtx.InS.coe_slift, Region.lwk_wthen]

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

theorem InS.vwk_lift_fixpoint {A B : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {r : InS φ (⟨A, ⊥⟩::Δ) ((B.coprod A)::L)}
  {ρ : Ctx.InS Γ Δ}
  : r.fixpoint.vwk ρ.slift = (r.vwk ρ.slift).fixpoint := by
  ext
  simp only [coe_fixpoint, coe_vwk, Ctx.InS.coe_slift, Region.vwk_lift_fixpoint]

theorem InS.vsubst_lift_fixpoint {A B : Ty α} {Γ Δ : Ctx α ε} {L : LCtx α}
  {r : InS φ (⟨A, ⊥⟩::Δ) ((B.coprod A)::L)}
  {σ : Term.Subst.InS φ Γ Δ}
  : r.fixpoint.vsubst (σ.lift (le_refl _)) = (r.vsubst (σ.lift (le_refl _))).fixpoint := by
  ext
  simp only [coe_fixpoint, coe_vsubst, Term.Subst.InS.coe_lift, Region.vsubst_lift_fixpoint]

def InS.cfgSubst {Γ : Ctx α ε} {L : LCtx α} (R : LCtx α)
  (G : ∀i : Fin R.length, InS φ ((R.get i, ⊥)::Γ) (R ++ L))
  : Subst.InS φ Γ (R ++ L) L := ⟨
    Region.cfgSubst R.length (λi => G i),
    λℓ => Wf.cfg (hR := rfl)
      (Wf.br ⟨ℓ.prop, by simp⟩ (Term.Wf.var Ctx.Var.shead))
      (λi => (G i).prop.vwk1)⟩

@[simp]
theorem InS.coe_cfgSubst {Γ : Ctx α ε} {L : LCtx α} (R : LCtx α)
  (G : ∀i : Fin R.length, InS φ ((R.get i, ⊥)::Γ) (R ++ L))
  : (InS.cfgSubst R G : Region.Subst φ) = Region.cfgSubst R.length (λi => G i) := rfl

theorem InS.vlift_cfgSubst {Γ : Ctx α ε} {L : LCtx α} (R : LCtx α)
  (G : ∀i : Fin R.length, InS φ ((R.get i, ⊥)::Γ) (R ++ L))
  : (InS.cfgSubst R G).vlift = InS.cfgSubst R (λi => (G i).vwk1 (inserted := inserted)) := by
  ext k
  simp only [
    Region.Subst.vlift, Region.cfgSubst, Subst.InS.coe_vlift, coe_cfgSubst, coe_vwk1,
    Function.comp_apply, Region.vwk1, Region.vwk, Term.wk, Nat.liftWk, Region.vwk_vwk
  ]
  congr
  funext ℓ
  congr
  funext k
  cases k <;> rfl

def InS.cfgSubst' {Γ : Ctx α ε} {L : LCtx α} (R : LCtx α)
  (G : ∀i : Fin R.length, InS φ ((R.get i, ⊥)::Γ) (R ++ L))
  : Subst.InS φ Γ (R ++ L) L := ⟨
    Region.cfgSubst' R.length (λi => G i),
    λℓ => if h : ℓ < R.length then by
        simp only [Region.cfgSubst', h, ↓reduceIte]
        exact Wf.cfg (hR := rfl)
          (Wf.br ⟨ℓ.prop, by simp⟩ (Term.Wf.var Ctx.Var.shead))
          (λi => (G i).prop.vwk1)
      else by
        simp only [Region.cfgSubst', h, ↓reduceIte]
        apply Wf.br _ (Term.Wf.var Ctx.Var.shead)
        constructor
        · simp only [List.get_eq_getElem]
          rw [List.getElem_append_right]
          exact h
        · rw [Nat.sub_lt_iff_lt_add (Nat.le_of_not_lt h)]
          have h := ℓ.prop
          simp at h
          exact h
    ⟩

@[simp]
theorem InS.coe_cfgSubst' {Γ : Ctx α ε} {L : LCtx α} (R : LCtx α)
  (G : ∀i : Fin R.length, InS φ ((R.get i, ⊥)::Γ) (R ++ L))
  : (InS.cfgSubst' R G : Region.Subst φ) = Region.cfgSubst' R.length (λi => G i) := rfl

def InS.ucfg {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α) (β : InS φ Γ (R ++ L)) (G : ∀i : Fin R.length, InS φ ((R.get i, ⊥)::Γ) (R ++ L))
  : InS φ Γ L := β.lsubst (InS.cfgSubst R G)

@[simp]
theorem InS.coe_ucfg {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α) (β : InS φ Γ (R ++ L)) (G : ∀i : Fin R.length, InS φ ((R.get i, ⊥)::Γ) (R ++ L))
  : (InS.ucfg R β G : Region φ) = Region.ucfg R.length β (λi => (G i)) := rfl

theorem Wf.ucfg {Γ : Ctx α ε} {L : LCtx α}
  (n : ℕ) (R : LCtx α) (hR : R.length = n)
  {β : Region φ} {G : Fin n → Region φ}
  (dβ : β.Wf Γ (R ++ L)) (dG : ∀i : Fin n, (G i).Wf ((R.get (i.cast hR.symm), ⊥)::Γ) (R ++ L))
  : (Region.ucfg n β G).Wf Γ L
  := by cases hR; exact (InS.ucfg R ⟨β, dβ⟩ (λi => ⟨G i, dG i⟩)).prop

def InS.ucfg' {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α) (β : InS φ Γ (R ++ L)) (G : ∀i : Fin R.length, InS φ ((R.get i, ⊥)::Γ) (R ++ L))
  : InS φ Γ L := β.lsubst (InS.cfgSubst' R G)

@[simp]
theorem InS.coe_ucfg' {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α) (β : InS φ Γ (R ++ L)) (G : ∀i : Fin R.length, InS φ ((R.get i, ⊥)::Γ) (R ++ L))
  : (InS.ucfg' R β G : Region φ) = Region.ucfg' R.length β (λi => (G i)) := rfl

theorem Wf.ucfg' {Γ : Ctx α ε} {L : LCtx α}
  (n : ℕ) (R : LCtx α) (hR : R.length = n)
  {β : Region φ} {G : Fin n → Region φ}
  (dβ : β.Wf Γ (R ++ L)) (dG : ∀i : Fin n, (G i).Wf ((R.get (i.cast hR.symm), ⊥)::Γ) (R ++ L))
  : (Region.ucfg' n β G).Wf Γ L
  := by cases hR; exact (InS.ucfg' R ⟨β, dβ⟩ (λi => ⟨G i, dG i⟩)).prop

def Wf.lsubst0 {Γ : Ctx α ε} {L : LCtx α} {r : Region φ} (hr : r.Wf (⟨A, ⊥⟩::Γ) L)
  : r.lsubst0.Wf Γ (A::L) L
  := Fin.cases hr (λi => Wf.br ⟨i.prop, le_refl _⟩ (by simp))

def InS.lsubst0 {A : Ty α} {Γ : Ctx α ε} {L : LCtx α} (r : InS φ (⟨A, ⊥⟩::Γ) L)
  : Subst.InS φ Γ (A::L) L
  := ⟨(r : Region φ).lsubst0, r.prop.lsubst0⟩

@[simp]
theorem InS.coe_lsubst0 {A : Ty α} {Γ : Ctx α ε} {L : LCtx α} (r : InS φ (⟨A, ⊥⟩::Γ) L)
  : (r.lsubst0 : Region.Subst φ) = (r : Region φ).lsubst0 := rfl

def loop : Region φ := cfg (br 0 Term.unit) 1 (Fin.elim1 (br 0 (Term.var 0)))

@[simp]
theorem vwk_loop : loop.vwk ρ = loop (φ := φ) := by
  simp only [vwk, Term.wk, loop, cfg.injEq, heq_eq_eq, true_and]
  funext i
  cases i using Fin.elim1
  rfl

@[simp]
theorem lwk_loop : loop.lwk ρ = loop (φ := φ) := by
  simp only [lwk, Nat.liftnWk, zero_lt_one, ↓reduceIte, loop, cfg.injEq, heq_eq_eq, true_and]
  funext i
  cases i using Fin.elim1
  rfl

@[simp]
theorem vsubst_loop {σ : Term.Subst φ} : loop.vsubst σ = loop (φ := φ) := by
  simp only [vsubst, loop, cfg.injEq, heq_eq_eq, true_and, Term.subst]
  funext i
  cases i using Fin.elim1
  rfl

@[simp]
theorem lsubst_loop {σ : Subst φ} : loop.lsubst σ = loop (φ := φ) := by
  simp only [lsubst, vsubst, loop, cfg.injEq, heq_eq_eq, true_and, Term.subst, Term.subst0]
  funext i
  cases i using Fin.elim1
  rfl

@[simp]
theorem Wf.loop {Γ : Ctx α ε} {L : LCtx α} : Wf Γ (loop (φ := φ)) L
  := Wf.cfg 1 [Ty.unit] rfl
    (Wf.br LCtx.Trg.shead (by simp))
    (Fin.elim1 (Wf.br LCtx.Trg.shead (by simp)))

def InS.loop : InS φ Γ L := ⟨Region.loop, Wf.loop⟩

@[simp]
theorem InS.coe_loop {Γ : Ctx α ε} {L : LCtx α}
  : (InS.loop (φ := φ) (Γ := Γ) (L := L) : Region φ) = Region.loop := rfl

@[simp]
theorem InS.vwk_loop {Γ Δ : Ctx α ε} {L : LCtx α} {ρ : Ctx.InS Γ Δ}
  : InS.loop.vwk ρ = InS.loop (φ := φ) (L := L) := ext Region.vwk_loop

@[simp]
theorem InS.vsubst_loop {Γ Δ : Ctx α ε} {L : LCtx α} {σ : Term.Subst.InS φ Γ Δ}
  : InS.loop.vsubst σ = InS.loop (φ := φ) (L := L) := ext Region.vsubst_loop

@[simp]
theorem InS.lwk_loop {Γ : Ctx α ε} {L K : LCtx α} {ρ : LCtx.InS L K}
  : InS.loop.lwk ρ = InS.loop (φ := φ) (Γ := Γ) := ext Region.lwk_loop

@[simp]
theorem InS.lsubst_loop {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K}
  : InS.loop.lsubst σ = InS.loop (φ := φ) := ext Region.lsubst_loop
