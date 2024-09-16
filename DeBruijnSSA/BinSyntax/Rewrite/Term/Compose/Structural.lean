import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Seq
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Product
import DeBruijnSSA.BinSyntax.Typing.Term.Structural


namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

def Eqv.pack_sum {Γ : Ctx α ε} (R : LCtx α) (i : Fin R.length) : Eqv φ ((R.get i, ⊥)::Γ) (R.pack, ⊥)
  := match R with
  | [] => i.elim0
  | _::R => i.cases (inl nil) (λi => inr (pack_sum R i))

theorem Eqv.pack_sum_def {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : Eqv.pack_sum (φ := φ) (Γ := Γ) R i = ⟦Term.InS.pack0 R i⟧ := by
  induction R generalizing Γ with
  | nil => exact i.elim0
  | cons _ _ I =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      simp only [pack_sum, I, inr_quot, Fin.cases_succ]
      apply congrArg
      ext
      simp [Term.pack0, Term.Wf.pack0, -Function.iterate_succ, Function.iterate_succ']

def Eqv.pack' {Γ : Ctx α ε} : Eqv φ Γ (Γ.pack, Γ.sup_effect) := match Γ with
  | [] => unit ⊥
  | V::Γ => pair (var 0 (by cases V; simp)) ((pack' (Γ := Γ)).wk0.wk_eff (by simp))

theorem Eqv.pack_def' {Γ : Ctx α ε} : Eqv.pack' (φ := φ) (Γ := Γ) = ⟦Term.InS.pack'⟧ := by
  induction Γ with
  | nil => rfl
  | cons _ _ I => simp only [pack', I]; rfl

def _root_.BinSyntax.Ctx.Pure.packE' {Γ : Ctx α ε} (h : Γ.Pure) : Eqv φ Γ (Γ.pack, ⊥) := match Γ with
  | [] => Eqv.unit ⊥
  | V::Γ => Eqv.pair (Eqv.var 0 (by cases V; convert h.head; simp)) h.tail.packE'.wk0

theorem Eqv.packE_def' {Γ : Ctx α ε} {h : Γ.Pure} : h.packE' (φ := φ) = ⟦h.pack'⟧ := by
  induction Γ with
  | nil => rfl
  | cons _ _ I => simp only [Ctx.Pure.packE', I]; rfl

def Eqv.pack_drop {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : Eqv φ ((Γ.pack, ⊥)::Δ) (Ctx.pack (Γ.drop i), e)
  := ⟦InS.pack_drop i⟧

def Eqv.pack_drop' {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : Eqv φ ((Γ.pack, ⊥)::Δ) ((Γ.get i).1.prod (Ctx.pack (Γ.drop (i + 1))), e)
  := ⟦InS.pack_drop' i⟧

theorem Eqv.cast_pack_drop {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (Eqv.pack_drop (φ := φ) (Δ := Δ) (e := e) i).cast rfl (by rw [Ctx.pack_drop_fin]) = pack_drop' i
  := rfl

theorem Eqv.cast_pack_drop' {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (Eqv.pack_drop' (φ := φ) (Δ := Δ) (e := e) i).cast rfl (by rw [<-Ctx.pack_drop_fin])
  = pack_drop i
  := rfl

def Eqv.pack_drop_succ {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : pack_drop (φ := φ)  (Γ := V::Γ) (Δ := Δ) (e := e) i.succ
  = (pack_drop' (φ := φ) (Γ := V::Γ) (Δ := Δ) (e := e) i.castSucc).pr := by
  simp only [pack_drop, InS.pack_drop_succ]; rfl

def Eqv.unpack0 {Γ Δ : Ctx α ε} (i : Fin Γ.length) : Eqv φ ((Γ.pack, ⊥)::Δ) ((Γ.get i).1, e)
  := ⟦InS.unpack0 i⟧

theorem Eqv.pl_pack_drop'  {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (Eqv.pack_drop' (φ := φ) (Δ := Δ) (e := e) i).pl = unpack0 i := rfl

theorem Eqv.unpack0_def {Γ Δ : Ctx α ε} (i : Fin Γ.length) :
  Eqv.unpack0 (φ := φ) (Δ := Δ) (e := e) i = ⟦Term.InS.unpack0 i⟧ := rfl

def Eqv.unpack0' {Γ Δ : Ctx α ε} (i : Fin Γ.length) : Eqv φ ((Γ.pack, ⊥)::Δ) ((Γ.get i).1, e)
  := match Γ with
  | [] => i.elim0
  | V::Γ => let2
    (var (V := (V.1.prod (Ctx.pack Γ), e)) 0 (by simp [Ctx.pack]))
    (i.cases (var 1 (by simp)) (λi => unpack0' i))

theorem Eqv.unpack0_def' {Γ Δ : Ctx α ε} (i : Fin Γ.length) :
  unpack0' (φ := φ) (Δ := Δ) (e := e) i = ⟦Term.InS.unpack0' i⟧ := by
  induction Γ generalizing Δ with
  | nil => exact i.elim0
  | cons _ _ I =>
    simp only [
      List.get_eq_getElem, List.length_cons, unpack0', var, Fin.val_zero,
      List.getElem_cons_zero, I, InS.unpack0'
    ]
    cases i using Fin.cases <;> rfl

-- theorem Eqv.unpack0_eq_unpack0' {Γ Δ : Ctx α ε} (i : Fin Γ.length) :
--   Eqv.unpack0 (φ := φ) (Δ := Δ) (e := e) i = Eqv.unpack0' i := by
--   cases Γ with
--   | nil => exact i.elim0
--   | cons V Γ =>
--   induction i using Fin.induction generalizing Δ with
--   | zero => rfl
--   | succ =>
--     simp [unpack0', <-pl_pack_drop', <-cast_pack_drop, pack_drop_succ]
--     sorry

-- TODO: wk lift unpack

-- TODO: let1 pack (unpack i) = var i

-- TODO: need InS version for this... :(

-- def Subst.Eqv.unpacked {Γ Δ : Ctx α ε} (i : Fin Γ.length) : Subst.Eqv φ ((Γ.pack, ⊥)::Δ) Γ
--   := sorry

end Term
