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

def Eqv.pack {Γ : Ctx α ε} (h : ∀i, Γ.effect i ≤ e) : Eqv φ Γ (Γ.pack, e) := match Γ with
  | [] => unit e
  | V::Γ => pair
    (var 0 (Ctx.Var.head (by constructor; rfl; convert (h 0); simp) _))
    ((pack (Γ := Γ) (λi => by convert h (i + 1) using 1; simp)).wk0)

theorem Eqv.pack_def {Γ : Ctx α ε} {h : ∀i, Γ.effect i ≤ e}
  : Eqv.pack (φ := φ) (Γ := Γ) h = ⟦Term.InS.pack h⟧ := by
  induction Γ with
  | nil => rfl
  | cons _ _ I => simp only [pack, I]; rfl

abbrev _root_.BinSyntax.Ctx.Pure.packE {Γ : Ctx α ε} (h : Γ.Pure) : Eqv φ Γ (Γ.pack, ⊥)
  := Eqv.pack (e := ⊥) (h := λi => by simp [h.effect i])

theorem Eqv.packE_def' {Γ : Ctx α ε} {h : Γ.Pure} : h.packE (φ := φ) = ⟦h.pack⟧ := by
  simp only [Ctx.Pure.packE, pack_def]

@[simp]
theorem Eqv.wk_eff_pack {Γ : Ctx α ε} {h : ∀i, Γ.effect i ≤ lo} {h' : lo ≤ hi}
  : (pack (φ := φ) h).wk_eff h' = pack (λi => (h i).trans h') := by
  simp [pack_def]

theorem Eqv.wk_eff_packE {Γ : Ctx α ε} {h : Γ.Pure}
  : h.packE.wk_eff bot_le = pack (φ := φ) (e := hi) (λi => by simp [h.effect]) := by simp

@[simp]
theorem  _root_.BinSyntax.Ctx.Pure.packP {Γ : Ctx α ε} (h : Γ.Pure) (h')
  : Eqv.Pure (Eqv.pack (φ := φ) (Γ := Γ) (e := e) h')
  := ⟨h.packE, by simp⟩

def Eqv.pack_drop {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : Eqv φ ((Γ.pack, ⊥)::Δ) (Ctx.pack (Γ.drop i), e)
  := ⟦InS.pack_drop i⟧

theorem Eqv.Pure.pack_drop {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : Pure (pack_drop (φ := φ) (Δ := Δ) (e := e) i)
  := ⟨Eqv.pack_drop i, rfl⟩

def Eqv.pack_drop' {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : Eqv φ ((Γ.pack, ⊥)::Δ) ((Γ.get i).1.prod (Ctx.pack (Γ.drop (i + 1))), e)
  := ⟦InS.pack_drop' i⟧

theorem Eqv.Pure.pack_drop' {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : Pure (pack_drop' (φ := φ) (Δ := Δ) (e := e) i)
  := ⟨Eqv.pack_drop' i, rfl⟩

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

theorem Eqv.Pure.unpack0 {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : Pure (unpack0 (φ := φ) (Δ := Δ) (e := e) i)
  := ⟨Eqv.unpack0 i, rfl⟩

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

def Subst.Eqv.unpack {Γ Δ : Ctx α ε} : Subst.Eqv φ ((Γ.pack, ⊥)::Δ) Γ := ⟦Subst.InS.unpack⟧

def Eqv.packed {Γ Δ : Ctx α ε} (a : Eqv φ Γ V) : Eqv φ ((Γ.pack, ⊥)::Δ) V
  := a.subst Subst.Eqv.unpack

def Eqv.unpacked {Γ : Ctx α ε} (a : Eqv φ [(Γ.pack, ⊥)] (A, e)) (h : ∀i, Γ.effect i ≤ e)
  : Eqv φ Γ (A, e) := let1 (pack h) (a.wk_id (by simp [Ctx.Wkn.drop]))

-- theorem Eqv.packed_unpacked {Γ : Ctx α ε} {a : Eqv φ [(Γ.pack, ⊥)] (A, e)} (h : Γ.Pure)
--   : (a.unpacked (λi => by simp [h.effect])).packed = a := by
--   rw [
--     unpacked, <-wk_eff_packE (h := h), let1_beta, packed, subst_subst, <-wk_eq_wk_id,
--     <-subst_fromWk, subst_subst, subst_id'
--   ]
--   ext k; cases k using Fin.elim1
--   simp only [Fin.isValue, List.get_eq_getElem, List.length_singleton, Fin.val_zero,
--     List.getElem_cons_zero, Set.mem_setOf_eq, Subst.Eqv.get_comp, Subst.Eqv.get_fromWk,
--     Fin.zero_eta, Fin.coe_fin_one, id_eq, subst_var, List.length_cons, subst0_get_zero,
--      wk_res_self,
--     Subst.Eqv.get_id, Ctx.Pure.packE]
--   induction Γ with
--   | nil => apply Eqv.terminal
--   | cons V Γ I =>
--     simp [Eqv.pack, subst_var]
--     convert Eqv.Pure.pair_eta ⟨var 0 Ctx.Var.shead, rfl⟩
--     simp only [wk_eff_self]
--     sorry

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
