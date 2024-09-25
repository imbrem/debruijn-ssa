import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Product
import DeBruijnSSA.BinSyntax.Typing.Term.Structural

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

def Eqv.pack {Γ : Ctx α ε} (h : ∀i, Γ.effect i ≤ e) : Eqv φ Γ (Γ.pack, e) := match Γ with
  | [] => unit e
  | V::Γ => pair
    ((pack (Γ := Γ) (λi => by convert h (i + 1) using 1; simp)).wk0)
    (var 0 (Ctx.Var.head (by constructor; rfl; convert (h 0); simp) _))

theorem Eqv.pack_def {Γ : Ctx α ε} {h : ∀i, Γ.effect i ≤ e}
  : Eqv.pack (φ := φ) (Γ := Γ) h = ⟦Term.InS.pack h⟧ := by
  induction Γ with
  | nil => rfl
  | cons _ _ I => simp only [pack, I]; rfl

abbrev _root_.BinSyntax.Ctx.Pure.packE {Γ : Ctx α ε} (h : Γ.Pure) : Eqv φ Γ (Γ.pack, ⊥)
  := Eqv.pack (e := ⊥) (h := λi => by simp [h.effect i])

theorem Eqv.packE_def' {Γ : Ctx α ε} {h : Γ.Pure} : h.packE (φ := φ) = ⟦h.pack⟧ := by
  simp only [Ctx.Pure.packE, pack_def]

theorem Eqv.packE_cons {Γ : Ctx α ε} {h : Ctx.Pure (V::Γ)}
  : h.packE (φ := φ) = pair h.tail.packE.wk0 (var 0 (h.any_effect_refl (by simp)))
  := rfl

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
  : Eqv φ ((Γ.pack, ⊥)::Δ) ((Ctx.pack (Γ.drop (i + 1))).prod (Γ.get i).1, e)
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
  = (pack_drop' (φ := φ) (Γ := V::Γ) (Δ := Δ) (e := e) i.castSucc).pl := by
  simp only [pack_drop, InS.pack_drop_succ]; rfl

def Eqv.pi_n {Γ Δ : Ctx α ε} (i : Fin Γ.length) : Eqv φ ((Γ.pack, ⊥)::Δ) ((Γ.get i).1, e)
  := ⟦InS.pi_n i⟧

theorem Eqv.Pure.pi_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : Pure (pi_n (φ := φ) (Δ := Δ) (e := e) i)
  := ⟨Eqv.pi_n i, rfl⟩

@[simp]
theorem Eqv.wk1_pi_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (Eqv.pi_n (φ := φ) (Γ := Γ) (Δ := Δ) (e := e) i).wk1 (inserted := inserted) = pi_n i := by
  simp [pi_n]

@[simp]
theorem Eqv.wk2_pi_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (Eqv.pi_n (φ := φ) (Γ := Γ) (Δ := V::Δ) (e := e) i).wk2 (inserted := inserted)
  = pi_n i := by
  simp only [List.get_eq_getElem, wk2, ←Ctx.InS.lift_wk1, pi_n, wk_quot]
  apply congrArg
  ext
  rw [InS.coe_wk, InS.coe_pi_n, InS.coe_pi_n]
  exact wk_lift_pi_n

@[simp]
theorem Eqv.wk_lift_pi_n {Γ Δ : Ctx α ε} {i : Fin Γ.length} {ρ : Γ.InS Δ}
  : (Eqv.pi_n (φ := φ) (Γ := Γ) (Δ := Δ) (e := e) i).wk (ρ.lift (le_refl _)) = pi_n i := by
  simp [pi_n]

@[simp]
theorem Eqv.subst_lift_pi_n {Γ Δ Δ' : Ctx α ε} {i : Fin Γ.length} {σ : Subst.Eqv φ Δ' Δ}
  : (Eqv.pi_n (φ := φ) (Γ := Γ) (Δ := Δ) (e := e) i).subst (σ.lift (le_refl _)) = pi_n i := by
  induction σ using Quotient.inductionOn
  simp [pi_n]

@[simp]
theorem Eqv.subst0_nil_pl_pi_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (Eqv.pi_n (φ := φ) (Γ := Γ) (e := e) i).subst (nil.pl.subst0)
  = pi_n (φ := φ) (Γ := V::Γ) (Δ := Δ) i.succ := by
  apply eq_of_term_eq
  apply Term.subst0_nil_pl_pi_n

@[simp]
theorem Eqv.subst0_pi_l_pi_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (Eqv.pi_n (φ := φ) (Γ := Γ) (e := e) i).subst pi_l.subst0
  = pi_n (φ := φ) (Γ := V::Γ) (Δ := Δ) i.succ := subst0_nil_pl_pi_n

theorem Eqv.pr_pack_drop'  {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (Eqv.pack_drop' (φ := φ) (Δ := Δ) (e := e) i).pr = pi_n i := rfl

theorem Eqv.pi_n_def {Γ Δ : Ctx α ε} (i : Fin Γ.length) :
  Eqv.pi_n (φ := φ) (Δ := Δ) (e := e) i = ⟦Term.InS.pi_n i⟧ := rfl

theorem Eqv.pi_n_zero {Γ Δ : Ctx α ε}
  : Eqv.pi_n (φ := φ) (Γ := V::Γ) (Δ := Δ) (e := e) (0 : Fin (Γ.length + 1)) = pi_r := rfl

theorem Eqv.pi_n_zero' {Γ Δ : Ctx α ε}
  : Eqv.pi_n (φ := φ) (Γ := V::Γ) (Δ := Δ) (e := e) ⟨0, by simp⟩ = pi_r := rfl

theorem Eqv.pi_n_succ {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : pi_n (φ := φ) (Γ := V::Γ) (Δ := Δ) (e := e) i.succ = pi_l ;;' pi_n i := by
  rw [seq, <-wk_eff_pi_l, let1_beta, wk1_pi_n, subst0_pi_l_pi_n]

theorem Eqv.pi_n_succ' {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : pi_n (φ := φ) (Γ := V::Γ) (Δ := Δ) (e := e) ⟨i + 1, by simp⟩ = pi_l ;;' pi_n i
  := pi_n_succ i

theorem Eqv.pi_n_one {Γ Δ : Ctx α ε}
  : Eqv.pi_n (φ := φ) (Γ := V::V'::Γ) (Δ := Δ) (e := e) (1 : Fin (Γ.length + 2))
  = pi_l ;;' pi_r := by exact pi_n_succ (Γ := V'::Γ) (0 : Fin (Γ.length + 1))

-- def Eqv.pi_n' {Γ Δ : Ctx α ε} (i : Fin Γ.length) : Eqv φ ((Γ.pack, ⊥)::Δ) ((Γ.get i).1, e)
--   := match Γ with
--   | [] => i.elim0
--   | V::Γ => let2
--     (var (V := (V.1.prod (Ctx.pack Γ), e)) 0 (by simp [Ctx.pack]))
--     (i.cases (var 1 (by simp)) (λi => pi_n' i))

-- theorem Eqv.pi_n_def' {Γ Δ : Ctx α ε} (i : Fin Γ.length) :
--   pi_n' (φ := φ) (Δ := Δ) (e := e) i = ⟦Term.InS.pi_n' i⟧ := by
--   induction Γ generalizing Δ with
--   | nil => exact i.elim0
--   | cons _ _ I =>
--     simp only [
--       List.get_eq_getElem, List.length_cons, pi_n', var, Fin.val_zero,
--       List.getElem_cons_zero, I, InS.pi_n'
--     ]
--     cases i using Fin.cases <;> rfl

def Subst.Eqv.unpack {Γ Δ : Ctx α ε} : Subst.Eqv φ ((Γ.pack, ⊥)::Δ) Γ := ⟦Subst.InS.unpack⟧

@[simp]
theorem Subst.Eqv.get_unpack {Γ Δ : Ctx α ε} {i}
  : (unpack (φ := φ) (Γ := Γ) (Δ := Δ)).get i = Eqv.pi_n i
  := rfl

def _root_.BinSyntax.Ctx.Pure.packSE {Γ} (h : Γ.Pure) : Subst.Eqv φ Γ [(Γ.pack, ⊥)]
  := ⟦h.packS⟧

@[simp]
theorem Subst.Eqv.get_packSE_zero {Γ : Ctx α ε} (h : Γ.Pure)
  : (h.packSE (φ := φ)).get (0 : Fin 1) = h.packE
  := by simp only [Fin.isValue, List.get_eq_getElem, List.length_singleton, Fin.val_zero,
    List.getElem_cons_zero, Ctx.Pure.packSE, get_quot, Fin.getElem_fin, Ctx.Pure.packE,
    Eqv.pack_def]; congr; ext; simp [Ctx.Pure.packS, pack]

def Eqv.packed {Γ Δ : Ctx α ε} (a : Eqv φ Γ V) : Eqv φ ((Γ.pack, ⊥)::Δ) V
  := a.subst Subst.Eqv.unpack

@[simp]
theorem Eqv.packed_pair {Γ Δ : Ctx α ε} {A B : Ty α} {a : Eqv φ Γ (A, e)} {b : Eqv φ Γ (B, e)}
  : (pair a b).packed (Δ := Δ) = pair a.packed b.packed := by simp [packed]

@[simp]
theorem Eqv.wk_lift_packed {Γ Δ : Ctx α ε} {A : Ty α} {a : Eqv φ Γ (A, e)} {ρ : Ctx.InS Δ' Δ}
  : (a.packed).wk (ρ.lift (le_refl _)) = a.packed := by
  induction a using Quotient.inductionOn
  apply eq_of_term_eq
  simp only [Set.mem_setOf_eq, InS.coe_wk, Ctx.InS.coe_wk1, InS.coe_subst, Subst.InS.coe_unpack, ←
    Term.subst_fromWk, Term.subst_subst, Ctx.InS.coe_lift]
  congr
  funext k; simp only [Subst.comp, Term.subst_fromWk, Term.wk_lift_pi_n, Subst.pi_n]

@[simp]
theorem Eqv.wk_liftn₂_packed {Γ Δ : Ctx α ε} {A : Ty α} {a : Eqv φ Γ (A, e)} {ρ : Ctx.InS Δ' Δ}
  : (a.packed (Δ := V::Δ)).wk (ρ.liftn₂ (le_refl _) (le_refl _)) = a.packed := by
  simp [<-Ctx.InS.lift_lift]

@[simp]
theorem Eqv.subst_lift_packed {Γ Δ Δ' : Ctx α ε} {A : Ty α} {a : Eqv φ Γ (A, e)}
  {σ : Subst.Eqv φ Δ' Δ} : (a.packed).subst (σ.lift (le_refl _)) = a.packed := by
  induction a using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  apply eq_of_term_eq
  simp only [Set.mem_setOf_eq, InS.coe_subst, Subst.InS.coe_lift, InS.coe_wk, Subst.InS.coe_unpack,
    ←Term.subst_fromWk, Term.subst_subst]
  congr
  funext k; simp only [Subst.comp, Term.subst_fromWk, Term.subst_lift_pi_n, Subst.pi_n]

@[simp]
theorem Eqv.subst_liftn₂_packed {Γ Δ Δ' : Ctx α ε} {A : Ty α} {a : Eqv φ Γ (A, e)}
  {σ : Subst.Eqv φ Δ' Δ}
  : (a.packed (Δ := V::Δ)).subst (σ.liftn₂ (le_refl _) (le_refl _)) = a.packed := by
  simp [<-Subst.Eqv.lift_lift]

@[simp]
theorem Eqv.wk1_packed {Γ Δ : Ctx α ε} {A : Ty α} {a : Eqv φ Γ (A, e)}
  : (a.packed (Δ := Δ)).wk1 (inserted := inserted) = a.packed := wk_lift_packed (ρ := Ctx.InS.wk0)

@[simp]
theorem Eqv.wk2_packed {Γ Δ : Ctx α ε} {A : Ty α} {a : Eqv φ Γ (A, e)}
  : (a.packed (Δ := V::Δ)).wk2 (inserted := inserted) = a.packed := by
  simp only [wk2, <-Ctx.InS.lift_wk1, wk_lift_packed]

@[simp]
theorem Eqv.subst0_var0_packed {Γ Δ : Ctx α ε} {A : Ty α} {a : Eqv φ Γ (A, e)}
  : a.packed.subst (var 0 Ctx.Var.shead).subst0 = a.packed (Δ := Δ)
  := by rw [<-wk1_packed, subst0_var0_wk1]

def Eqv.unpacked {Γ : Ctx α ε} (a : Eqv φ [(Γ.pack, ⊥)] (A, e)) (h : Γ.Pure)
  : Eqv φ Γ (A, e) := let1 (pack (by simp [h.effect])) (a.wk_id (by simp [Ctx.Wkn.drop]))

theorem Eqv.unpacked_def' {Γ : Ctx α ε} {a : Eqv φ [(Γ.pack, ⊥)] (A, e)} {h : Γ.Pure}
  : a.unpacked (φ := φ) (Γ := Γ) h = a.subst h.packSE := by
  rw [unpacked, <-wk_eff_packE (h := h), let1_beta, <-wk_eq_wk_id, <-subst_fromWk, subst_subst]
  congr
  ext k; cases k using Fin.elim1
  simp [Subst.Eqv.get_comp]

theorem Eqv.packed_wk0 {Γ : Ctx α ε} {a : Eqv φ Γ (A, e)}
  : (a.wk0 (head := head)).packed (Δ := Δ) = pi_l ;;' a.packed := by
  rw [
    packed, wk0, <-subst_fromWk, subst_subst, seq, <-wk_eff_pi_l, let1_beta, wk1, <-subst_fromWk,
    subst_subst, packed, subst_subst
  ]
  congr 1; ext k
  simp only [List.get_eq_getElem, Subst.Eqv.get_comp, Subst.Eqv.get_fromWk, Fin.eta,
    Set.mem_setOf_eq, Ctx.InS.coe_wk0, Nat.succ_eq_add_one, subst_var, id_eq,
    List.getElem_cons_succ, List.length_cons, Subst.Eqv.get_unpack, wk_res_self, ← subst_subst,
    subst_fromWk]
  rw [<-wk1, wk1_pi_n, subst0_pi_l_pi_n]
  rfl

theorem Eqv.packed_packE {Γ : Ctx α ε} {h : Γ.Pure} : h.packE.packed (Δ := Δ) = nil (φ := φ) := by
  induction Γ generalizing Δ with
  | nil => exact Eqv.terminal
  | cons V Γ I =>
    rw [packE_cons, packed_pair]
    convert Eqv.Pure.pair_eta _
    · simp [packed_wk0, I]; rfl
    · rfl
    · simp

@[simp]
theorem Subst.Eqv.unpack_comp_packSE {Γ : Ctx α ε} (h : Γ.Pure)
  : unpack.comp h.packSE = Subst.Eqv.id (φ := φ) := by
  ext k; cases k using Fin.elim1
  simp only [Fin.isValue, List.get_eq_getElem, List.length_singleton, Fin.val_zero,
    List.getElem_cons_zero, get_comp, get_packSE_zero, get_id, Fin.coe_fin_one]
  exact Eqv.packed_packE

-- theorem Eqv.pi_n_eq_pi_n' {Γ Δ : Ctx α ε} (i : Fin Γ.length) :
--   Eqv.pi_n (φ := φ) (Δ := Δ) (e := e) i = Eqv.pi_n' i := by
--   induction Γ generalizing Δ with
--   | nil => exact i.elim0
--   | cons V Γ I =>
--   simp only [List.length_cons] at i
--   cases i using Fin.cases with
--   | zero => rfl
--   | succ =>
--     simp only [List.get_eq_getElem, List.length_cons, Fin.val_succ, List.getElem_cons_succ,
--       pi_n', Fin.val_zero, List.getElem_cons_zero, Fin.cases_succ, <-I]
--     rw [<-wk1_pi_n, <-wk1_pi_n, <-nil, <-pi_r_seq, pi_n_succ]

theorem Eqv.unpacked_pi_n {Γ : Ctx α ε} {h : Γ.Pure} {i}
  : (Eqv.pi_n (φ := φ) (e := e) i).unpacked h = var i (h.any_effect_refl i.prop)
  := by induction Γ with
  | nil => exact i.elim0
  | cons V Γ I => cases i using Fin.cases with
  | zero =>
    simp [pi_n_zero, unpacked_def', pi_r, nil, subst_var, pr, Subst.Eqv.get_liftn₂_one]
    rw [<-pr, pack, Pure.pr_pair]
    exact Pure.wk0 ⟨h.tail.packE, by simp⟩
  | succ i =>
    rw [unpacked_def', pi_n_succ, seq]
    simp only [List.get_eq_getElem, List.length_cons, Fin.val_succ, List.getElem_cons_succ,
      wk1_pi_n, subst_let1, subst_lift_pi_n]
    simp only [pi_l, pl, nil, subst_let2, subst_var, List.getElem_cons_zero, List.length_singleton,
      Fin.zero_eta, Fin.isValue, Subst.Eqv.get_packSE_zero, wk_res_eff, wk_eff_pack,
      List.getElem_cons_succ, List.length_cons, Nat.reduceAdd, Fin.mk_one, Subst.Eqv.get_liftn₂_one,
      List.get_eq_getElem, Fin.val_one, wk_eff_var]
    rw [<-pl, pack, Pure.pl_pair, <-wk1_pi_n, <-wk0_let1, <-wk0_var]
    apply congrArg
    exact I (h := h.tail)
    exact ⟨var 0 (h.any_effect_refl (by simp)), rfl⟩

@[simp]
theorem Subst.Eqv.packSE_comp_unpack {Γ : Ctx α ε} (h : Γ.Pure)
  : h.packSE.comp unpack = Subst.Eqv.id (φ := φ) := by
  ext k; simp only [List.get_eq_getElem, get_comp, get_unpack, get_id]
  rw [<-Eqv.unpacked_pi_n, Eqv.unpacked_def']

theorem Eqv.packed_unpacked {Γ : Ctx α ε} {a : Eqv φ [(Γ.pack, ⊥)] (A, e)} {h : Γ.Pure}
  : (a.unpacked h).packed = a := by simp [unpacked_def', packed, subst_subst]

theorem Eqv.unpacked_packed {Γ : Ctx α ε} {a : Eqv φ Γ (A, e)} {h : Γ.Pure}
  : a.packed.unpacked h = a := by simp [unpacked_def', packed, subst_subst]

theorem Eqv.packed_injective {Γ : Ctx α ε} {a b : Eqv φ Γ V} (hΓ : Γ.Pure)
  (h : a.packed (Δ := []) = b.packed) : a = b := by
  rw [<-unpacked_packed (a := a), <-unpacked_packed (a := b), h]; exact hΓ

theorem Eqv.unpacked_injective {Γ : Ctx α ε} {a b : Eqv φ [(Γ.pack, ⊥)] (A, e)} {hΓ : Γ.Pure}
  (h : a.unpacked hΓ = b.unpacked hΓ) : a = b := by
  rw [<-packed_unpacked (a := a), <-packed_unpacked (a := b), h]

@[simp]
theorem Eqv.packed_var {Γ : Ctx α ε} {i} {hv}
  : (var (V := V) i hv).packed (Δ := Δ)
  = (pi_n (φ := φ) (Γ := Γ) ⟨i, hv.length⟩).wk_res hv.get := by simp [packed, subst_var]

theorem Subst.Eqv.lift_unpack {Γ Δ : Ctx α ε}
  : (unpack (φ := φ) (Γ := Γ) (Δ := Δ)).lift (le_refl (A, ⊥))
  = ((Eqv.var 1 (by simp)).pair (Eqv.var 0 (by simp))).subst0.comp Subst.Eqv.unpack := by
  ext k
  cases k using Fin.cases with
  | zero =>
    simp [
      Subst.Eqv.get_comp, Eqv.pi_n_zero, Eqv.pi_r, Eqv.nil, Eqv.pr, Eqv.let2_pair,
      Eqv.let1_beta_var0, Eqv.let1_beta_var1]
  | succ k =>
    simp only [List.get_eq_getElem, List.length_cons, Fin.val_succ, List.getElem_cons_succ,
      get_lift_succ, get_unpack, get_comp, Eqv.pi_n_succ, Eqv.seq, Eqv.pi_l, Eqv.pl, Eqv.nil,
      Eqv.wk1_pi_n, Eqv.subst_let1, Eqv.subst_let2, Eqv.var0_subst0, Fin.zero_eta, Fin.val_zero,
      List.getElem_cons_zero, Eqv.wk_res_eff, Eqv.wk_eff_pair, Eqv.wk_eff_var,
      Eqv.subst_liftn₂_var_one, Eqv.let2_pair, Eqv.wk0_var, zero_add, Eqv.let1_beta_var1,
      Eqv.var_succ_subst0, Eqv.subst_lift_pi_n]
    rw [Eqv.wk0, <-Eqv.subst_fromWk]
    apply Eqv.eq_of_term_eq
    apply subst_eqOn_fvi
    intro i
    simp only [InS.coe_pi_n, fvi_pi_n]
    simp only [Set.mem_Iio, Nat.lt_one_iff, Set.mem_setOf_eq, Ctx.InS.coe_toSubst, Ctx.InS.coe_wk0,
      Subst.fromWk_apply, Nat.succ_eq_add_one, InS.coe_subst0, InS.coe_var]
    intro i; cases i; rfl

theorem Subst.Eqv.liftn₂_unpack {Γ Δ : Ctx α ε}
  : (unpack (φ := φ) (Γ := Γ) (Δ := Δ)).liftn₂ (le_refl (A, ⊥)) (le_refl (B, ⊥))
  = ((
    Eqv.pair (Eqv.pair (Eqv.var 2 (by simp)) (Eqv.var 1 (by simp))) (Eqv.var 0 (by simp))
  )).subst0.comp Subst.Eqv.unpack := by
  ext k
  cases k using Fin.cases with
  | zero =>
    simp only [List.get_eq_getElem, List.length_cons, Fin.val_zero, List.getElem_cons_zero,
      get_liftn₂_zero, get_comp, get_unpack, Eqv.pi_n_zero, Eqv.pi_r, Eqv.pr, Eqv.nil,
      Eqv.subst_let2, Eqv.var0_subst0, Fin.zero_eta, Eqv.wk_res_self, ge_iff_le, le_refl,
      Eqv.subst_liftn₂_var_zero, Eqv.let2_pair, Eqv.wk0_var, zero_add, Eqv.let1_beta_var1]
    rw [Eqv.let1_beta'
      (a' := (Eqv.pair (Eqv.var 2 (by simp)) (Eqv.var 1 (by simp)))) (h := by simp)]
    rfl
  | succ k =>
    cases k using Fin.cases with
    | zero =>
      simp [
        Subst.Eqv.get_comp, Eqv.pi_n_zero, Eqv.pi_r, Eqv.nil, Eqv.pl, Eqv.let2_pair,
        Eqv.let1_beta_var0, get_liftn₂_one,
      ]
      rw [Eqv.pi_n_one, Eqv.seq_pi_r]
      simp only [Eqv.pi_l, Eqv.subst_pl, Eqv.subst_pr, Eqv.nil_subst0, Eqv.wk_eff_self]
      rw [Eqv.Pure.pl_pair, Eqv.Pure.pr_pair] <;> simp
    | succ k =>
      simp only [List.length_cons, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ,
        get_liftn₂_succ, get_lift_succ, get_unpack, get_comp]
      rw [Eqv.pi_n_succ (Γ := _::Γ) (i := k.succ)]
      rw [Eqv.pi_n_succ]
      simp only [Eqv.seq, List.get_eq_getElem, List.length_cons, Fin.val_succ,
        List.getElem_cons_succ, Eqv.pi_l, Eqv.nil, Eqv.wk1_pi_n, Eqv.wk1_let1, Eqv.wk1_pl,
        Eqv.wk1_var0, Fin.zero_eta, Fin.val_zero, List.getElem_cons_zero, Eqv.wk2_pi_n,
        Eqv.subst_let1, Eqv.subst_pl, Eqv.var0_subst0, Eqv.wk_res_eff, Eqv.wk_eff_pair,
        Eqv.wk_eff_var, Eqv.subst_lift_var_zero, Eqv.subst_lift_pi_n]
      rw [Eqv.Pure.pl_pair]
      rw [Eqv.let1_beta'
        (a' := (Eqv.pair (Eqv.var 2 (by simp)) (Eqv.var 1 (by simp)))) (h := by simp)]
      simp only [Eqv.subst_let1, Eqv.subst_pl, Eqv.var0_subst0, List.length_cons, Nat.add_zero,
        Nat.zero_eq, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
        Eqv.wk_res_eff, Eqv.wk_eff_pair, Eqv.wk_eff_var, Eqv.subst_lift_pi_n]
      rw [Eqv.Pure.pl_pair, Eqv.let1_beta_var2, Eqv.wk0, Eqv.wk0, Eqv.wk_wk, <-Eqv.subst_fromWk]
      apply Eqv.eq_of_term_eq
      apply subst_eqOn_fvi
      intro i
      rw [InS.coe_pi_n, fvi_pi_n]
      simp only [Set.mem_Iio, Nat.lt_one_iff, Set.mem_setOf_eq, Ctx.InS.coe_toSubst,
        Ctx.InS.coe_comp, Ctx.InS.coe_wk0, fromWk_apply, Function.comp_apply, Nat.succ_eq_add_one,
        InS.coe_subst0, Term.InS.coe_var]
      intro h; cases h; rfl
      exact ⟨Eqv.var 1 (by simp), rfl⟩
      exact ⟨Eqv.var 0 (by simp), rfl⟩

theorem Eqv.packed_let1 {Γ : Ctx α ε} {A B : Ty α}
  {a : Eqv φ Γ (A, e)} {b : Eqv φ ((A, ⊥)::Γ) (B, e)}
  : (let1 a b).packed (Δ := Δ)
  = let1 a.packed (let1 (pair (var 1 (by simp)) (var 0 (by simp))) b.packed) := by
  rw [packed, subst_let1]; apply congrArg
  rw [
    packed, let1_beta' (a' := pair (var 1 (by simp)) (var 0 (by simp))) (h := by simp),
    subst_subst, Subst.Eqv.lift_unpack
  ]

theorem Eqv.packed_let2 {Γ : Ctx α ε} {A B C : Ty α}
  {a : Eqv φ Γ (A.prod B, e)} {b : Eqv φ ((B, ⊥)::(A, ⊥)::Γ) (C, e)}
  : (let2 a b).packed (Δ := Δ)
  = let2 a.packed (
      let1 (pair (pair (var 2 (by simp)) (var 1 (by simp))) (var 0 (by simp))) b.packed) := by
  rw [packed, subst_let2]; congr
  rw [
    packed,
    let1_beta'
      (a' := pair (pair (var 2 (by simp)) (var 1 (by simp))) (var 0 (by simp))) (h := by simp),
    subst_subst, Subst.Eqv.liftn₂_unpack,
  ]

theorem Eqv.packed_case {Γ : Ctx α ε} {A B : Ty α}
  {a : Eqv φ Γ (A.coprod B, e)} {l : Eqv φ ((A, ⊥)::Γ) (C, e)} {r : Eqv φ ((B, ⊥)::Γ) (C, e)}
  : (case a l r).packed (Δ := Δ)
  = case a.packed
    (let1 (pair (var 1 (by simp)) (var 0 (by simp))) l.packed)
    (let1 (pair (var 1 (by simp)) (var 0 (by simp))) r.packed) := by
  rw [packed, subst_case]; congr <;> rw [
    packed, let1_beta' (a' := pair (var 1 (by simp)) (var 0 (by simp))) (h := by simp),
    subst_subst, Subst.Eqv.lift_unpack
  ]

@[simp]
theorem Eqv.packed_inl {Γ : Ctx α ε} {A B : Ty α} {a : Eqv φ Γ (A, e)}
  : (inl (B := B) a).packed (Δ := Δ) = inl a.packed := by simp [packed]

@[simp]
theorem Eqv.packed_inr {Γ : Ctx α ε} {A B : Ty α} {a : Eqv φ Γ (B, e)}
  : (inr (A := A) a).packed (Δ := Δ) = inr a.packed := by simp [packed]

@[simp]
theorem Eqv.packed_abort {Γ : Ctx α ε} {A : Ty α} {a : Eqv φ Γ (Ty.empty, e)}
  : (abort a A).packed (Δ := Δ) = abort a.packed A := by simp [packed]

@[simp]
theorem Eqv.packed_unit {Γ : Ctx α ε} : (unit (φ := φ) (Γ := Γ) (e := e)).packed (Δ := Δ) = unit _
  := rfl

end Term
