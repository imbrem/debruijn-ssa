import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Seq
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Product
import DeBruijnSSA.BinSyntax.Typing.Term.Structural

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

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

theorem Eqv.packE_cons {Γ : Ctx α ε} {h : Ctx.Pure (V::Γ)}
  : h.packE (φ := φ) = pair (var 0 (h.any_effect_refl (by simp))) h.tail.packE.wk0
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

def Eqv.proj_n {Γ Δ : Ctx α ε} (i : Fin Γ.length) : Eqv φ ((Γ.pack, ⊥)::Δ) ((Γ.get i).1, e)
  := ⟦InS.proj_n i⟧

theorem Eqv.Pure.proj_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : Pure (proj_n (φ := φ) (Δ := Δ) (e := e) i)
  := ⟨Eqv.proj_n i, rfl⟩

@[simp]
theorem Eqv.wk1_proj_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (Eqv.proj_n (φ := φ) (Γ := Γ) (Δ := Δ) (e := e) i).wk1 (inserted := inserted) = proj_n i := by
  simp [proj_n]

@[simp]
theorem Eqv.wk2_proj_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (Eqv.proj_n (φ := φ) (Γ := Γ) (Δ := V::Δ) (e := e) i).wk2 (inserted := inserted)
  = proj_n i := by
  simp only [List.get_eq_getElem, wk2, ←Ctx.InS.lift_wk1, proj_n, wk_quot]
  apply congrArg
  ext
  rw [InS.coe_wk, InS.coe_proj_n, InS.coe_proj_n]
  exact wk_lift_proj_n

@[simp]
theorem Eqv.wk_lift_proj_n {Γ Δ : Ctx α ε} {i : Fin Γ.length} {ρ : Γ.InS Δ}
  : (Eqv.proj_n (φ := φ) (Γ := Γ) (Δ := Δ) (e := e) i).wk (ρ.lift (le_refl _)) = proj_n i := by
  simp [proj_n]

@[simp]
theorem Eqv.subst_lift_proj_n {Γ Δ Δ' : Ctx α ε} {i : Fin Γ.length} {σ : Subst.Eqv φ Δ' Δ}
  : (Eqv.proj_n (φ := φ) (Γ := Γ) (Δ := Δ) (e := e) i).subst (σ.lift (le_refl _)) = proj_n i := by
  induction σ using Quotient.inductionOn
  simp [proj_n]

@[simp]
theorem Eqv.subst0_nil_pr_proj_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (Eqv.proj_n (φ := φ) (Γ := Γ) (e := e) i).subst (nil.pr.subst0)
  = proj_n (φ := φ) (Γ := V::Γ) (Δ := Δ) i.succ := by
  apply eq_of_term_eq
  apply Term.subst0_nil_pr_proj_n

@[simp]
theorem Eqv.subst0_pi_r_proj_n {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (Eqv.proj_n (φ := φ) (Γ := Γ) (e := e) i).subst pi_r.subst0
  = proj_n (φ := φ) (Γ := V::Γ) (Δ := Δ) i.succ := subst0_nil_pr_proj_n

theorem Eqv.pl_pack_drop'  {Γ Δ : Ctx α ε} {i : Fin Γ.length}
  : (Eqv.pack_drop' (φ := φ) (Δ := Δ) (e := e) i).pl = proj_n i := rfl

theorem Eqv.proj_n_def {Γ Δ : Ctx α ε} (i : Fin Γ.length) :
  Eqv.proj_n (φ := φ) (Δ := Δ) (e := e) i = ⟦Term.InS.proj_n i⟧ := rfl

theorem Eqv.proj_n_zero {Γ Δ : Ctx α ε}
  : Eqv.proj_n (φ := φ) (Γ := V::Γ) (Δ := Δ) (e := e) (0 : Fin (Γ.length + 1)) = pi_l := rfl

theorem Eqv.proj_n_succ {Γ Δ : Ctx α ε} (i : Fin Γ.length)
  : proj_n (φ := φ) (Γ := V::Γ) (Δ := Δ) (e := e) i.succ = pi_r ;;' proj_n i := by
  rw [seq, <-wk_eff_pi_r, let1_beta, wk1_proj_n, subst0_pi_r_proj_n]

theorem Eqv.proj_n_one {Γ Δ : Ctx α ε}
  : Eqv.proj_n (φ := φ) (Γ := V::V'::Γ) (Δ := Δ) (e := e) (1 : Fin (Γ.length + 2))
  = pi_r ;;' pi_l := by exact proj_n_succ (Γ := V'::Γ) (0 : Fin (Γ.length + 1))

def Eqv.proj_n' {Γ Δ : Ctx α ε} (i : Fin Γ.length) : Eqv φ ((Γ.pack, ⊥)::Δ) ((Γ.get i).1, e)
  := match Γ with
  | [] => i.elim0
  | V::Γ => let2
    (var (V := (V.1.prod (Ctx.pack Γ), e)) 0 (by simp [Ctx.pack]))
    (i.cases (var 1 (by simp)) (λi => proj_n' i))

theorem Eqv.proj_n_def' {Γ Δ : Ctx α ε} (i : Fin Γ.length) :
  proj_n' (φ := φ) (Δ := Δ) (e := e) i = ⟦Term.InS.proj_n' i⟧ := by
  induction Γ generalizing Δ with
  | nil => exact i.elim0
  | cons _ _ I =>
    simp only [
      List.get_eq_getElem, List.length_cons, proj_n', var, Fin.val_zero,
      List.getElem_cons_zero, I, InS.proj_n'
    ]
    cases i using Fin.cases <;> rfl

def Subst.Eqv.unpack {Γ Δ : Ctx α ε} : Subst.Eqv φ ((Γ.pack, ⊥)::Δ) Γ := ⟦Subst.InS.unpack⟧

@[simp]
theorem Subst.Eqv.get_unpack {Γ Δ : Ctx α ε} {i}
  : (unpack (φ := φ) (Γ := Γ) (Δ := Δ)).get i = Eqv.proj_n i
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

def Eqv.unpacked {Γ : Ctx α ε} (a : Eqv φ [(Γ.pack, ⊥)] (A, e)) (h : Γ.Pure)
  : Eqv φ Γ (A, e) := let1 (pack (by simp [h.effect])) (a.wk_id (by simp [Ctx.Wkn.drop]))

theorem Eqv.unpacked_def' {Γ : Ctx α ε} {a : Eqv φ [(Γ.pack, ⊥)] (A, e)} {h : Γ.Pure}
  : a.unpacked (φ := φ) (Γ := Γ) h = a.subst h.packSE := by
  rw [unpacked, <-wk_eff_packE (h := h), let1_beta, <-wk_eq_wk_id, <-subst_fromWk, subst_subst]
  congr
  ext k; cases k using Fin.elim1
  simp [Subst.Eqv.get_comp]

theorem Eqv.packed_wk0 {Γ : Ctx α ε} {a : Eqv φ Γ (A, e)}
  : (a.wk0 (head := head)).packed (Δ := Δ) = pi_r ;;' a.packed := by
  rw [
    packed, wk0, <-subst_fromWk, subst_subst, seq, <-wk_eff_pi_r, let1_beta, wk1, <-subst_fromWk,
    subst_subst, packed, subst_subst
  ]
  congr 1; ext k
  simp only [List.get_eq_getElem, Subst.Eqv.get_comp, Subst.Eqv.get_fromWk, Fin.eta,
    Set.mem_setOf_eq, Ctx.InS.coe_wk0, Nat.succ_eq_add_one, subst_var, id_eq,
    List.getElem_cons_succ, List.length_cons, Subst.Eqv.get_unpack, wk_res_self, ← subst_subst,
    subst_fromWk]
  rw [<-wk1, wk1_proj_n, subst0_pi_r_proj_n]
  rfl

theorem Eqv.packed_packE {Γ : Ctx α ε} {h : Γ.Pure} : h.packE.packed (Δ := Δ) = nil (φ := φ) := by
  induction Γ generalizing Δ with
  | nil => exact Eqv.terminal
  | cons V Γ I =>
    rw [packE_cons, packed_pair]
    convert Eqv.Pure.pair_eta _
    · rfl
    · simp [packed_wk0, I]; rfl
    · simp

@[simp]
theorem Subst.Eqv.unpack_comp_packSE {Γ : Ctx α ε} (h : Γ.Pure)
  : unpack.comp h.packSE = Subst.Eqv.id (φ := φ) := by
  ext k; cases k using Fin.elim1
  simp only [Fin.isValue, List.get_eq_getElem, List.length_singleton, Fin.val_zero,
    List.getElem_cons_zero, get_comp, get_packSE_zero, get_id, Fin.coe_fin_one]
  exact Eqv.packed_packE

theorem Eqv.proj_n_eq_proj_n' {Γ Δ : Ctx α ε} (i : Fin Γ.length) :
  Eqv.proj_n (φ := φ) (Δ := Δ) (e := e) i = Eqv.proj_n' i := by
  induction Γ generalizing Δ with
  | nil => exact i.elim0
  | cons V Γ I =>
  simp only [List.length_cons] at i
  cases i using Fin.cases with
  | zero => rfl
  | succ =>
    simp only [List.get_eq_getElem, List.length_cons, Fin.val_succ, List.getElem_cons_succ,
      proj_n', Fin.val_zero, List.getElem_cons_zero, Fin.cases_succ, <-I]
    rw [<-wk1_proj_n, <-wk1_proj_n, <-nil, <-pi_r_seq, proj_n_succ]

theorem Eqv.unpacked_proj_n {Γ : Ctx α ε} {h : Γ.Pure} {i}
  : (Eqv.proj_n (φ := φ) (e := e) i).unpacked h = var i (h.any_effect_refl i.prop)
  := by induction Γ with
  | nil => exact i.elim0
  | cons V Γ I => cases i using Fin.cases with
  | zero =>
    simp [proj_n_zero, unpacked_def', pi_l, nil, subst_var, pl, Subst.Eqv.get_liftn₂_one]
    rw [<-pl, pack, Pure.pl_pair]
    exact Pure.wk0 ⟨h.tail.packE, by simp⟩
  | succ i =>
    rw [unpacked_def', proj_n_succ, seq]
    simp only [List.get_eq_getElem, List.length_cons, Fin.val_succ, List.getElem_cons_succ,
      wk1_proj_n, subst_let1, subst_lift_proj_n]
    simp [pi_r, pr, nil, subst_var]
    rw [<-pr, pack, Pure.pr_pair, <-wk1_proj_n, <-wk0_let1, <-wk0_var]
    apply congrArg
    exact I (h := h.tail)
    exact ⟨var 0 (h.any_effect_refl (by simp)), rfl⟩

@[simp]
theorem Subst.Eqv.packSE_comp_unpack {Γ : Ctx α ε} (h : Γ.Pure)
  : h.packSE.comp unpack = Subst.Eqv.id (φ := φ) := by
  ext k; simp only [List.get_eq_getElem, get_comp, get_unpack, get_id]
  rw [<-Eqv.unpacked_proj_n, Eqv.unpacked_def']

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
  = (proj_n (φ := φ) (Γ := Γ) ⟨i, hv.length⟩).wk_res hv.get := by simp [packed, subst_var]

theorem Subst.Eqv.lift_unpack {Γ Δ : Ctx α ε}
  : (unpack (φ := φ) (Γ := Γ) (Δ := Δ)).lift (le_refl (A, ⊥))
  = ((Eqv.var 0 (by simp)).pair (Eqv.var 1 (by simp))).subst0.comp Subst.Eqv.unpack := by
  ext k
  cases k using Fin.cases with
  | zero =>
    simp [
      Subst.Eqv.get_comp, Eqv.proj_n_zero, Eqv.pi_l, Eqv.nil, Eqv.pl, Eqv.let2_pair,
      Eqv.let1_beta_var0, Eqv.let1_beta_var1]
  | succ k =>
    simp only [List.get_eq_getElem, List.length_cons, Fin.val_succ, List.getElem_cons_succ,
      get_lift_succ, get_unpack, get_comp, Eqv.proj_n_succ, Eqv.seq, Eqv.pi_r, Eqv.pr, Eqv.nil,
      Eqv.wk1_proj_n, Eqv.subst_let1, Eqv.subst_let2, Eqv.var0_subst0, Fin.zero_eta, Fin.val_zero,
      List.getElem_cons_zero, Eqv.wk_res_eff, Eqv.wk_eff_pair, Eqv.wk_eff_var, ge_iff_le,
      Prod.mk_le_mk, le_refl, bot_le, and_self, Eqv.subst_liftn₂_var_zero, Eqv.let2_pair,
      Eqv.wk0_var, Nat.reduceAdd, Eqv.let1_beta_var0, Eqv.var_succ_subst0, Eqv.subst_lift_var_zero,
      Eqv.let1_beta_var1, Nat.add_zero, Nat.zero_eq, Eqv.subst_lift_proj_n]
    rw [Eqv.wk0, <-Eqv.subst_fromWk]
    apply Eqv.eq_of_term_eq
    apply subst_eqOn_fvi
    intro i
    simp only [InS.coe_proj_n, fvi_proj_n]
    simp only [Set.mem_Iio, Nat.lt_one_iff, Set.mem_setOf_eq, Ctx.InS.coe_toSubst, Ctx.InS.coe_wk0,
      Subst.fromWk_apply, Nat.succ_eq_add_one, InS.coe_subst0, InS.coe_var]
    intro i; cases i; rfl

theorem Subst.Eqv.liftn₂_unpack {Γ Δ : Ctx α ε}
  : (unpack (φ := φ) (Γ := Γ) (Δ := Δ)).liftn₂ (le_refl (A, ⊥)) (le_refl (B, ⊥))
  = (Eqv.pair (Eqv.var 0 (by simp))
    (Eqv.pair (Eqv.var 1 (by simp)) (Eqv.var 2 (by simp)))).subst0.comp Subst.Eqv.unpack := by
  ext k
  cases k using Fin.cases with
  | zero =>
    simp only [List.get_eq_getElem, List.length_cons, Fin.val_zero, List.getElem_cons_zero,
      get_liftn₂_zero, get_comp, get_unpack, Eqv.proj_n_zero, Eqv.pi_l, Eqv.pl, Eqv.nil,
      Eqv.subst_let2, Eqv.var0_subst0, Fin.zero_eta, Eqv.wk_res_self, Eqv.subst_liftn₂_var_one,
      Eqv.let2_pair, Eqv.wk0_pair, Eqv.wk0_var, Nat.reduceAdd, Eqv.let1_beta_var0, Eqv.subst_let1,
      Eqv.subst_pair, Eqv.var_succ_subst0, Eqv.subst_lift_var_succ, zero_add]
    rw [Eqv.let1_beta'
      (a' := (Eqv.pair (Eqv.var 1 (by simp)) (Eqv.var 2 (by simp)))) (h := by simp)]
    rfl
  | succ k =>
    cases k using Fin.cases with
    | zero =>
      simp [
        Subst.Eqv.get_comp, Eqv.proj_n_zero, Eqv.pi_l, Eqv.nil, Eqv.pl, Eqv.let2_pair,
        Eqv.let1_beta_var0, get_liftn₂_one,
      ]
      rw [Eqv.proj_n_one, Eqv.seq_pi_l]
      simp only [Eqv.pi_r, Eqv.subst_pl, Eqv.subst_pr, Eqv.nil_subst0, Eqv.wk_eff_self]
      rw [Eqv.Pure.pr_pair, Eqv.Pure.pl_pair] <;> simp
    | succ k =>
      simp only [List.length_cons, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ,
        get_liftn₂_succ, get_lift_succ, get_unpack, get_comp]
      rw [Eqv.proj_n_succ (Γ := _::Γ) (i := k.succ)]
      rw [Eqv.proj_n_succ]
      simp only [Eqv.seq, List.get_eq_getElem, List.length_cons, Fin.val_succ,
        List.getElem_cons_succ, Eqv.pi_r, Eqv.nil, Eqv.wk1_proj_n, Eqv.wk1_let1, Eqv.wk1_pr,
        Eqv.wk1_var0, Fin.zero_eta, Fin.val_zero, List.getElem_cons_zero, Eqv.wk2_proj_n,
        Eqv.subst_let1, Eqv.subst_pr, Eqv.var0_subst0, Eqv.wk_res_eff, Eqv.wk_eff_pair,
        Eqv.wk_eff_var, Eqv.subst_lift_var_zero, Eqv.subst_lift_proj_n]
      rw [Eqv.Pure.pr_pair]
      rw [Eqv.let1_beta'
        (a' := (Eqv.pair (Eqv.var 1 (by simp)) (Eqv.var 2 (by simp)))) (h := by simp)]
      simp only [Eqv.subst_let1, Eqv.subst_pr, Eqv.var0_subst0, List.length_cons, Nat.add_zero,
        Nat.zero_eq, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
        Eqv.wk_res_eff, Eqv.wk_eff_pair, Eqv.wk_eff_var, Eqv.subst_lift_proj_n]
      rw [Eqv.Pure.pr_pair, Eqv.let1_beta_var2, Eqv.wk0, Eqv.wk0, Eqv.wk_wk, <-Eqv.subst_fromWk]
      apply Eqv.eq_of_term_eq
      apply subst_eqOn_fvi
      intro i
      rw [InS.coe_proj_n, fvi_proj_n]
      simp only [Set.mem_Iio, Nat.lt_one_iff, Set.mem_setOf_eq, Ctx.InS.coe_toSubst,
        Ctx.InS.coe_comp, Ctx.InS.coe_wk0, fromWk_apply, Function.comp_apply, Nat.succ_eq_add_one,
        InS.coe_subst0, Term.InS.coe_var]
      intro h; cases h; rfl
      exact ⟨Eqv.var 1 (by simp), rfl⟩
      exact ⟨Eqv.var 0 (by simp), rfl⟩

theorem Eqv.packed_let1 {Γ : Ctx α ε} {A B : Ty α}
  {a : Eqv φ Γ (A, e)} {b : Eqv φ ((A, ⊥)::Γ) (B, e)}
  : (let1 a b).packed (Δ := Δ)
  = let1 a.packed (let1 (pair (var 0 (by simp)) (var 1 (by simp))) b.packed) := by
  rw [packed, subst_let1]; apply congrArg
  rw [
    packed, let1_beta' (a' := pair (var 0 (by simp)) (var 1 (by simp))) (h := by simp),
    subst_subst, Subst.Eqv.lift_unpack
  ]

theorem Eqv.packed_let2 {Γ : Ctx α ε} {A B C : Ty α}
  {a : Eqv φ Γ (A.prod B, e)} {b : Eqv φ ((B, ⊥)::(A, ⊥)::Γ) (C, e)}
  : (let2 a b).packed (Δ := Δ)
  = let2 a.packed (
      let1 (pair (var 0 (by simp)) (pair (var 1 (by simp)) (var 2 (by simp)))) b.packed) := by
  rw [packed, subst_let2]; congr
  rw [
    packed,
    let1_beta'
      (a' := (pair (var 0 (by simp)) (pair (var 1 (by simp)) (var 2 (by simp))))) (h := by simp),
    subst_subst, Subst.Eqv.liftn₂_unpack,
  ]

theorem Eqv.packed_case {Γ : Ctx α ε} {A B : Ty α}
  {a : Eqv φ Γ (A.coprod B, e)} {l : Eqv φ ((A, ⊥)::Γ) (C, e)} {r : Eqv φ ((B, ⊥)::Γ) (C, e)}
  : (case a l r).packed (Δ := Δ)
  = case a.packed
    (let1 (pair (var 0 (by simp)) (var 1 (by simp))) l.packed)
    (let1 (pair (var 0 (by simp)) (var 1 (by simp))) r.packed) := by
  rw [packed, subst_case]; congr <;> rw [
    packed, let1_beta' (a' := pair (var 0 (by simp)) (var 1 (by simp))) (h := by simp),
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
