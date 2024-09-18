import DeBruijnSSA.BinSyntax.Rewrite.Region.LSubst
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Seq
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Structural.Sum
import DeBruijnSSA.BinSyntax.Typing.Region.Structural

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

def Eqv.unpack {Γ : Ctx α ε} {R : LCtx α} : Eqv φ ((R.pack, ⊥)::Γ) R :=
  match R with
  | [] => loop
  | _::_ => coprod nil unpack.lwk0

theorem Eqv.unpack_def {Γ : Ctx α ε} {R : LCtx α}
  : Eqv.unpack (φ := φ) (Γ := Γ) (R := R) = ⟦InS.unpack (Γ := Γ) (R := R)⟧ := by induction R with
  | nil => rw [unpack, loop_def]; rfl
  | cons _ _ I =>
    rw [unpack, nil, I, lwk0_quot]
    apply Eqv.eq_of_reg_eq
    simp [
      Region.unpack, Region.nil, Region.ret, Region.lwk0, Region.vwk_lwk, Region.vwk_lift_unpack]

@[simp]
theorem Eqv.vwk_lift_unpack {Γ Δ : Ctx α ε} {R : LCtx α} (ρ : Γ.InS Δ)
  : Eqv.vwk (ρ.lift (le_refl _)) (Eqv.unpack (φ := φ) (R := R)) = unpack := by
  rw [unpack_def, vwk_quot, unpack_def]
  apply Eqv.eq_of_reg_eq
  simp

@[simp]
theorem Eqv.vwk1_unpack {Γ : Ctx α ε} {R : LCtx α}
  : (Eqv.unpack (φ := φ) (Γ := Γ) (R := R)).vwk1 (inserted := inserted) = unpack := by
  rw [vwk1, <-Ctx.InS.lift_wk0, vwk_lift_unpack]

@[simp]
theorem Eqv.vsubst_lift_unpack {Γ Δ : Ctx α ε} {R : LCtx α} (σ : Term.Subst.Eqv φ Γ Δ)
  : Eqv.vsubst (σ.lift (le_refl _)) (Eqv.unpack (φ := φ) (R := R)) = Eqv.unpack := by
  induction σ using Quotient.inductionOn
  rw [unpack_def, Term.Subst.Eqv.lift_quot, vsubst_quot, unpack_def]
  apply Eqv.eq_of_reg_eq
  simp

def Subst.Eqv.unpack {Γ : Ctx α ε} {R : LCtx α} : Subst.Eqv φ Γ [R.pack] R
  := Region.Eqv.unpack.csubst

theorem Subst.Eqv.unpack_def {Γ : Ctx α ε} {R : LCtx α}
  : Subst.Eqv.unpack (φ := φ) (Γ := Γ) (R := R) = ⟦InS.unpack (Γ := Γ) (R := R)⟧
  := by rw [unpack, Region.Eqv.unpack_def]; rfl

@[simp]
theorem Subst.Eqv.vlift_unpack {Γ : Ctx α ε} {R : LCtx α}
  : (Subst.Eqv.unpack (φ := φ) (Γ := Γ) (R := R)).vlift (head := head) = unpack := by
  simp [unpack_def]

@[simp]
theorem Subst.Eqv.vliftn₂_unpack {Γ : Ctx α ε} {R : LCtx α}
  : (Subst.Eqv.unpack (φ := φ) (Γ := Γ) (R := R)).vliftn₂ (left := left) (right := right)
  = unpack := by simp [Subst.Eqv.vliftn₂_eq_vlift_vlift]

def Subst.Eqv.pack {Γ : Ctx α ε} {R : LCtx α} : Subst.Eqv φ Γ R [R.pack] := ⟦Subst.InS.pack⟧

@[simp]
theorem Subst.Eqv.pack_get {Γ : Ctx α ε} {R : LCtx α} {i : Fin R.length}
  : (Subst.Eqv.pack (φ := φ) (Γ := Γ) (R := R)).get i
  = Eqv.br 0 (Term.Eqv.inj_n R i) LCtx.Trg.shead := by rw [pack, Term.Eqv.inj_n_def]; rfl

@[simp]
theorem Subst.Eqv.vlift_pack {Γ : Ctx α ε} {R : LCtx α}
  : (pack (φ := φ) (Γ := Γ) (R := R)).vlift (head := head) = pack
  := by simp only [pack, vlift_quot, Subst.InS.vlift_pack]

@[simp]
theorem Subst.Eqv.vliftn₂_pack {Γ : Ctx α ε} {R : LCtx α}
  : (Subst.Eqv.pack (φ := φ) (Γ := Γ) (R := R)).vliftn₂ (left := left) (right := right)
  = pack := by simp [Subst.Eqv.vliftn₂_eq_vlift_vlift]

theorem Eqv.vsubst0_pack_unpack {Γ : Ctx α ε} {R : LCtx α} {ℓ : Fin R.length}
  : (unpack (φ := φ) (Γ := _::Γ) (R := R)).vsubst (Term.Eqv.inj_n R ℓ).subst0
  = br ℓ (Term.Eqv.var 0 Ctx.Var.shead) (by simp) := by
  induction R with
  | nil => exact ℓ.elim0
  | cons _ _ I =>
    cases ℓ using Fin.cases with
    | zero =>
      simp only [Term.Eqv.inj_n, Fin.val_succ, Fin.cases_zero, unpack, coprod, vsubst_case,
        Term.Eqv.var0_subst0, Term.Eqv.wk_res_self, case_inl, let1_beta]
      rfl
    | succ ℓ =>
      simp only [
        List.get_eq_getElem, List.length_cons, Fin.val_succ, List.getElem_cons_succ, unpack,
        LCtx.pack.eq_2, Term.Eqv.inj_n, Fin.val_zero, List.getElem_cons_zero, Fin.cases_succ,
        coprod, vwk1_quot, InS.nil_vwk1, vwk1_lwk0, vwk1_unpack, vsubst_case, Term.Eqv.var0_subst0,
        Fin.zero_eta, Term.Eqv.wk_res_self, vsubst_lwk0, vsubst_lift_unpack, case_inr, let1_beta, I]
      rfl

def Eqv.unpacked_out {Γ : Ctx α ε} {R : LCtx α} (r : Eqv φ Γ [R.pack]) : Eqv φ Γ R
  := r.lsubst Subst.Eqv.unpack

-- TODO: br here?

@[simp]
theorem Eqv.unpacked_out_quot {Γ : Ctx α ε} {R : LCtx α} (r : InS φ Γ [R.pack])
  : unpacked_out ⟦r⟧ = ⟦r.unpacked_out⟧ := by simp only [unpacked_out, Subst.Eqv.unpack,
    unpack_def, InS.unpack, Set.mem_setOf_eq, csubst_quot, lsubst_quot]; rfl

theorem Eqv.unpacked_out_let1 {Γ : Ctx α ε} {R : LCtx α}
  (a : Term.Eqv φ Γ (A, e)) (r : Eqv φ ((A, ⊥)::Γ) [R.pack])
  :  (let1 a r).unpacked_out = let1 a r.unpacked_out := by simp [unpacked_out]

theorem Eqv.unpacked_out_let2 {Γ : Ctx α ε} {R : LCtx α}
  (a : Term.Eqv φ Γ (A.prod B, e)) (r : Eqv φ ((B, ⊥)::(A, ⊥)::Γ) [R.pack])
  : (let2 a r).unpacked_out = let2 a r.unpacked_out := by simp [unpacked_out]

theorem Eqv.unpacked_out_case {Γ : Ctx α ε} {R : LCtx α}
  (a : Term.Eqv φ Γ (A.coprod B, e))
  (l : Eqv φ ((A, ⊥)::Γ) [R.pack]) (r : Eqv φ ((B, ⊥)::Γ) [R.pack])
  : (case a l r).unpacked_out = case a l.unpacked_out r.unpacked_out := by simp [unpacked_out]

-- TODO: unpacking a cfg is a quarter of Böhm–Jacopini

def Eqv.packed_out {Γ : Ctx α ε} {R : LCtx α} (h : Eqv φ Γ R) : Eqv φ Γ [R.pack]
  := h.lsubst Subst.Eqv.pack

@[simp]
theorem Eqv.packed_out_quot {Γ : Ctx α ε} {R : LCtx α} (r : InS φ Γ R)
  : packed_out ⟦r⟧ = ⟦r.packed_out⟧ := rfl

-- TODO: br becomes an injection

theorem Eqv.packed_out_let1 {Γ : Ctx α ε} {R : LCtx α}
  (a : Term.Eqv φ Γ (A, e)) (r : Eqv φ ((A, ⊥)::Γ) R)
  : (let1 a r).packed_out = let1 a r.packed_out := by simp [packed_out]

theorem Eqv.packed_out_let2 {Γ : Ctx α ε} {R : LCtx α}
  (a : Term.Eqv φ Γ (A.prod B, e)) (r : Eqv φ ((B, ⊥)::(A, ⊥)::Γ) R)
  : (let2 a r).packed_out = let2 a r.packed_out := by simp [packed_out]

theorem Eqv.packed_out_case {Γ : Ctx α ε} {R : LCtx α}
  (a : Term.Eqv φ Γ (A.coprod B, e))
  (l : Eqv φ ((A, ⊥)::Γ) R) (r : Eqv φ ((B, ⊥)::Γ) R)
  : (case a l r).packed_out = case a l.packed_out r.packed_out := by simp [packed_out]

-- TODO: packing a cfg is half of Böhm–Jacopini, and I believe the best we can do sans dinaturality

theorem Eqv.packed_out_lwk0_arrow {Γ : Ctx α ε} {R : LCtx α}
  (r : Eqv φ ((A, ⊥)::Γ) R) : (r.lwk0 (head := head)).packed_out = r.packed_out ;; inj_r := by
  induction r using Quotient.inductionOn
  apply Eqv.eq_of_reg_eq
  simp only [LCtx.pack.eq_2, Set.mem_setOf_eq, Subst.InS.pack, InS.coe_lsubst, InS.coe_lwk,
    LCtx.InS.coe_wk0, ← lsubst_fromLwk, Region.lsubst_lsubst, InS.vwk_br, Term.InS.wk_inr,
    Term.InS.wk_var, Ctx.InS.coe_wk1, Nat.liftWk_zero, InS.coe_alpha0, InS.coe_br, Term.InS.coe_inr,
    Term.InS.coe_var]
  congr
  funext k
  simp [Subst.comp, Term.inj_n, Term.inj, Function.iterate_succ_apply']

theorem Subst.Eqv.unpack_comp_pack {Γ : Ctx α ε} {R : LCtx α}
  : Subst.Eqv.unpack.comp Subst.Eqv.pack = Subst.Eqv.id (φ := φ) (Γ := Γ) (L := R)
  := by ext ℓ; simp [get_comp, pack_get, get_id, unpack, Eqv.csubst_get, Eqv.vsubst0_pack_unpack]

@[simp]
theorem Eqv.unpacked_out_packed_out {Γ : Ctx α ε} {R : LCtx α} (h : Eqv φ Γ R)
  : h.packed_out.unpacked_out = h := by
  rw [Eqv.unpacked_out, packed_out, lsubst_lsubst, Subst.Eqv.unpack_comp_pack, lsubst_id]

@[simp]
theorem Eqv.packed_out_unpack {Γ : Ctx α ε} {R : LCtx α}
  : (unpack (φ := φ) (Γ := Γ) (R := R)).packed_out
  = nil := by
  induction R generalizing Γ with
  | nil =>
    apply Eqv.initial
    simp
  | cons A R I =>
    simp only [LCtx.pack.eq_2, unpack, coprod, vwk1_quot, InS.nil_vwk1, vwk1_lwk0, vwk1_unpack,
      lsubst_case, Subst.Eqv.vlift_pack]
    apply Eq.trans _ Eqv.sum_nil
    simp only [sum, coprod, packed_out, lsubst_case]
    congr
    simp only [Subst.Eqv.vlift_pack, vwk1_seq, nil_vwk1, vwk1_inj_r]
    rw [<-packed_out, packed_out_lwk0_arrow, I]

  theorem Subst.Eqv.pack_comp_unpack {Γ : Ctx α ε} {R : LCtx α}
    : Subst.Eqv.pack.comp Subst.Eqv.unpack = Subst.Eqv.id (φ := φ) (Γ := Γ) (L := [R.pack]) := by
  ext ℓ
  induction ℓ using Fin.elim1
  simp only [unpack, get_comp, vlift_pack, Eqv.csubst_get, Eqv.cast_rfl, get_id, Fin.coe_fin_one]
  rw [<-Eqv.packed_out, Eqv.packed_out_unpack]
  rfl

@[simp]
theorem Eqv.packed_out_unpacked_out {Γ : Ctx α ε} {R : LCtx α} (h : Eqv φ Γ [R.pack])
  : h.unpacked_out.packed_out = h := by
  rw [Eqv.unpacked_out, packed_out, lsubst_lsubst, Subst.Eqv.pack_comp_unpack, lsubst_id]

theorem Eqv.unpacked_out_injective {Γ : Ctx α ε} {R : LCtx α}
  : Function.Injective (Eqv.unpacked_out (φ := φ) (Γ := Γ) (R := R)) := by
  intros x y h; convert congrArg Eqv.packed_out h <;> simp

theorem Eqv.packed_out_injective {Γ : Ctx α ε} {R : LCtx α}
  : Function.Injective (Eqv.packed_out (φ := φ) (Γ := Γ) (R := R)) := by
  intros x y h; convert congrArg Eqv.unpacked_out h <;> simp

theorem Eqv.unpacked_out_inj {Γ : Ctx α ε} {R : LCtx α} {r s : Eqv φ Γ [R.pack]}
  : r.unpacked_out = s.unpacked_out ↔ r = s := ⟨λh => unpacked_out_injective h, λh => by simp [h]⟩

theorem Eqv.packed_out_inj {Γ : Ctx α ε} {R : LCtx α} {r s : Eqv φ Γ R}
  : r.packed_out = s.packed_out ↔ r = s := ⟨λh => packed_out_injective h, λh => by simp [h]⟩
