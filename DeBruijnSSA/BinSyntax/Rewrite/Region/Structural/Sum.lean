import DeBruijnSSA.BinSyntax.Rewrite.Region.LSubst
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Seq
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Gloop
import DeBruijnSSA.BinSyntax.Rewrite.Term.Structural.Sum
import DeBruijnSSA.BinSyntax.Typing.Region.Structural

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

def Eqv.unpack {Γ : Ctx α ε} {R : LCtx α} : Eqv φ ((R.pack, ⊥)::Γ) R :=
  match R with
  | [] => loop
  | _::_ => coprod unpack.lwk0 nil

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

theorem Subst.Eqv.unpack_zero {Γ : Ctx α ε} {R : LCtx α}
  : (Subst.Eqv.unpack (φ := φ) (Γ := Γ) (R := R)).get (0 : Fin 1) = Region.Eqv.unpack
  := by rw [unpack_def, Region.Eqv.unpack_def]; rfl

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
        Term.Eqv.var0_subst0, Term.Eqv.wk_res_self, case_inr, let1_beta]
      rfl
    | succ ℓ =>
      simp only [
        List.get_eq_getElem, List.length_cons, Fin.val_succ, List.getElem_cons_succ, unpack,
        LCtx.pack.eq_2, Term.Eqv.inj_n, Fin.val_zero, List.getElem_cons_zero, Fin.cases_succ,
        coprod, vwk1_quot, InS.nil_vwk1, vwk1_lwk0, vwk1_unpack, vsubst_case, Term.Eqv.var0_subst0,
        Fin.zero_eta, Term.Eqv.wk_res_self, vsubst_lwk0, vsubst_lift_unpack, case_inl, let1_beta, I]
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

theorem Eqv.packed_out_br {Γ : Ctx α ε} {L : LCtx α}
  {ℓ} {a : Term.Eqv φ Γ (A, ⊥)} {hℓ}
  : (br (L := L) ℓ a hℓ).packed_out = br 0 (a.wk_res ⟨hℓ.get, by rfl⟩).inj (by simp) := by
  simp [packed_out]
  induction a using Quotient.inductionOn
  simp only [Term.Eqv.subst0_quot, Term.Eqv.inj_n_def, List.get_eq_getElem, Term.Eqv.wk_id_quot,
    Term.Eqv.subst_quot, br_quot, Term.Eqv.wk_res_quot]
  rw [Term.Eqv.inj_quot]
  simp only [br_quot]
  congr; ext; simp [Term.inj_n]

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
  (r : Eqv φ ((A, ⊥)::Γ) R) : (r.lwk0 (head := head)).packed_out = r.packed_out ;; inj_l := by
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
    simp only [Subst.Eqv.vlift_pack, vwk1_seq, nil_vwk1, vwk1_inj_l]
    rw [<-packed_out, packed_out_lwk0_arrow, I]

theorem Eqv.lsubst_pack_unpack {Γ : Ctx α ε} {R : LCtx α}
  : lsubst Subst.Eqv.pack (unpack (φ := φ) (Γ := Γ) (R := R)) = nil := by
  rw [<-Eqv.packed_out, Eqv.packed_out_unpack]

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

theorem Eqv.cfg_unpack_rec {Γ : Ctx α ε} {R L : LCtx α}
  {β : Eqv φ Γ (R.pack::L)} {G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R.pack::L)}
  : cfg R (β.lsubst Subst.Eqv.unpack.extend) (λi => (G i).lsubst Subst.Eqv.unpack.extend)
  = gloop R.pack β (Eqv.unpack.lsubst (Subst.Eqv.fromFCFG G).vlift) := by
  convert dinaturality_to_gloop_rec
  · rw [Subst.Eqv.vlift_extend, Subst.Eqv.vlift_unpack]
  · rw [Subst.Eqv.unpack_zero]

theorem Eqv.packed_out_cfg_liftn {Γ : Ctx α ε} {R L : LCtx α}
  {β : Eqv φ Γ (R ++ L)} {G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : (cfg R β G).packed_out
  = cfg R (β.lsubst (Subst.Eqv.pack.liftn_append _))
          (λi => (G i).lsubst (Subst.Eqv.pack.liftn_append _))
  := by simp only [packed_out, lsubst_cfg, Subst.Eqv.vlift_liftn_append, Subst.Eqv.vlift_pack]

def Eqv.unpack_right_out {Γ : Ctx α ε} {R L : LCtx α}
  : Eqv φ (((R ++ L).pack, ⊥)::Γ) (R ++ [L.pack]) :=
  case (Term.Eqv.pack_app (e := ⊥))
    (br (List.length R) Term.Eqv.nil (by simp))
    (lwk_id LCtx.Wkn.id_right_append unpack)

theorem Eqv.lsubst_pack_append_vlift_unpack {Γ : Ctx α ε} {L R : LCtx α}
  : lsubst (Subst.Eqv.liftn_append R Subst.Eqv.pack).vlift (unpack (φ := φ) (Γ := Γ) (R := R ++ L))
  = unpack_right_out := by
  rw [unpack_right_out]
  induction R with
  | nil => simp only [List.nil_append, Subst.Eqv.liftn_append_empty, Subst.Eqv.vlift_pack,
    lsubst_pack_unpack, LCtx.pack.eq_1, Term.Eqv.pack_app, Term.Eqv.inj_l, List.length_nil,
    case_inl, let1_beta, vsubst_br, Term.Eqv.nil_subst0, Term.Eqv.wk_eff_self]; rfl
  | cons A L I =>
    simp only [List.cons_append, LCtx.pack.eq_2, unpack, coprod, List.append_eq,
      Eqv.nil_vwk1, lsubst_case, Term.Eqv.pack_app, Term.Eqv.coprod, List.length_cons]
    conv => rhs; rw [case_bind, let1_case]
    apply congrArg₂
    · have I' := congrArg (vwk1 (inserted := ?h)) <| congrArg (lwk0 (head := A)) I
      convert I' using 1
      · simp [vwk1_lwk0, unpack_def, Subst.Eqv.pack]
        congr; ext
        simp [Region.vwk1_lwk0, Region.vwk1_lsubst]
        simp [Region.lwk0, <-Region.lsubst_fromLwk, Region.lsubst_lsubst]
        congr
        funext k
        simp only [Subst.comp, Region.lsubst, Subst.vlift, Nat.succ_eq_add_one, Function.comp_apply,
          Subst.liftn, add_lt_add_iff_right, Region.lwk, zero_add, Nat.reduceSubDiff,
          vsubst0_var0_vwk1, Subst.vwk1_comp_fromLwk, vwk2_vwk1, lsubst_fromLwk]
        split <;> rfl
      · simp [
          lwk0, Term.Eqv.seq, let1_let1, Term.Eqv.sum, Term.Eqv.coprod, Term.Eqv.wk2, Term.Eqv.nil,
          Nat.liftnWk, Term.Eqv.wk_lift_inj_l, <-Ctx.InS.lift_wk1, lwk_id_eq_lwk, let1_case
        ]
        conv => lhs; rhs; simp only [let1_beta]
        simp [
          Term.Eqv.inj_l, Term.Eqv.inj_r, vwk2, Nat.liftnWk, case_inl, case_inr, let1_beta, lwk_lwk,
          vwk1_lwk]
        congr
        simp only [<-Ctx.InS.lift_wk1, vwk_lwk, vwk_lift_unpack, vsubst_lwk, vsubst_lift_unpack]
        congr 1
        conv =>
          lhs; rhs; rw [<-vwk1_unpack, vwk1, <-vsubst_fromWk, vsubst_vsubst, vsubst_id']
          · skip
          · tactic => ext i; apply Term.Eqv.eq_of_term_eq; cases i using Fin.cases <;> rfl
        rw [vsubst_lift_unpack]
    · simp only [Eqv.nil_vwk1, Term.Eqv.seq_inj_r, Term.Eqv.wk1_inr, Term.Eqv.wk1_inj_r,
      vwk1_br, Term.Eqv.wk1_nil, vwk1_case, Term.Eqv.wk1_var0, List.length_cons, Fin.zero_eta,
      List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, vwk2_br, Term.Eqv.wk2_nil]
      rw [<-ret_var_zero]
      simp only [lsubst_br, List.length_cons, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero,
        List.getElem_cons_zero, Subst.Eqv.get_vlift, List.cons_append, lt_add_iff_pos_left,
        add_pos_iff, zero_lt_one, or_true, Subst.Eqv.liftn_append_get_le, vwk1_br,
        Term.Eqv.wk1_var0, vwk_id_eq, vsubst_br, Term.Eqv.var0_subst0, Term.Eqv.wk_res_self,
        Term.Eqv.inj_r, vwk2, lwk_id_eq_lwk, Set.mem_setOf_eq, lwk_case, lwk_quot, vwk1_case,
        LCtx.pack.eq_2, vwk_quot, vwk_case, Term.Eqv.wk_var, Ctx.InS.coe_wk2, Nat.liftnWk,
        Nat.ofNat_pos, ↓reduceIte, let1_beta, vsubst_case, Term.Eqv.subst_lift_nil,
        Term.Eqv.subst_lift_var_zero, case_inr, Nat.add_zero, Nat.zero_eq, ↓dreduceIte,
        Nat.reduceSub, Nat.succ_eq_add_one, Nat.reduceAdd]
      apply eq_of_reg_eq
      simp

theorem Eqv.lsubst_pack_append_unpack {Γ : Ctx α ε} {L R : LCtx α}
  : lsubst (Subst.Eqv.liftn_append R Subst.Eqv.pack) (unpack (φ := φ) (Γ := Γ) (R := R ++ L))
  = unpack_right_out := by
  convert lsubst_pack_append_vlift_unpack
  rw [Subst.Eqv.vlift_liftn_append, Subst.Eqv.vlift_pack]

def Subst.Eqv.unpack_right_out {Γ : Ctx α ε} {R L : LCtx α}
  : Subst.Eqv φ Γ [(R ++ L).pack] (R ++ [L.pack]) := (Eqv.case (Term.Eqv.pack_app (e := ⊥))
    (Eqv.br R.length Term.Eqv.nil (by simp))
    (Region.Eqv.unpack.lwk_id LCtx.Wkn.id_right_append)).csubst

def Eqv.unpacked_right_out {Γ : Ctx α ε} {R L : LCtx α} (β : Eqv φ Γ [(R ++ L).pack])
  : Eqv φ Γ (R ++ [L.pack]) := β.lsubst Subst.Eqv.unpack_right_out

theorem Eqv.unpacked_out_pack_liftn {Γ : Ctx α ε} {R L : LCtx α}
  {β : Eqv φ Γ [(R ++ L).pack]}
  : β.unpacked_out.lsubst (Subst.Eqv.pack.liftn_append R)
  = β.unpacked_right_out := by
  rw [unpacked_out, lsubst_lsubst]; congr; ext k; cases k using Fin.elim1
  simp [
    Subst.Eqv.get_comp, Subst.Eqv.unpack_zero, Subst.Eqv.unpack_right_out,
    lsubst_pack_append_vlift_unpack, unpack_right_out,
  ]

theorem Eqv.packed_out_cfg_unpacked_out {Γ : Ctx α ε} {R L : LCtx α}
  {β : Eqv φ Γ [(R ++ L).pack]} {G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) [(R ++ L).pack]}
  : (cfg R β.unpacked_out (λi => (G i).unpacked_out)).packed_out
  = (cfg R β.unpacked_right_out (λi => (G i).unpacked_right_out))
  := by simp [packed_out, unpacked_out_pack_liftn, Subst.Eqv.vlift_liftn_append]

theorem Eqv.packed_out_cfg {Γ : Ctx α ε} {R L : LCtx α}
  {β : Eqv φ Γ (R ++ L)} {G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : (cfg R β G).packed_out
  = (cfg R β.packed_out.unpacked_right_out (λi => (G i).packed_out.unpacked_right_out)) := calc
  _ = (cfg R β.packed_out.unpacked_out (λi => (G i).packed_out.unpacked_out)).packed_out := by simp
  _ = _ := by rw [packed_out_cfg_unpacked_out]

def Eqv.unpack_app_out {Γ : Ctx α ε} {R L : LCtx α}
  : Eqv φ (((R ++ L).pack, ⊥)::Γ) [R.pack, L.pack] :=
  case (Term.Eqv.pack_app (e := ⊥))
    (br 1 Term.Eqv.nil (by simp))
    (nil)

@[simp]
theorem Eqv.vwk1_unpack_app_out {Γ : Ctx α ε} {R L : LCtx α}
  : (unpack_app_out (φ := φ) (Γ := Γ) (R := R) (L := L)).vwk1 (inserted := inserted)
  = unpack_app_out := by simp only [unpack_app_out, vwk1_case, Term.Eqv.wk1_pack_app]; rfl

def Subst.Eqv.unpack_app_out {Γ : Ctx α ε} {R L : LCtx α}
  : Subst.Eqv φ Γ [(R ++ L).pack] [R.pack, L.pack] := Region.Eqv.unpack_app_out.csubst

@[simp]
theorem Subst.Eqv.vlift_unpack_app_out {Γ : Ctx α ε} {R L : LCtx α}
  : (Subst.Eqv.unpack_app_out (φ := φ) (Γ := Γ) (R := R) (L := L)).vlift (head := head)
  = unpack_app_out := by
  ext k; cases k using Fin.elim1
  simp [unpack_app_out]

theorem Subst.Eqv.extend_unpack_comp_unpack_app_out {Γ : Ctx α ε} {R L : LCtx α}
  : Subst.Eqv.unpack.extend.comp Subst.Eqv.unpack_app_out
  = Subst.Eqv.unpack_right_out (φ := φ) (Γ := Γ) (R := R) (L := L) := by
  ext k; cases k using Fin.elim1
  simp only [Fin.isValue, List.get_eq_getElem, List.length_singleton, Fin.val_zero,
    List.getElem_cons_zero, List.singleton_append, unpack_app_out, Region.Eqv.unpack_app_out,
    get_comp, Eqv.csubst_get, Eqv.cast_rfl, Eqv.lsubst_case, Eqv.lsubst_br, List.length_cons,
    Nat.reduceAdd, Fin.mk_one, Fin.val_one, List.getElem_cons_succ, get_vlift, Eqv.vwk_id_eq,
    unpack_right_out]
  congr
  · simp only [unpack_def, extend_quot, List.singleton_append, get_quot, List.get_eq_getElem,
    List.length_cons, List.length_singleton, Nat.reduceAdd, Fin.val_one, List.getElem_cons_succ,
    List.getElem_cons_zero, Eqv.vwk1_quot]
    apply Region.Eqv.eq_of_reg_eq
    simp
  · simp only [unpack_def, extend_quot, List.singleton_append, vlift_quot, Eqv.lsubst_quot,
    Region.Eqv.unpack_def, Region.InS.unpack, Set.mem_setOf_eq, Eqv.lwk_id_quot]
    apply Region.Eqv.eq_of_reg_eq
    simp only [Set.mem_setOf_eq, InS.coe_lsubst, lsubst, Term.InS.coe_var, InS.coe_vlift,
      Subst.vlift, InS.coe_extend, InS.coe_unpack, List.length_singleton, Function.comp_apply,
      Subst.extend, zero_lt_one, ↓reduceIte, csubst, InS.coe_lwk_id, Region.vsubst0_var0_vwk1]
    rw [Region.vwk1_unpack]

def Eqv.unpacked_app_out {Γ : Ctx α ε} {R L : LCtx α} (r : Eqv φ Γ [(R ++ L).pack])
  : Eqv φ Γ [R.pack, L.pack] := r.lsubst Subst.Eqv.unpack_app_out

theorem Eqv.vwk1_unpacked_app_out {Γ : Ctx α ε} {R L : LCtx α} {r : Eqv φ (V::Γ) [(R ++ L).pack]}
  : r.unpacked_app_out.vwk1 (inserted := inserted) = r.vwk1.unpacked_app_out := by rw [
    unpacked_app_out, <-Subst.Eqv.vlift_unpack_app_out, Subst.Eqv.vwk1_lsubst_vlift,
    Subst.Eqv.vlift_unpack_app_out, Subst.Eqv.vlift_unpack_app_out, <-unpacked_app_out]

theorem Eqv.extend_unpack_unpacked_app_out
  {Γ : Ctx α ε} {R L : LCtx α} {r : Eqv φ Γ [(R ++ L).pack]}
  : r.unpacked_app_out.lsubst Subst.Eqv.unpack.extend = r.unpacked_right_out := by
  rw [unpacked_app_out, lsubst_lsubst, Subst.Eqv.extend_unpack_comp_unpack_app_out]; rfl

theorem Eqv.packed_out_cfg_gloop {Γ : Ctx α ε} {R L : LCtx α}
  {β : Eqv φ Γ (R ++ L)} {G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : (cfg R β G).packed_out
  = gloop R.pack β.packed_out.unpacked_app_out
      (unpack.lsubst (Subst.Eqv.fromFCFG (λi => (G i).vwk1.packed_out.unpacked_app_out))) := calc
  _ = (cfg R (β.packed_out.unpacked_app_out.lsubst Subst.Eqv.unpack.extend)
              (λi => (G i).packed_out.unpacked_app_out.lsubst Subst.Eqv.unpack.extend.vlift))
      := by simp [packed_out_cfg, extend_unpack_unpacked_app_out, Subst.Eqv.vlift_extend]
  _ = _ := by
    rw [dinaturality_to_gloop_rec]
    congr
    · ext k; simp [Subst.Eqv.get_fromFCFG]
      sorry
    · simp [Subst.Eqv.unpack]

end Region

end BinSyntax
