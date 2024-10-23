import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural
import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Elgot
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Functor
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Elgot
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Cast
import DeBruijnSSA.BinSyntax.Rewrite.Term.Structural.Distrib

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

theorem Eqv.packed_br_den {Γ : Ctx α ε} {L : LCtx α}
  {ℓ} {a : Term.Eqv φ Γ (A, ⊥)} {hℓ}
  : (br (L := L) ℓ a hℓ).packed (L := L) (Δ := Δ)
  = ret ((a.packed.wk_res ⟨hℓ.get, by rfl⟩)) ;; ret (Term.Eqv.inj_n _ ⟨ℓ, hℓ.length⟩) := by
  rw [<-ret_of_seq, Term.Eqv.seq_inj_n, packed_br]

theorem Eqv.packed_let1_den {Γ : Ctx α ε} {R : LCtx α}
  {a : Term.Eqv φ Γ (A, e)} {r : Eqv φ ((A, ⊥)::Γ) R}
  : (let1 a r).packed (L := L) (Δ := Δ)
  = ret Term.Eqv.split ;; _ ⋊ lret a.packed ;; r.packed := by
  rw [<-lret_rtimes, ret_seq, lret]
  simp only [Term.Eqv.rtimes, Term.Eqv.tensor, Term.Eqv.wk1_nil, Term.Eqv.wk1_packed, let1_let2,
    InS.nil_vwk1, vwk1_let2, vwk3, vwk_let1, Term.Eqv.wk_pair, vwk_quot,
    InS.nil_vwk_lift, vsubst_let2, Term.Eqv.nil_subst0, Term.Eqv.wk_eff_split, vsubst_let1,
    Term.Eqv.subst_pair]
  rw [<-Term.Eqv.wk_eff_split (lo := ⊥) (h := bot_le), let2_wk_eff, Term.Eqv.split, let2_pair]
  simp only [vwk1_quot, InS.nil_vwk1, vwk_quot, InS.nil_vwk_lift, let1_beta, vsubst_let1,
    Term.Eqv.subst_pair, let1_seq]
  rw [packed_let1, <-nil, <-ret_nil, vsubst_ret]
  simp only [Term.Eqv.nil, Term.Eqv.wk0_var, zero_add, ← Ctx.InS.lift_wk2, Term.Eqv.wk_var,
    Set.mem_setOf_eq, Ctx.InS.coe_lift, Ctx.InS.coe_wk2, Nat.liftWk_succ, Term.Eqv.wk_lift_packed,
    Term.Eqv.subst_liftn₂_packed, Term.Eqv.subst_lift_var_zero, vsubst_br]
  conv =>
    rhs
    rw [let1_pair, let1_pair]
    simp [let1_beta, Nat.liftnWk, ↓reduceIte, zero_add,
    Term.Eqv.subst_liftn₂_var_one, Term.Eqv.var_succ_subst0, Term.Eqv.var0_subst0, List.length_cons,
    ↓dreduceIte, Nat.reduceAdd, Set.mem_setOf_eq, Ctx.InS.coe_lift, Ctx.InS.coe_wk2,
    Nat.liftWk_succ, id_eq, Nat.reduceSub, Nat.succ_eq_add_one, Fin.zero_eta, List.get_eq_getElem,
    Fin.val_zero, List.getElem_cons_zero, Term.Eqv.wk_res_eff, Term.Eqv.wk_eff_var
    ]
    rw [<-Term.Eqv.wk_eff_var (lo := ⊥) (hn := by simp) (he := bot_le), let1_wk_eff, let1_beta]
  simp only [Term.Eqv.wk_var, Nat.succ_eq_add_one, zero_add, vsubst_let1]
  congr
  · induction a using Quotient.inductionOn
    apply Term.Eqv.eq_of_term_eq
    simp [Term.subst_subst]
    congr
    funext n
    simp only [Term.Subst.pi_n, Term.pi_n, Term.Subst.comp, Term.subst_pn]
    rfl
  · conv => rhs; rhs; rhs; rhs; rhs; rw [<-ret, <-Term.Eqv.nil, ret_nil, nil_seq]
    simp only [let1_beta, vwk1, vsubst_vsubst]
    simp only [<-vsubst_fromWk, vsubst_vsubst, packed, packed_out, packed_in]
    congr 1
    ext k
    simp [Term.Subst.Eqv.get_comp, Term.Eqv.subst_fromWk, <-Ctx.InS.lift_wk0]
    apply Term.Eqv.eq_of_term_eq
    simp only [Term.InS.coe_subst, Term.InS.coe_subst0, Term.InS.coe_pi_n, Term.pi_n, Term.subst_pn,
      Term.wk_pn, Term.InS.coe_wk,
      Term.InS.coe_pair, Term.InS.coe_var, List.length_cons, Term.Subst.liftn,
      ↓reduceIte, Ctx.InS.lift_wk0, Term.Subst.InS.coe_comp, Term.Subst.InS.coe_lift,
      Ctx.InS.coe_wk1, Nat.liftnWk]
    rfl

theorem Eqv.packed_let2_den {Γ : Ctx α ε} {R : LCtx α}
  {a : Term.Eqv φ Γ (A.prod B, e)} {r : Eqv φ ((B, ⊥)::(A, ⊥)::Γ) R}
  : (let2 a r).packed (L := L) (Δ := Δ)
  = ret Term.Eqv.split ;; _ ⋊ lret a.packed ;; assoc_inv ;; r.packed := by
  rw [ret_seq_rtimes]
  simp only [
    Term.Eqv.split, Term.Eqv.nil, lret, vwk1_let1, Term.Eqv.wk1_packed,
    let2_pair, Term.Eqv.wk0_var, zero_add, let1_beta, nil_vwk2, let1_seq, vwk1_ret,
    Term.Eqv.wk1_pair, nil_seq, Term.Eqv.wk1_var_succ, Term.Eqv.wk1_var0, vsubst_let1,
    vwk1_assoc_inv, vwk1_packed, packed_let2
  ]
  rw [let2_bind]
  congr
  · induction a using Quotient.inductionOn
    apply Term.Eqv.eq_of_term_eq
    simp [Term.subst_subst]
    congr
    funext n
    simp only [Term.Subst.pi_n, Term.pi_n, Term.Subst.comp, Term.subst_pn]
    rfl
  · simp only [vwk2, List.length_cons, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero,
    List.getElem_cons_zero, vsubst_br, Term.Eqv.subst_pair, Term.Eqv.subst_lift_var_succ,
    Term.Eqv.var_succ_subst0, Term.Eqv.wk0_var, zero_add, Term.Eqv.subst_lift_var_zero,
    Term.Eqv.var0_subst0, Nat.reduceAdd, Nat.liftWk_succ, Nat.succ_eq_add_one, Term.Eqv.wk_res_self,
    assoc_inv, ret_seq, vwk1_let2, Term.Eqv.wk1_var0, vwk3, vwk_let2, Term.Eqv.wk_var,
    Set.mem_setOf_eq, Ctx.InS.coe_wk3, Nat.liftnWk, ↓reduceIte, vwk_br,
    Term.Eqv.wk_pair, Ctx.InS.coe_liftn₂, Nat.reduceLT, Nat.reduceSub, Nat.one_lt_ofNat,
    vsubst_let2, ge_iff_le, le_refl, Term.Eqv.subst_liftn₂_var_zero,
    Term.Eqv.subst_liftn₂_var_add_2, Term.Eqv.subst_liftn₂_var_one, let2_pair, let1_beta,
    ↓dreduceIte, let2_seq, vwk1_packed]
    congr
    simp only [packed, packed_in, vsubst_vsubst, ← vsubst_fromWk]
    congr 1
    ext k
    apply Term.Eqv.eq_of_term_eq
    simp only [List.get_eq_getElem, List.length_cons, Set.mem_setOf_eq, Term.Subst.InS.get_comp,
      Term.InS.coe_subst, Ctx.InS.coe_toSubst, Ctx.InS.coe_wk2, Term.InS.coe_subst0,
      Term.InS.coe_pair, Term.InS.coe_var, Term.Subst.liftn, ↓reduceIte,
      Term.subst_fromWk, Term.Subst.InS.unpack, Term.Subst.InS.get, Term.Subst.InS.coe_comp,
      Term.Subst.pi_n, Term.Subst.comp, Term.pi_n, Term.subst_pn, Term.wk_pn]
    rfl

theorem Eqv.packed_case_den {Γ : Ctx α ε} {R : LCtx α}
  {a : Term.Eqv φ Γ (A.coprod B, e)} {r : Eqv φ ((A, ⊥)::Γ) R} {s : Eqv φ ((B, ⊥)::Γ) R}
  : (case a r s).packed (L := L) (Δ := Δ)
  = ret Term.Eqv.split ;; _ ⋊ lret a.packed ;; distl_inv ;; coprod r.packed s.packed := by
  rw [ret_seq_rtimes, Term.Eqv.split, let2_pair]
  simp only [Term.Eqv.nil, Term.Eqv.wk0_var, zero_add, lret, vwk1_let1, Term.Eqv.wk1_packed,
    nil_vwk2, nil_seq, let1_seq, vwk1_br, Term.Eqv.wk1_pair, Term.Eqv.wk1_var_succ,
    Term.Eqv.wk1_var0, List.length_cons, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero,
    List.getElem_cons_zero, let1_beta, vsubst_let1, vwk1_distl_inv, vwk1_coprod, vwk1_packed]
  simp only [vsubst_br, Term.Eqv.subst_pair, Term.Eqv.subst_lift_var_succ, Term.Eqv.var_succ_subst0,
    Term.Eqv.wk0_var, zero_add, Term.Eqv.subst_lift_var_zero, Term.Eqv.var0_subst0,
    List.length_cons, Nat.reduceAdd, Nat.liftWk_succ, Nat.succ_eq_add_one, Fin.zero_eta,
    List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Term.Eqv.wk_res_self]
  rw [<-ret, packed_case, case_bind]
  congr
  · induction a using Quotient.inductionOn
    apply Term.Eqv.eq_of_term_eq
    simp [Term.subst_subst]
    congr
    funext n
    simp only [Term.Subst.pi_n, Term.pi_n, Term.Subst.comp, Term.subst_pn]
    rfl
  · rw [distl_inv, ret_seq]
    simp only [let1_beta, vwk1_let2, Term.Eqv.wk1_var0, List.length_cons, Fin.zero_eta,
      List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, vwk3, vwk_case, Term.Eqv.wk_var,
      Set.mem_setOf_eq, Ctx.InS.coe_wk3, Nat.liftnWk, ↓reduceIte, vwk_br,
      Term.Eqv.wk_inl, Term.Eqv.wk_pair, Ctx.InS.coe_lift, Nat.liftWk_succ, Nat.one_lt_ofNat,
      Nat.reduceAdd, Nat.liftWk_zero, Term.Eqv.wk_inr, vsubst_let2, Term.Eqv.var0_subst0,
      Term.Eqv.wk_res_self, vsubst_case, ge_iff_le, le_refl, Term.Eqv.subst_liftn₂_var_zero,
      vsubst_br, Term.Eqv.subst_inl, Term.Eqv.subst_pair, Term.Eqv.subst_lift_var_succ,
      Term.Eqv.subst_liftn₂_var_one, Term.Eqv.wk0_var, Term.Eqv.subst_lift_var_zero,
      Term.Eqv.subst_inr, let2_pair, zero_add, Term.Eqv.var_succ_subst0, ↓dreduceIte, Nat.reduceSub,
      Nat.succ_eq_add_one]
    rw [<-ret, <-ret, case_seq]
    simp only [vwk1_coprod, vwk1_packed, ret_inl_coprod, ret_inr_coprod]
    simp only [ret_seq, vwk1_packed]
    congr 1 <;> {
      simp only [vwk1, packed, packed_in, vsubst_vsubst, ← vsubst_fromWk]
      congr 1
      ext k
      apply Term.Eqv.eq_of_term_eq
      simp only [List.get_eq_getElem, List.length_cons, Set.mem_setOf_eq, Term.Subst.InS.get_comp,
        Term.InS.coe_subst, Ctx.InS.coe_toSubst, Ctx.InS.coe_wk1, Term.InS.coe_subst0,
        Term.InS.coe_pair, Term.InS.coe_var, Term.let2.injEq, Term.Subst.InS.unpack,
        Term.Subst.InS.get, Term.Subst.InS.coe_comp, Term.Subst.pi_n, Term.Subst.comp, Term.pi_n,
        Term.subst_pn, Term.wk_pn]
      rfl
    }

open Term.Eqv

-- theorem Eqv.packed_cfg_den {Γ : Ctx α ε} {L R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G}
--   : (cfg R β G).packed (Δ := Δ)
--   = ret Term.Eqv.split ;; _ ⋊ β.packed ;; fixpoint (
--     _ ⋊ ret Term.Eqv.pack_app ;; distl_inv ;; sum pi_r (
--       ret Term.Eqv.distl_pack ;; pack_coprod
--         (λi => acast (R.get_dist (i := i)) ;; ret Term.Eqv.split ⋉ _ ;; assoc
--             ;; _ ⋊ (G (i.cast R.length_dist)).packed
--         ))) := by
--   -- rw [
--   --   packed_cfg_unpack, letc_to_vwk1, letc_vwk1_den, ret_seq, <-vsubst_packed_out,
--   --   <-vwk1_packed_out, <-ret_seq
--   -- ]
--   -- simp only [seq_assoc]
--   -- congr 1
--   sorry

theorem Eqv.unpacked_app_out_eq_left_exit' {Γ : Ctx α ε} {R L : LCtx α}
  {r : Eqv φ ((A, ⊥)::Γ) [(R ++ L).pack]} : r.unpacked_app_out
  = (r ;; ret Term.Eqv.pack_app).lwk1 ;; left_exit
  := by
  rw [seq, seq, lwk1, <-lsubst_toSubstE, lsubst_lsubst, lsubst_lsubst, unpacked_app_out]
  congr; ext k; cases k using Fin.elim1
  simp only [Fin.isValue, List.get_eq_getElem, List.length_singleton, Fin.val_zero,
    List.getElem_cons_zero, Subst.Eqv.unpack_app_out, unpack_app_out, csubst_get, cast_rfl,
    left_exit, List.getElem_cons_succ, vwk1_case, wk1_var0, List.length_cons, Fin.zero_eta, vwk2_br,
    wk2_var0, vwk1_br, wk1_pack_app, Subst.Eqv.get_comp, get_alpha0, List.length_nil, Fin.val_succ,
    Fin.cases_zero, lsubst_br, Subst.Eqv.get_vlift, Subst.Eqv.get_toSubstE, Set.mem_setOf_eq,
    Fin.val_eq_zero, LCtx.InS.coe_wk1, Nat.liftWk_zero, Nat.reduceAdd, zero_add, vwk_id_eq,
    vsubst_case, var0_subst0, wk_res_self, vsubst_br, subst_lift_var_zero, Nat.add_zero,
    Nat.zero_eq]
  rfl

theorem Eqv.unpacked_app_out_eq_left_exit {Γ : Ctx α ε} {R L : LCtx α}
  {r : Eqv φ ((A, ⊥)::Γ) [(R ++ L).pack]} : r.unpacked_app_out
  = r.lwk1 ;; ret Term.Eqv.pack_app ;; left_exit
  := by rw [unpacked_app_out_eq_left_exit', lwk1_seq, lwk1_ret]

theorem Eqv.packed_cfg_den {Γ : Ctx α ε} {L R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G}
  : (cfg R β G).packed (L := []) (Δ := Δ)
  = (ret Term.Eqv.split ;; _ ⋊ (β.packed ;; ret Term.Eqv.pack_app) ;; distl_inv ;; sum pi_r nil)
    ;; coprod nil (
      fixpoint (
        ret split ⋉ R.pack ;; assoc ;; Γ.pack ⋊ (ret distl_pack
          ;; pack_coprod (λ i =>
            acast R.get_dist ;; (G (Fin.cast R.length_dist i)).packed)
          ;; ret Term.Eqv.pack_app
        ) ;; distl_inv ;; sum pi_r nil
        -- ret Term.Eqv.distl_pack ;; pack_coprod
        --   (λi => acast (R.get_dist (i := i)) ;; ret Term.Eqv.split ⋉ _ ;; assoc
        --       ;; _ ⋊ ((G (i.cast R.length_dist)).packed ;; ret Term.Eqv.pack_app)
        --       ;; distl_inv
        --       ;; sum pi_r nil
        --   )
      )
    )
   := by
  rw [packed_cfg_split_vwk1, fixpoint_def', letc_vwk1_den]
  congr 1
  · rw [ret_seq, <-vsubst_packed_out, <-vwk1_packed_out, <-ret_seq]
    simp only [seq_assoc]
    congr 1
    simp only [LCtx.pack.eq_2, LCtx.pack.eq_1, sum, coprod, Eqv.nil_vwk1, nil_seq,
      vwk1_inj_r, distl_inv_eq_ret, ret_seq, vwk1_case, wk1_var0, List.length_cons, Fin.zero_eta,
      List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, vwk1_vwk2, vwk2_inj_r, vsubst_case,
      var0_subst0, wk_res_self, vsubst_lift_inj_r, vwk1_zero]
    simp only [rtimes, vwk1_unpacked_app_out, vwk1_packed, packed_out_let2, LCtx.pack.eq_2,
      LCtx.pack.eq_1, vwk1_seq, vwk1_case, wk1_var0, List.length_cons, Fin.zero_eta,
      List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, vwk2_zero, nil_vwk2, vwk1_inj_l,
      let2_seq, vwk2_inj_r, vwk1_br, wk1_pack_app, Term.Eqv.distl_inv, vwk1_pi_r, vsubst_lift_seq,
      vsubst_lift_pi_r, vsubst_lift_inj_l, wk1_let2, wk1_nil, ← Ctx.InS.lift_lift, Ctx.InS.lift_wk1,
      wk_lift_coprod, wk_inl, wk_pair, wk_var, Set.mem_setOf_eq, Ctx.InS.coe_lift, Ctx.InS.coe_wk2,
      Nat.liftWk_succ, Nat.liftnWk, ↓reduceIte, zero_add, wk_lift_nil, wk_inr]
    congr 1
    conv => rhs; rw [<-ret, case_let2, seq_assoc]; rhs; rw [ret_seq]
    simp only [vwk2, ← Ctx.InS.lift_wk1, vwk_lift_seq, vwk_case, wk_var, Set.mem_setOf_eq,
      Ctx.InS.coe_lift, Ctx.InS.coe_wk1, Nat.liftWk_zero, vwk_lift_zero, InS.nil_vwk_lift,
      vwk_lift_inj_l, Term.Eqv.coprod, wk1_inl, wk1_pair, wk1_var_succ, zero_add, wk1_nil, wk1_inr,
      vwk_lift_pi_r, vwk1_seq, vwk1_pi_r, vwk1_inj_l, vwk1_inj_r, case_case, vwk1_let2, vwk3, ←
      Ctx.InS.lift_wk2, wk_lift_nil, wk_inl, wk_pair, Nat.liftWk_succ, Nat.reduceAdd,
      vwk_lift_inj_r, wk_inr, vsubst_let2, nil_subst0, wk_eff_self, ← Term.Subst.Eqv.lift_lift,
      vsubst_case, subst_lift_nil, subst_inl, subst_pair, subst_lift_var_succ, subst_lift_var_zero,
      wk0_var, vsubst_lift_seq, vsubst_lift_pi_r, vsubst_lift_inj_l, vsubst_lift_inj_r, subst_inr,
      let2_pair, let1_beta, var_succ_subst0, var0_subst0, List.length_cons, Nat.add_zero,
      Nat.zero_eq, Nat.succ_eq_add_one, Ctx.InS.coe_wk2, Nat.liftnWk, ↓dreduceIte,
      Nat.reduceSub, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
      wk_res_self, nil_vwk_lift]
    simp only [packed_out_unpacked_app_out_ret_seq, LCtx.pack.eq_1, seq_assoc, case_inl, case_inr]
    apply congrArg
    apply congrArg
    simp only [sum, inj_r, inj_l, ret_seq, vwk1_br, wk1_inl, wk1_var0, List.length_cons,
      Fin.zero_eta, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, vsubst_br, subst_inl,
      var0_subst0, wk_res_self, wk1_inr, subst_inr, coprod_seq, vwk1_case, LCtx.pack.eq_2,
      LCtx.pack.eq_1, vwk2, ← Ctx.InS.lift_wk1, vwk_lift_seq, vwk_case, wk_var, Set.mem_setOf_eq,
      Ctx.InS.coe_lift, Ctx.InS.coe_wk1, Nat.liftWk_zero, vwk_lift_zero, nil_vwk_lift,
      vwk_br, wk_inl, wk_inr, vsubst_case, subst_lift_var_zero, case_inl, let1_beta, case_inr,
      Nat.add_zero, Nat.zero_eq, id_eq, pi_r_eq_ret, Term.Eqv.pi_r, subst_pr, nil_subst0,
      wk_eff_self]
    rw [coprod, zero, <-ret_nil, case_ret, ret_seq]
    simp only [vwk1_br, wk1_inl, wk1_var0, List.length_cons, Set.mem_setOf_eq, Ctx.InS.coe_lift,
      Ctx.InS.coe_wk1, Nat.liftWk_zero, id_eq, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero,
      List.getElem_cons_zero, vsubst_br, subst_inl, var0_subst0, wk_res_self, subst_case,
      subst_lift_var_zero, subst_abort, subst_lift_nil, Nat.add_zero, Nat.zero_eq, LCtx.pack.eq_1,
      Term.Eqv.case_inr, let1_beta_pure, nil_subst0, wk_eff_self, wk1_inr, wk1_pair, wk1_var_succ,
      zero_add, pure_is_pure, Pure.pr_pair]
    rfl
  · rw [fixpoint_def']
    congr 5
    simp only [LCtx.pack.eq_2, LCtx.pack.eq_1, ltimes_eq_ret, assoc_eq_ret, List.get_eq_getElem,
      Fin.coe_cast, seq_assoc, packed_out_ret_seq]
    apply congrArg
    apply congrArg
    conv =>
      lhs
      rw [
        packed_out_binary_rtimes, packed_out_unpacked_app_out, <-rtimes_rtimes,
        seq_assoc (right := distl_inv), rtimes_sum_seq_distl_inv,
        seq_assoc (right := sum _ _), seq_assoc (right := coprod _ _)
      ]
    congr 1
    · rw [seq_assoc]
    · rw [seq_assoc, seq_assoc]
      apply congrArg
      rw [
        sum_seq_coprod, sum_seq_coprod, nil_seq, rtimes_nil, nil_seq, <-seq_assoc,
        rtimes_pi_r, seq_assoc, inj_r_coprod
      ]
      rfl
