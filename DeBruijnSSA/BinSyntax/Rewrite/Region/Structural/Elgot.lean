import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Letc
import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Elgot

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

def Eqv.fixpoint_def' {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L)}
  : fixpoint f = letc A nil (f.vwk1.lwk1 ;; left_exit)
  := rfl


def Eqv.fixpoint_def_vwk1 {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {f : Eqv φ (⟨A, ⊥⟩::Γ) ((B.coprod A)::L)}
  : fixpoint f = letc A nil (f.lwk1 ;; left_exit).vwk1
  := by rw [vwk1_seq, vwk1_lwk1]; rfl

-- theorem Eqv.letc_to_vwk1 {Γ : Ctx α ε} {L : LCtx α} {A : Ty α} {β : Eqv φ ((B, ⊥)::Γ) (A::L)} {G}
--   : letc A β G = letc (B.prod A)
--     (ret Term.Eqv.split ;; _ ⋊ β)
--     ((ret Term.Eqv.split ⋉ _ ;; assoc ;; _ ⋊ (let2 (Term.Eqv.var 0 Ctx.Var.shead) G.vwk2)).vwk1)
--   := by
--   sorry

theorem Eqv.coprod_left_letc_binary {Γ : Ctx α ε}
  {A B : Ty α} {l : Eqv φ ((X, ⊥)::Γ) [B]}
  {β : Eqv φ ((Y, ⊥)::Γ) [A, B]} {G : Eqv φ ((A, ⊥)::Γ) [A, B]}
  : coprod l (letc A β G.vwk1)
  = letc A (coprod (l.lwk1 ;; br 1 (Term.Eqv.var 0 Ctx.Var.shead) (by simp)) β) G.vwk1 := by
  sorry

theorem Eqv.packed_out_sum_coprod {β : Eqv φ ((X, ⊥)::Γ) [A, B]}
  :  (β.packed_out ;; (zero.coprod nil).sum nil).lwk1
      ;; (br 1 (Term.Eqv.var 0 Ctx.Var.shead) (by simp)).coprod nil = β
  := by
    rw [
      lwk1_seq, lwk1_packed_out, lwk1_sum, lwk1_coprod, nil_lwk1, nil_lwk1, seq, seq, packed_out,
      lsubst_lsubst, lsubst_lsubst, lsubst_id'
    ]
    ext k; cases k using Fin.cases with
    | zero =>
      simp only [List.get_eq_getElem, List.length_cons, List.length_singleton, Nat.reduceAdd,
        Fin.val_zero, List.getElem_cons_zero, LCtx.pack.eq_2, LCtx.pack.eq_1, coprod, vwk1_br,
        Term.Eqv.wk1_var0, Fin.zero_eta, vwk1_quot, InS.nil_vwk1, vwk1_case, vwk2_br,
        Term.Eqv.wk2_var0, vwk2_quot, sum, inj_r, nil_seq, Term.Eqv.wk1_inr, Term.Eqv.wk2_inr,
        Subst.Eqv.get_comp, Subst.Eqv.pack_get, Term.Eqv.inj_n, Term.Eqv.nil, Fin.val_succ,
        List.getElem_cons_succ, List.length_nil, Fin.cases_zero, lsubst_br, Fin.isValue,
        Subst.Eqv.get_vlift, get_alpha0, Fin.coe_fin_one, zero_add, lsubst_case, vwk_id_eq,
        vsubst_case, Term.Eqv.var0_subst0, Term.Eqv.wk_res_self, vsubst_br,
        Term.Eqv.subst_lift_var_zero, case_inr, let1_beta]
      rfl
    | succ k =>
      cases k using Fin.elim1
      simp only [List.length_singleton, Fin.isValue, Fin.succ_zero_eq_one, List.get_eq_getElem,
        List.length_cons, Nat.reduceAdd, Fin.val_one, List.getElem_cons_succ,
        List.getElem_cons_zero, LCtx.pack.eq_2, LCtx.pack.eq_1, coprod, vwk1_br, Term.Eqv.wk1_var0,
        Fin.zero_eta, Fin.val_zero, nil_vwk1, vwk1_case, vwk2_br, Term.Eqv.wk2_var0,
        sum, nil_seq, vwk1_inj_r, vwk2_inj_r, Subst.Eqv.get_comp, Subst.Eqv.pack_get,
        Term.Eqv.inj_n, Fin.cases, Fin.induction, Fin.induction.go, List.length_nil, eq_mpr_eq_cast,
        cast_eq, lsubst_br, Subst.Eqv.get_vlift, get_alpha0, lsubst_case, vwk_id_eq, vsubst_case,
        Term.Eqv.var0_subst0, Term.Eqv.wk_res_self, nil_vwk2, inj_l]
      simp only [case_inl, let1_beta]
      conv =>
        lhs; rhs; rhs; rhs; rhs;
        rw [
          <-inj_l, zero, lwk1_ret, vwk1_ret, <-ret_nil, inj_l_eq_ret, case_ret, <-ret_of_seq,
          vwk1_vwk2, vwk1_ret, vwk1_ret
        ]
      simp only [vwk2, Term.Eqv.wk1_abort, Term.Eqv.wk1_var0, List.length_cons, Fin.zero_eta,
        List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, lsubst_br, List.length_singleton,
        Nat.reduceAdd, Fin.isValue, Subst.Eqv.get_vlift, get_alpha0, Fin.val_succ,
        List.getElem_cons_succ, Fin.coe_fin_one, zero_add, Fin.cases_zero, vwk1_case, vwk_br,
        Term.Eqv.wk_var, Set.mem_setOf_eq, Ctx.InS.coe_wk2, Nat.liftnWk, Nat.ofNat_pos, ↓reduceIte,
        vwk_id_eq, vsubst_case, Term.Eqv.var0_subst0, Term.Eqv.wk_res_self, vsubst_br,
        Term.Eqv.subst_lift_var_zero, vwk_case, Ctx.InS.coe_lift, Nat.liftWk_zero]
      rw [<-vwk2, <-vwk2, nil_vwk2, nil_vwk2, <-ret_var_zero]
      simp [
        Term.Eqv.seq, Term.Eqv.inj_l, Term.Eqv.nil, <-Term.Eqv.inl_let1, case_inl, let1_beta,
        Subst.Eqv.get_id, Term.Eqv.let1_beta_pure, Nat.liftnWk, Term.Eqv.case_inr
      ]


theorem Eqv.packed_out_sum_left_exit {β : Eqv φ ((X, ⊥)::Γ) [A, B]}
  : (β.packed_out ;; (zero.coprod nil).sum nil).lwk1 ;; left_exit = β
  := packed_out_sum_coprod

theorem Eqv.letc_vwk1_den {Γ : Ctx α ε}
  {A B : Ty α} {β : Eqv φ ((X, ⊥)::Γ) [A, B]} {G : Eqv φ ((A, ⊥)::Γ) [A, B]}
  : letc A β G.vwk1 = (β.packed_out ;; sum (coprod zero nil) nil) ;;
                    coprod nil (fixpoint (G.packed_out ;; coprod (coprod zero inj_l) inj_r)) := by
  rw [fixpoint_def_vwk1, coprod_left_letc_binary, nil_lwk1, nil_seq, seq_letc_vwk1]
  congr
  · rw [packed_out_sum_coprod]
  · convert packed_out_sum_left_exit.symm
    simp [sum, coprod_seq, zero_seq]
