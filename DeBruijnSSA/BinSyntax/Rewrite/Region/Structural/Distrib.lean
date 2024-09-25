import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Region.Structural.Product
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Cast
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Distrib
import DeBruijnSSA.BinSyntax.Rewrite.Term.Structural.Distrib
import DeBruijnSSA.BinSyntax.Rewrite.Region.Case

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

open Term.Eqv

theorem Eqv.packed_in_case_split {Γ : Ctx α ε} {R : LCtx α}
  {a : Term.Eqv φ Γ (A.coprod B, e)} {r : Eqv φ ((A, ⊥)::Γ) R} {s : Eqv φ ((B, ⊥)::Γ) R}
  : (case a r s).packed_in (Δ := Δ)
  = case (Term.Eqv.split ;;' _ ⋊' a.packed ;;' Term.Eqv.distl_inv) r.packed_in s.packed_in := by
  rw [
    packed_in_case, split, Term.Eqv.seq_rtimes, Term.Eqv.seq_let2, case_let2, let2_pair,
    <-wk_eff_nil (h := bot_le), wk0_wk_eff, let1_wk_eff, let1_wk_eff
  ]
  simp [let1_beta, Term.Eqv.nil]
  simp [
    Term.Eqv.distl_inv, Term.Eqv.seq, Term.Eqv.wk1, Term.Eqv.coprod,
    Nat.liftnWk, Term.Eqv.nil, Term.Eqv.case_inl, Term.Eqv.case_inr,
    case_let1, case_let2,
  ]
  conv => rhs; rw [let1_pair, <-wk_eff_var (hn := Ctx.Var.shead) (he := bot_le), let1_wk_eff]
  simp only [Set.mem_setOf_eq, let1_beta, vsubst_let1]
  sorry

theorem Eqv.packed_in_coprod {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) L} {r : Eqv φ (⟨B, ⊥⟩::Γ) L}
  : (l.coprod r).packed_in (Δ := Δ)
  = let2 (var 0 Ctx.Var.shead) (
      coprod
        (let1 (pair (var 1 Ctx.Var.shead.step) (var 0 Ctx.Var.shead)) l.packed_in)
        (let1 (pair (var 1 Ctx.Var.shead.step) (var 0 Ctx.Var.shead)) r.packed_in)
  )
  := by
  simp only [packed_in, coprod, vsubst_case, subst_var, List.getElem_cons_zero, List.length_cons,
    Fin.zero_eta, Term.Subst.Eqv.get_unpack, List.get_eq_getElem, Fin.val_zero, pi_n_zero,
    Term.Eqv.pi_r, pr, wk_res_self, case_let2]
  sorry
  -- congr <;> {
  --   simp [vwk1, <-vsubst_fromWk, vsubst_vsubst]
  --   congr 1; ext k;
  --   cases k using Fin.cases with
  --   | zero =>
  --     simp [Term.Subst.Eqv.get_comp, subst_fromWk, pi_n_zero, Term.Eqv.pi_r, Term.Eqv.Pure.pr_pair]
  --   | succ i =>
  --     simp only [List.get_eq_getElem, List.length_cons, Fin.val_succ, List.getElem_cons_succ,
  --       Term.Subst.Eqv.get_comp, Term.Subst.Eqv.get_fromWk, Set.mem_setOf_eq, Ctx.InS.coe_wk1,
  --       Nat.liftWk_succ, Nat.succ_eq_add_one, subst_lift_var_succ, subst_fromWk,
  --       Term.Subst.Eqv.get_unpack]
  --     simp only [subst_var, Set.mem_setOf_eq, List.length_cons, Fin.val_succ, Ctx.InS.coe_wk1,
  --       Nat.liftWk_succ, Nat.succ_eq_add_one, id_eq, List.getElem_cons_succ,
  --       Term.Subst.Eqv.get_unpack, List.get_eq_getElem, wk_res_self]
  --     conv => rhs; rw [<-Term.Eqv.let1_beta, <-wk1_pi_n, <-Term.Eqv.seq]
  --     rw [
  --       pi_n_succ, Term.Eqv.seq_assoc, Term.Eqv.seq_pi_l, wk_eff_pair,
  --       Term.Eqv.Pure.pl_pair ⟨_, rfl⟩, pi_n_succ', Term.Eqv.seq,
  --       wk1_pi_n, wk0_let1, wk1_pi_n, wk_let1, <-wk1, Ctx.InS.lift_wk1, <-wk2, wk2_pi_n,
  --       Term.Eqv.seq, wk1_pi_n
  --     ]
  --     sorry
  -- }

theorem Eqv.packed_in_coprod_dist {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) L} {r : Eqv φ (⟨B, ⊥⟩::Γ) L}
  : (l.coprod r).packed_in (Δ := Δ) = case (Term.Eqv.distl_inv (e := ⊥)) l.packed_in r.packed_in
  := by
  rw [
    packed_in, coprod, vsubst_case, subst_var, wk_res_self, Term.Subst.Eqv.get_unpack,
    Term.Eqv.pi_n_zero', Term.Eqv.distl_inv, case_let2, Term.Eqv.pi_r, Term.Eqv.pr, case_let2,
  ]
  simp [Term.Eqv.nil, Term.Eqv.coprod, case_case, case_inl, case_inr]
  stop
  simp [packed_in, vwk1, <-vsubst_fromWk, vsubst_vsubst]
  congr 3 <;> {
    ext k; cases k using Fin.cases with
    | zero =>
      simp [Term.Subst.Eqv.get_comp, subst_fromWk, pi_n_zero, Term.Eqv.pi_r, Term.Eqv.Pure.pr_pair]
    | succ k =>
      simp only [List.get_eq_getElem, List.length_cons, Fin.val_succ, List.getElem_cons_succ,
        Term.Subst.Eqv.get_comp, Term.Subst.Eqv.get_fromWk, Set.mem_setOf_eq, Ctx.InS.coe_wk1,
        Nat.liftWk_succ, Nat.succ_eq_add_one, subst_lift_var_succ, subst_fromWk,
        Term.Subst.Eqv.get_unpack]
      simp only [subst_var, Set.mem_setOf_eq, List.length_cons, Fin.val_succ, Ctx.InS.coe_wk1,
        Nat.liftWk_succ, Nat.succ_eq_add_one, id_eq, List.getElem_cons_succ,
        Term.Subst.Eqv.get_unpack, List.get_eq_getElem, wk_res_self]
      conv => rhs; rw [<-Term.Eqv.let1_beta, <-wk1_pi_n, <-Term.Eqv.seq]
      rw [
        pi_n_succ, Term.Eqv.seq_assoc, Term.Eqv.seq_pi_l, wk_eff_pair,
        Term.Eqv.Pure.pl_pair ⟨_, rfl⟩, pi_n_succ', Term.Eqv.seq,
        wk1_pi_n, wk0_let1, wk1_pi_n, wk_let1, <-wk1, Ctx.InS.lift_wk1, <-wk2, wk2_pi_n
      ]
      sorry
  }

theorem Eqv.packed_in_coprod_arr {A B : Ty α} {Γ : Ctx α ε} {L : LCtx α}
  {l : Eqv φ (⟨A, ⊥⟩::Γ) (C::L)} {r : Eqv φ (⟨B, ⊥⟩::Γ) (C::L)}
  : (l.coprod r).packed_in (Δ := Δ)
  = distl_inv ;; coprod l.packed_in r.packed_in
  := sorry

-- theorem Eqv.packed_in_pack_coprod {Γ : Ctx α ε} {R L : LCtx α}
--   {G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) L}
--   : (pack_coprod G).packed_in (Δ := Δ)
--   = vsubst (distl_pack (e := ⊥) (R := R) (X := Γ.pack)).subst0 (
--     pack_coprod (λi => ((G (i.cast R.length_dist)).packed_in).cast (by rw [LCtx.get_dist]; rfl) rfl)
--   )
--   := by induction R generalizing Γ Δ with
--   | nil => simp [pack_coprod_empty, packed_in]
--   | cons A R I =>
--     conv => lhs; rw [pack_coprod_cons, coprod, packed_in_case, vwk1_pack_coprod, I]
--     conv =>
--       rhs
--       simp only [
--         packed_var, wk_res_self, pack_coprod_cons, coprod, vwk1_packed_in, vsubst_case, var0_subst0
--       ]
--       arg 1
--       rw [distl_pack, distl_inv, Term.Eqv.seq_let2]
--     sorry

-- theorem Eqv.packed_in_pack_coprod_arr {Γ : Ctx α ε} {R L : LCtx α}
--   {G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (A::L)}
--   : (pack_coprod G).packed_in (Δ := Δ)
--   = ret (distl_pack (X := Γ.pack))
--     ;; pack_coprod (λi => acast R.get_dist ;; (G (i.cast R.length_dist)).packed_in)
--   := by
--     rw [packed_in_pack_coprod, ret_seq]; congr;
--     rw [vwk1_pack_coprod]; congr; funext i
--     rw [vwk1_seq, vwk1_packed_in, vwk1_acast, acast_seq]

theorem Eqv.packed_in_pack_coprod_arr {Γ : Ctx α ε} {R L : LCtx α}
  {G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (A::L)}
  : (pack_coprod G).packed_in (Δ := Δ)
  = ret (distl_pack (X := Γ.pack))
    ;; pack_coprod (λi => acast R.get_dist ;; (G (i.cast R.length_dist)).packed_in)
  := by induction R generalizing Γ Δ with
  | nil => simp [pack_coprod_empty, packed_in, ret_seq, vwk1]
  | cons B R I =>
    rw [
      pack_coprod_cons, packed_in_coprod_arr, I, Term.Eqv.distl_pack, ret_of_seq,
      distl_inv_eq_ret, seq_assoc, ret_of_coprod, coprod_seq, ret_of_seq,
      seq_assoc
    ]
    congr 3
    · rw [<-inj_l_eq_ret, pack_coprod_cons, inj_l_coprod]; rfl
    · rw [<-inj_r_eq_ret, pack_coprod_cons, inj_r_coprod]; simp
