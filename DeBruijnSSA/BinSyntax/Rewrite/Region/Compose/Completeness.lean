import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Structural
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Functor
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Elgot

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

theorem Eqv.packed_br_den {Γ : Ctx α ε} {L : LCtx α}
  {ℓ} {a : Term.Eqv φ Γ (A, ⊥)} {hℓ}
  : (br (L := L) ℓ a hℓ).packed (Δ := Δ)
  = ret ((a.packed.wk_res ⟨hℓ.get, by rfl⟩)) ;; ret (Term.Eqv.inj_n _ ⟨ℓ, hℓ.length⟩) := by
  rw [<-ret_of_seq, Term.Eqv.seq_inj_n, packed_br]

theorem Eqv.packed_let1_den {Γ : Ctx α ε} {R : LCtx α}
  {a : Term.Eqv φ Γ (A, e)} {r : Eqv φ ((A, ⊥)::Γ) R}
  : (let1 a r).packed (Δ := Δ)
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
    simp only [let1_beta, Nat.liftnWk, Nat.ofNat_pos, ↓reduceIte, zero_add,
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
      Term.InS.coe_pair, Term.InS.coe_var, List.length_cons, Term.Subst.liftn, Nat.ofNat_pos,
      ↓reduceIte, Ctx.InS.lift_wk0, Term.Subst.InS.coe_comp, Term.Subst.InS.coe_lift, Ctx.InS.coe_wk1,
      Nat.liftnWk]
    rfl

-- theorem Eqv.packed_let2_den {Γ : Ctx α ε} {R : LCtx α}
--   {a : Term.Eqv φ Γ (A.prod B, e)} {r : Eqv φ ((B, ⊥)::(A, ⊥)::Γ) R}
--   : (let2 a r).packed (Δ := Δ)
--   = ret Term.Eqv.split ;; _ ⋊ lret a.packed ;; assoc_inv ;; r.packed := by sorry

-- theorem Eqv.packed_case_den {Γ : Ctx α ε} {R : LCtx α}
--   {a : Term.Eqv φ Γ (A.coprod B, e)} {r : Eqv φ ((A, ⊥)::Γ) R} {s : Eqv φ ((B, ⊥)::Γ) R}
--   : (case a r s).packed (Δ := Δ)
--   = ret Term.Eqv.split ;; _ ⋊ lret a.packed ;; distl_inv ;; coprod r.packed s.packed := by sorry

-- TODO: cfg: needs Böhm-Jacopini lore
