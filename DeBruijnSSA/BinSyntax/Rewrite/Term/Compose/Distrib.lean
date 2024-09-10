import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Term.Compose.Product

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Term

def Eqv.distl {A B C : Ty α} {Γ : Ctx α ε}
  : Eqv φ (⟨(A.prod B).coprod (A.prod C), ⊥⟩::Γ) ⟨A.prod (B.coprod C), e⟩
  := coprod (A ⋊' inj_l) (A ⋊' inj_r)

def Eqv.distl_inv {A B C : Ty α} {Γ : Ctx α ε}
  : Eqv φ (⟨A.prod (B.coprod C), ⊥⟩::Γ) ⟨(A.prod B).coprod (A.prod C), e⟩
  := let2 nil (coprod (inl (pair (var 1 (by simp)) nil)) (inr (pair (var 1 (by simp)) nil)))

theorem Eqv.distl_distl_inv_pure {A B C : Ty α} {Γ : Ctx α ε}
  : (distl : Eqv φ (⟨(A.prod B).coprod (A.prod C), ⊥⟩::Γ) ⟨A.prod (B.coprod C), ⊥⟩)
  ;;' distl_inv = nil := by
  simp only [distl, distl_inv, coprod_seq]
  simp [
    seq, let1_beta_pure, coprod, wk1_let2, rtimes, wk1_tensor, let2_tensor, subst_liftn₂_tensor,
    wk2, Nat.liftnWk, nil, inj_l, inj_r, case_inl, case_inr, <-inl_let2, <-inr_let2, let2_eta,
    case_eta
  ]

theorem Eqv.distl_inv_distl_pure {A B C : Ty α} {Γ : Ctx α ε}
  : (distl_inv : Eqv φ (⟨A.prod (B.coprod C), ⊥⟩::Γ) ⟨(A.prod B).coprod (A.prod C), ⊥⟩)
  ;;' distl = nil := by
  simp only [distl_inv, distl, seq_let2, wk1_coprod, wk1_rtimes, wk1_inj_l, wk1_inj_r, coprod_seq,
    inl_coprod, seq_rtimes, inr_coprod]
  convert let2_eta
  simp only [coprod, nil, wk1, inj_l, let2_pair, wk0_var, zero_add, wk_let1, wk_var,
    Set.mem_setOf_eq, Ctx.InS.coe_wk1, Nat.liftWk_succ, Nat.succ_eq_add_one, Nat.reduceAdd,
    Ctx.InS.lift_wk1, Ctx.InS.coe_wk2, Nat.liftnWk, Nat.one_lt_ofNat, ↓reduceIte, wk_pair,
    Ctx.InS.coe_lift, zero_lt_two, wk_inl, Nat.liftWk_zero, inj_r, wk_inr]
  calc
    _ = let1
      (case (var 0 Ctx.Var.shead) (var 0 Ctx.Var.shead).inl (var 0 Ctx.Var.shead).inr)
      (pair (var 2 (by simp)) (var 0 Ctx.Var.shead)) := by
      simp only [let1_case, wk1_pair, wk1_var_succ, Nat.reduceAdd, wk1_var0, List.length_cons,
        Fin.zero_eta, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero]
      congr 1 <;> simp [let1_beta_pure]
    _ = _ := by simp [case_eta, let1_beta_var0]

theorem Eqv.wk_eff_distl {A B C : Ty α} {Γ : Ctx α ε} {h : lo ≤ hi}
  : (distl : Eqv φ (⟨(A.prod B).coprod (A.prod C), ⊥⟩::Γ) ⟨A.prod (B.coprod C), _⟩).wk_eff h
  = distl
  := rfl

theorem Eqv.wk_eff_distl_inv {A B C : Ty α} {Γ : Ctx α ε} {h : lo ≤ hi}
  : (distl_inv : Eqv φ (⟨A.prod (B.coprod C), ⊥⟩::Γ) ⟨(A.prod B).coprod (A.prod C), _⟩).wk_eff h
  = distl_inv
  := rfl

theorem Eqv.Pure.distl {A B C : Ty α} {Γ : Ctx α ε}
  : (distl : Eqv φ (⟨(A.prod B).coprod (A.prod C), ⊥⟩::Γ) ⟨A.prod (B.coprod C), ⊥⟩).Pure
  := ⟨Eqv.distl, rfl⟩

theorem Eqv.Pure.distl_inv {A B C : Ty α} {Γ : Ctx α ε}
  : (distl_inv : Eqv φ (⟨A.prod (B.coprod C), ⊥⟩::Γ) ⟨(A.prod B).coprod (A.prod C), ⊥⟩).Pure
  := ⟨Eqv.distl_inv, rfl⟩

theorem Eqv.distl_distl_inv {A B C : Ty α} {Γ : Ctx α ε}
  : (distl : Eqv φ (⟨(A.prod B).coprod (A.prod C), ⊥⟩::Γ) ⟨A.prod (B.coprod C), e⟩)
  ;;' distl_inv = nil := by rw [
    <-wk_eff_distl (h := bot_le), <-wk_eff_distl_inv (h := bot_le), <-wk_eff_seq,
    distl_distl_inv_pure, wk_eff_nil
  ]

theorem Eqv.distl_inv_distl {A B C : Ty α} {Γ : Ctx α ε}
  : (distl_inv : Eqv φ (⟨A.prod (B.coprod C), ⊥⟩::Γ) ⟨(A.prod B).coprod (A.prod C), e⟩)
  ;;' distl = nil := by rw [
    <-wk_eff_distl (h := bot_le), <-wk_eff_distl_inv (h := bot_le), <-wk_eff_seq,
    distl_inv_distl_pure, wk_eff_nil
  ]
