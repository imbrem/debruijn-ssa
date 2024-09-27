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

@[simp]
theorem Eqv.wk1_distl_inv {A B C : Ty α} {Γ : Ctx α ε}
  : (distl_inv (φ := φ) (A := A) (B := B) (C := C) (Γ := Γ) (e := e)).wk1
    (inserted := inserted)
  = distl_inv := rfl

theorem Eqv.seq_distl_inv_eq_let {X A B C : Ty α} {Γ : Ctx α ε}
  {r : Eqv φ ((X, ⊥)::Γ) ⟨A.prod (B.coprod C), e⟩}
  : r ;;' distl_inv = let1 r distl_inv
  := by rw [seq, wk1_distl_inv]

theorem Eqv.seq_distl_inv {X A B C : Ty α} {Γ : Ctx α ε}
  {r : Eqv φ ((X, ⊥)::Γ) ⟨A.prod (B.coprod C), e⟩}
  : r ;;' distl_inv
  = let2 r (coprod (inl (pair (var 1 (by simp)) nil)) (inr (pair (var 1 (by simp)) nil))) := by
  rw [seq_distl_inv_eq_let, distl_inv]
  convert let2_bind.symm
  simp [wk2, coprod, nil, Nat.liftnWk]

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

theorem Eqv.distl_seq_injective {A B C : Ty α} {Γ : Ctx α ε}
  {r s : Eqv φ (⟨A.prod (B.coprod C), ⊥⟩::Γ) ⟨X, e⟩} (h : distl ;;' r = distl ;;' s)
  : r = s := by
  rw [<-nil_seq r, <-nil_seq s, <-distl_inv_distl, <-seq_assoc, h, seq_assoc]

def Eqv.distr {A B C : Ty α} {Γ : Ctx α ε}
  : Eqv φ (⟨(A.prod C).coprod (B.prod C), ⊥⟩::Γ) ⟨(A.coprod B).prod C, e⟩
  := coprod (inj_l ⋉' C) (inj_r ⋉' C)

theorem Eqv.distl_braid {A B C : Ty α} {Γ : Ctx α ε}
  : distl ;;' braid
  = sum braid braid ;;' distr (φ := φ) (Γ := Γ) (A := A) (B := B) (C := C) (e := e) := by
  rw [distr, sum_coprod, distl, coprod_seq, rtimes_braid, rtimes_braid]

-- theorem Eqv.rtimes_seq_distr {X Y A B C : Ty α} {Γ : Ctx α ε}
--   {a : Eqv φ ((Y, ⊥)::Γ) ⟨A.coprod B, e⟩}
--   : X ⋊' a ;;' distl_inv
--   = pi_r ;;' a ;;' sum sorry sorry := by
--   sorry

theorem Eqv.split_rtimes_pi_r_distl_pure {X A B C : Ty α} {Γ : Ctx α ε}
  : split (φ := φ) (A := X.prod (A.coprod B)) (e := ⊥) (Γ := Δ)
  ;;' _ ⋊' pi_r ;;' distl_inv
  = distl_inv
  ;;' sum
    (_ ⋊' (split ;;' inj_l ⋉' _) ;;' assoc_inv)
    (_ ⋊' (split ;;' inj_r ⋉' _) ;;' assoc_inv) := by
  apply distl_seq_injective
  conv => rhs; rw [seq_assoc, distl_distl_inv, nil_seq]
  rw [distl, coprod_seq, sum]
  congr 1
  · rw [seq_assoc, seq_assoc, dup_pure, split, pair_tensor_pure, pair_rtimes, seq_distl_inv]
    conv =>
      lhs
      simp only [← seq_assoc, rtimes_pi_r, let2_pair, nil_seq]
      simp only [seq, inj_l, wk1_inl, wk1_nil]
    simp [let1_beta_pure, subst0_var0_wk1, wk1_inj_l, coprod, case_inl, seq_inj_l]
    apply congrArg
    simp [
      split, pair_ltimes_pure, nil_seq, rtimes, tensor, wk1_pair, seq_assoc_inv, reassoc_inv_let2,
      reassoc_inv_beta, nil, pi_r, pr
    ]
    rw [<-Pure.let2_dist_pair (ha := by simp)]
    simp [seq, let1_beta_pure, inj_l]
  · sorry

--   rw [seq_distl_inv]
--   simp [
--     seq_rtimes, split, distl_inv, seq_let2, coprod_seq, sum, wk1_seq, wk1_coprod,
--     inl_coprod, inr_coprod, seq_assoc, seq_ltimes, wk1_rtimes, let2_let2, let2_pair,
--     wk1_assoc_inv
--   ]
--   simp [
--     nil, inj_l, inj_r, let1_beta_var0, let1_beta_var1, let2_pair, subst_lift_coprod,
--     pi_r, pr,
--   ]
--   simp [
--     coprod, let1_let2, let1_beta_var0, wk2, Nat.liftnWk, nil, seq_assoc_inv, reassoc_inv_beta,
--     wk1_seq
--   ]
--   simp [seq, let1_beta_pure]
--   rw [<-Eqv.pair_eta_pure (p := var 0 _)]
--   simp [let2_pair, wk0_pl, wk0_pr, let1_beta_pure]
--   conv => lhs; rw [<-case_eta (a := (var 0 _).pr)]
--   simp [case_case]
--   sorry

theorem Eqv.distr_braid {A B C : Ty α} {Γ : Ctx α ε}
  : distr ;;' braid
  = sum braid braid ;;' distl (φ := φ) (Γ := Γ) (A := A) (B := B) (C := C) (e := e)
  := by rw [distl, sum_coprod, distr, coprod_seq, ltimes_braid, ltimes_braid]

def Eqv.distr_inv {A B C : Ty α} {Γ : Ctx α ε}
  : Eqv φ (⟨(A.coprod B).prod C, ⊥⟩::Γ) ⟨(A.prod C).coprod (B.prod C), e⟩
  := let2 nil (case (var 1 (by simp))
    (pair (var 0 Ctx.Var.bhead) (var 1 (by simp))).inl
    (pair (var 0 Ctx.Var.bhead) (var 1 (by simp))).inr)

-- theorem Eqv.distr_distr_inv {A B C : Ty α} {Γ : Ctx α ε}
--   : (distr : Eqv φ (⟨(A.prod C).coprod (B.prod C), ⊥⟩::Γ) ⟨(A.coprod B).prod C, e⟩)
--   ;;' distr_inv = nil := by
--   rw [distr, coprod_seq]
  -- simp only [distr, distr_inv, coprod_seq]
  -- simp [
  --   seq, let1_beta_pure, coprod, wk1_let2, rtimes, wk1_tensor, let2_tensor, subst_liftn₂_tensor,
  --   wk2, Nat.liftnWk, nil, inj_l, inj_r, case_inl, case_inr, <-inl_let2, <-inr_let2, let2_eta,
  --   case_eta
  -- ]
