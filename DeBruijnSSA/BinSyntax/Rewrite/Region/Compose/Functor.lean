import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Product
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Sum

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

def Eqv.lret {Γ : Ctx α ε} {A B : Ty α} (a : Term.Eqv φ ((A, ⊥)::Γ) (B, e))
  : Eqv φ ((A, ⊥)::Γ) (B::L) := let1 a nil

theorem Eqv.lret_pure {Γ : Ctx α ε} {A B : Ty α} {a : Term.Eqv φ ((A, ⊥)::Γ) (B, ⊥)}
  : lret (L := L) a = ret a := by simp [lret, ret, let1_beta, <-ret_nil]

@[simp]
theorem Eqv.lret_wk_eff {Γ : Ctx α ε} {A B : Ty α}
  {a : Term.Eqv φ ((A, ⊥)::Γ) (B, lo)} {h : lo ≤ hi} : (lret (L := L) (a.wk_eff h)) = lret a
  := by simp [lret]

@[simp]
theorem Eqv.vwk_slift_lret {Γ Δ : Ctx α ε} {A B : Ty α} {a : Term.Eqv φ ((A, ⊥)::Δ) (B, e)}
  {ρ : Γ.InS Δ} : (lret (L := L) a).vwk ρ.slift = lret (a.wk ρ.slift)
  := by simp [lret]

@[simp]
theorem Eqv.vwk1_lret {Γ : Ctx α ε} {A B : Ty α} {a : Term.Eqv φ ((A, ⊥)::Γ) (B, e)}
  : (lret (L := L) a).vwk1 (inserted := inserted) = lret (a.wk1)
  := by simp only [lret, vwk1_let1]; rfl

@[simp]
theorem Eqv.lret_nil {Γ : Ctx α ε} {A : Ty α}
  : (lret (L := L) <| Term.Eqv.nil (φ := φ) (Γ := Γ) (A := A) (e := e)) = nil := by
  rw [lret, <-Term.Eqv.wk_eff_nil (lo := ⊥) (h := bot_le), let1_wk_eff, Term.Eqv.nil, let1_0_nil]

theorem Eqv.lret_lret {Γ : Ctx α ε}
  {f : Term.Eqv φ ((A, ⊥)::Γ) (B, e)} {g : Term.Eqv φ ((B, ⊥)::Γ) (C, e)}
  : lret f ;; lret g = lret (L := L) (f ;;' g)
  := by simp only [lret, let1_seq, vwk1_let1, nil_seq, Term.Eqv.seq, let1_let1]; rfl

theorem Eqv.lret_of_seq {Γ : Ctx α ε}
  {f : Term.Eqv φ ((A, ⊥)::Γ) (B, e)} {g : Term.Eqv φ ((B, ⊥)::Γ) (C, e)}
  : lret (L := L) (f ;;' g) = lret f ;; lret g := lret_lret.symm

theorem Eqv.lret_rtimes {Γ : Ctx α ε}
  {f : Term.Eqv φ ((A, ⊥)::Γ) (B, e)}
  : lret (L := L) (C ⋊' f) = C ⋊ lret f := by
  rw [lret, Term.Eqv.rtimes, Term.Eqv.tensor, let1_let2, rtimes]
  apply congrArg
  simp only [Term.Eqv.wk1_nil, InS.nil_vwk1, vwk1_lret, Term.Eqv.wk0_nil]
  rw [lret, let1_seq, nil_seq, vwk1_ret]
  simp only [InS.nil_vwk1, Term.Eqv.wk1_pair, Term.Eqv.wk1_var_succ, zero_add,
    Term.Eqv.wk1_var0, List.length_cons, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero,
    List.getElem_cons_zero]
  rw [
    let1_pair, let1_beta,
    <-Term.Eqv.wk_eff_var (lo := ⊥) (hn := by simp) (he := bot_le), let1_wk_eff, let1_beta
  ]
  simp only [vsubst_let1]
  congr
  induction f using Quotient.inductionOn
  apply Term.Eqv.eq_of_term_eq
  simp

theorem Eqv.lret_braid {Γ : Ctx α ε}
  : lret (Γ := Γ) (L := L) (e := e) (Term.Eqv.braid) = braid (φ := φ) (left := A) (right := B) := by
  rw [<-Term.Eqv.wk_eff_braid (lo := ⊥) (h := bot_le), lret_wk_eff, lret_pure, braid_eq_ret]

theorem Eqv.lret_ltimes {Γ : Ctx α ε}
  {f : Term.Eqv φ ((A, ⊥)::Γ) (B, e)}
  : lret (L := L) (f ⋉' C) = lret f ⋉ C := by
  rw [<-Term.Eqv.braid_rtimes_braid]
  simp [lret_of_seq, lret_braid, lret_rtimes, braid_rtimes_braid]

theorem Eqv.lret_assoc {Γ : Ctx α ε}
  : lret (Γ := Γ) (L := L) (e := e) (Term.Eqv.assoc)
  = assoc (φ := φ) (A := A) (B := B) (C := C) := by
  rw [<-Term.Eqv.wk_eff_assoc (lo := ⊥) (h := bot_le), lret_wk_eff, lret_pure, assoc_eq_ret]

theorem Eqv.lret_inj_l {Γ : Ctx α ε}
  : lret (L := L) (Term.Eqv.inj_l (e := e)) = inj_l (φ := φ) (Γ := Γ) (A := A) (B := B) := by
  rw [<-Term.Eqv.wk_eff_inj_l (lo := ⊥) (h := bot_le), lret_wk_eff, lret_pure]; rfl

theorem Eqv.lret_inj_r {Γ : Ctx α ε}
  : lret (L := L) (Term.Eqv.inj_r (e := e)) = inj_r (φ := φ) (Γ := Γ) (A := A) (B := B) := by
  rw [<-Term.Eqv.wk_eff_inj_r (lo := ⊥) (h := bot_le), lret_wk_eff, lret_pure]; rfl

theorem Eqv.lret_coprod {Γ : Ctx α ε}
  {f : Term.Eqv φ ((A, ⊥)::Γ) (C, e)} {g : Term.Eqv φ ((B, ⊥)::Γ) (C, e)}
  : lret (L := L) (f.coprod g) = coprod (lret f) (lret g) := by
  rw [lret, Term.Eqv.coprod, let1_case, coprod]
  simp only [vwk1_lret]; rfl
