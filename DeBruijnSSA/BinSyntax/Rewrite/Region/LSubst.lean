import DeBruijnSSA.BinSyntax.Rewrite.Region.Eqv

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

instance Subst.InS.instSetoid {Γ : Ctx α ε} {L K : LCtx α}
  : Setoid (Subst.InS φ Γ L K) where
  r σ τ := ∀i, σ.get i ≈ τ.get i
  iseqv := {
    refl := (λ_ _ => Setoid.refl _)
    symm := (λh i => (h i).symm)
    trans := (λhl hr i => Setoid.trans (hl i) (hr i))
  }

theorem Subst.InS.vlift_congr {Γ : Ctx α ε} {L K : LCtx α}
  {σ τ : Subst.InS φ Γ L K} (h : σ ≈ τ) : σ.vlift (head := head) ≈ τ.vlift
  := λk => by
  simp only [List.get_eq_getElem, get_vlift, InS.vwk1]
  apply InS.vwk_congr_right
  apply h

theorem Subst.InS.vliftn₂_congr {Γ : Ctx α ε} {L K : LCtx α}
  {σ τ : Subst.InS φ Γ L K} (h : σ ≈ τ) : σ.vliftn₂ (left := left) (right := right) ≈ τ.vliftn₂
  := by simp only [vliftn₂_eq_vlift_vlift]; exact vlift_congr <| vlift_congr h

theorem Subst.InS.liftn_append_congr {Γ : Ctx α ε} {L K J : LCtx α}
  {σ τ : Subst.InS φ Γ L K} (h : σ ≈ τ) : σ.liftn_append J ≈ τ.liftn_append J := by
  intro i
  simp only [List.get_eq_getElem, get, liftn_append, liftn]
  split
  · rfl
  case isFalse h' =>
    convert InS.lwk_congr_right (K := J ++ K) ⟨
        λi => i + J.length,
        λi h => ⟨by simp only [List.length_append]; omega, by
          rw [List.getElem_append_right]; simp
          simp only [add_lt_iff_neg_right, not_lt_zero', not_false_eq_true]
          reduce
          simp only [Nat.add_eq, Nat.sub_eq, add_tsub_cancel_right, Nat.succ_eq_add_one, Nat.le_eq]
          omega
        ⟩
      ⟩ (
      h ⟨
        i - J.length,
        by have h'' := i.prop; simp only [List.length_append] at h''; omega
      ⟩) using 1
    congr 3
    rw [List.getElem_append_right _ _ h']
    rfl
    congr 4
    rw [List.getElem_append_right _ _ h']
    rfl
    congr 1
    funext r
    simp only [Set.mem_setOf_eq, List.get_eq_getElem]
    congr 3
    rw [List.getElem_append_right _ _ h']
    apply proof_irrel_heq
    congr 1
    funext r
    simp only [Set.mem_setOf_eq, List.get_eq_getElem]
    congr 3
    rw [List.getElem_append_right _ _ h']
    apply proof_irrel_heq

theorem Subst.InS.slift_congr {Γ : Ctx α ε} {L K : LCtx α}
  {σ τ : Subst.InS φ Γ L K} (h : σ ≈ τ) : σ.slift (head := head) ≈ τ.slift
  := λi => by cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [List.get_eq_getElem, List.length_cons, Fin.val_succ, List.getElem_cons_succ,
      get_slift_succ, InS.lwk0]
    apply InS.lwk_congr_right
    apply h

theorem Subst.InS.extend_congr {Γ : Ctx α ε} {L K R : LCtx α}
  {σ τ : Subst.InS φ Γ L K} (h : σ ≈ τ) : σ.extend (R := R) ≈ τ.extend
  := λi => by
    simp only [List.get_eq_getElem, get, Set.mem_setOf_eq, extend, Subst.extend]
    split
    case isTrue h' =>
      have h := InS.lwk_congr_right (ρ := ⟨_, LCtx.Wkn.id_right_append (added := R)⟩) (h ⟨i, h'⟩)
      convert h using 2
      rw [List.getElem_append_left]
      rfl
      rw [List.getElem_append_left]
      rfl
      exact InS.hext (by rw [List.getElem_append_left]; rfl) rfl (by simp)
      exact InS.hext (by rw [List.getElem_append_left]; rfl) rfl (by simp)
    case _ => rfl

theorem Subst.InS.extend_in_congr {Γ : Ctx α ε} {L K R : LCtx α}
  {σ τ : Subst.InS φ Γ L (K ++ R)} (h : σ ≈ τ) : σ.extend_in ≈ τ.extend_in
  := λi => by
    simp only [List.get_eq_getElem, get, Set.mem_setOf_eq, extend_in, Subst.extend]
    split
    case isTrue h' =>
      convert h ⟨i, h'⟩ using 2
      rw [List.getElem_append_left]
      rfl
      rw [List.getElem_append_left]
      rfl
      exact InS.hext (by rw [List.getElem_append_left]; rfl) rfl (by simp)
      exact InS.hext (by rw [List.getElem_append_left]; rfl) rfl (by simp)
    case _ => rfl

theorem Subst.InS.extend_out_congr {Γ : Ctx α ε} {L K R : LCtx α}
  {σ τ : Subst.InS φ Γ L K} (h : σ ≈ τ) : σ.extend_out (R := R) ≈ τ.extend_out
  := λi => Region.InS.lwk_id_congr (K := K ++ R) LCtx.Wkn.id_right_append (h i)

open Subst.InS

theorem InS.lsubst_congr_subst {Γ : Ctx α ε} {L K : LCtx α} {σ τ : Subst.InS φ Γ L K}
  (h : σ ≈ τ) (r : InS φ Γ L) : r.lsubst σ ≈ r.lsubst τ := by
  induction r using InS.induction generalizing K with
  | br ℓ a hℓ =>
    simp only [lsubst_br, List.get_eq_getElem, vwk_id_eq_vwk]
    apply InS.vsubst_congr_right
    apply InS.vwk_congr_right
    apply h
  | case e r s Ir Is =>
    simp only [lsubst_case]
    exact InS.case_congr (by rfl) (Ir (vlift_congr h)) (Is (vlift_congr h))
  | let1 a r Ir =>
    simp only [lsubst_let1]
    exact InS.let1_congr (by rfl) (Ir (vlift_congr h))
  | let2 a r Ir =>
    simp only [lsubst_let2]
    exact InS.let2_congr (by rfl) (Ir (vliftn₂_congr h))
  | cfg R β G Iβ IG =>
    simp only [lsubst_cfg]
    exact InS.cfg_congr _ (Iβ (liftn_append_congr h))
      (λi => IG i (vlift_congr (liftn_append_congr h)))

theorem InS.lsubst_congr_right {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.InS φ Γ L K)
  {r r' : InS φ Γ L} (h : r ≈ r') : r.lsubst σ ≈ r'.lsubst σ
  := Uniform.lsubst TStep.lsubst σ.prop h

theorem InS.lsubst_congr {Γ : Ctx α ε} {L K : LCtx α} {σ σ' : Subst.InS φ Γ L K}
  {r r' : InS φ Γ L} (hσ : σ ≈ σ') (hr : r ≈ r') : r.lsubst σ ≈ r'.lsubst σ'
  := Setoid.trans (lsubst_congr_subst hσ r) (lsubst_congr_right σ' hr)

theorem Subst.InS.comp_congr {σ σ' : Subst.InS φ Γ K J} {τ τ' : Subst.InS φ Γ L K}
  (hσ : σ ≈ σ') (hτ : τ ≈ τ') : σ.comp τ ≈ σ'.comp τ'
  := λi => InS.lsubst_congr (vlift_congr hσ) (hτ i)

abbrev Subst.Eqv (φ) [EffInstSet φ (Ty α) ε] (Γ : Ctx α ε) (L K : LCtx α)
  := Quotient (α := Subst.InS φ Γ L K) inferInstance

def Subst.Eqv.get (σ : Subst.Eqv φ Γ L K) (i : Fin L.length) : Region.Eqv φ ((L.get i, ⊥)::Γ) K :=
  Quotient.liftOn σ (λσ => ⟦σ.get i⟧) (λ_ _ h => Quotient.sound $ h i)

@[simp]
theorem Subst.Eqv.get_quot {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K} {i : Fin L.length}
  : get ⟦σ⟧ i = ⟦σ.get i⟧ := rfl

theorem Subst.Eqv.ext_quot {σ τ : Subst.InS φ Γ L K}
  (h : ∀i, (⟦σ.get i⟧ : Region.Eqv φ _ _) = ⟦τ.get i⟧) : (⟦σ⟧ : Subst.Eqv φ Γ L K) = ⟦τ⟧
  := Quotient.sound (λi => Quotient.exact $ h i)

@[ext]
theorem Subst.Eqv.ext {σ τ : Subst.Eqv φ Γ L K} (h : ∀i, σ.get i = τ.get i) : σ = τ := by
  induction σ using Quotient.inductionOn
  induction τ using Quotient.inductionOn
  exact Subst.Eqv.ext_quot h

theorem Subst.Eqv.ext_iff' {σ τ : Subst.Eqv φ Γ L K} : σ = τ ↔ ∀i, σ.get i = τ.get i := by
  refine ⟨λh i => h ▸ rfl, Subst.Eqv.ext⟩

theorem Subst.Eqv.get_toSubst {Γ : Ctx α ε} {L K : LCtx α} {σ : L.InS K}
  {i : Fin L.length}
  : get (⟦σ.toSubst⟧ : Eqv φ Γ L K) i
  = Region.Eqv.br (σ.val i) (Term.Eqv.var 0 Ctx.Var.shead) (σ.prop i i.prop) := rfl

def Eqv.lsubst {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.Eqv φ Γ L K) (r : Eqv φ Γ L)
  : Eqv φ Γ K
  := Quotient.liftOn₂ σ r
    (λσ r => (r.lsubst σ).q)
    (λ_ _ _ _ hσ hr => Quotient.sound (InS.lsubst_congr hσ hr))

def Subst.Eqv.vlift {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.Eqv φ Γ L K)
  : Subst.Eqv φ (head::Γ) L K
  := Quotient.liftOn σ
    (λσ => ⟦σ.vlift⟧)
    (λ_ _ h => Quotient.sound (Subst.InS.vlift_congr h))

@[simp]
theorem Subst.Eqv.vlift_quot {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K}
  : vlift (head := head) ⟦σ⟧ = ⟦σ.vlift⟧ := rfl

def Subst.Eqv.vliftn₂ {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.Eqv φ Γ L K)
  : Subst.Eqv φ (left::right::Γ) L K
  := Quotient.liftOn σ
    (λσ => ⟦σ.vliftn₂⟧)
    (λ_ _ h => Quotient.sound (Subst.InS.vliftn₂_congr h))

@[simp]
theorem Subst.Eqv.vliftn₂_quot {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K}
  : vliftn₂ (left := left) (right := right) ⟦σ⟧ = ⟦σ.vliftn₂⟧ := rfl

theorem Subst.Eqv.vliftn₂_eq_vlift_vlift {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.Eqv φ Γ L K)
  : σ.vliftn₂ (left := left) (right := right) = σ.vlift.vlift := by
  induction σ using Quotient.inductionOn;
  simp [Subst.InS.vliftn₂_eq_vlift_vlift]

def Subst.Eqv.extend {Γ : Ctx α ε} {L K R : LCtx α} (σ : Eqv φ Γ L K) : Eqv φ Γ (L ++ R) (K ++ R)
  := Quotient.liftOn σ (λσ => ⟦σ.extend⟧) (λ_ _ h => Quotient.sound <| Subst.InS.extend_congr h)

@[simp]
theorem Subst.Eqv.extend_quot {Γ : Ctx α ε} {L K R : LCtx α} {σ : Subst.InS φ Γ L K}
  : extend (R := R) ⟦σ⟧ = ⟦σ.extend⟧ := rfl

def Subst.Eqv.extend_in {Γ : Ctx α ε} {L K R : LCtx α} (σ : Eqv φ Γ L (K ++ R))
  : Eqv φ Γ (L ++ R) (K ++ R)
  := Quotient.liftOn σ (λσ => ⟦σ.extend_in⟧)
    (λ_ _ h => Quotient.sound <| Subst.InS.extend_in_congr h)

@[simp]
theorem Subst.Eqv.extend_in_quot {Γ : Ctx α ε} {L K R : LCtx α} {σ : Subst.InS φ Γ L (K ++ R)}
  : extend_in ⟦σ⟧ = ⟦σ.extend_in⟧ := rfl

def Subst.Eqv.extend_out {Γ : Ctx α ε} {L K R : LCtx α} (σ : Eqv φ Γ L K)
  : Eqv φ Γ L (K ++ R) := Quotient.liftOn σ (λσ => ⟦σ.extend_out⟧)
    (λ_ _ h => Quotient.sound <| Subst.InS.extend_out_congr h)

@[simp]
theorem Subst.Eqv.extend_out_quot {Γ : Ctx α ε} {L K R : LCtx α} {σ : Subst.InS φ Γ L K}
  : extend_out (R := R) ⟦σ⟧ = ⟦σ.extend_out⟧ := rfl

theorem Subst.Eqv.extend_in_extend_out {Γ : Ctx α ε} {L K R : LCtx α} (σ : Eqv φ Γ L K)
  : σ.extend_out.extend_in = σ.extend (R := R) := by
  induction σ using Quotient.inductionOn
  rw [extend_out_quot, extend_in_quot, Subst.InS.extend_in_extend_out]; rfl

theorem Subst.Eqv.vlift_extend_in {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.Eqv φ Γ L (K ++ R)}
  : σ.extend_in.vlift (head := head) = σ.vlift.extend_in
  := by induction σ using Quotient.inductionOn; simp [Subst.InS.vlift_extend_in]

theorem Subst.Eqv.vlift_extend_out {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.Eqv φ Γ L K}
  : σ.extend_out.vlift (head := head) = σ.vlift.extend_out (R := R)
  := by induction σ using Quotient.inductionOn; rfl

theorem Subst.Eqv.vlift_extend {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.Eqv φ Γ L K}
  : σ.extend.vlift (head := head) = σ.vlift.extend (R := R)
  := by rw [<-extend_in_extend_out, vlift_extend_in, vlift_extend_out, extend_in_extend_out]

theorem Subst.Eqv.get_extend_out {Γ : Ctx α ε} {L K R : LCtx α} {σ : Subst.Eqv φ Γ L K}
  {i : Fin L.length} : (extend_out (R := R) σ).get i = (σ.get i).lwk_id LCtx.Wkn.id_right_append
  := by induction σ using Quotient.inductionOn; rfl

@[simp]
theorem InS.lsubst_q {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K} {r : InS φ Γ L}
   : (r.q).lsubst ⟦σ⟧ = (r.lsubst σ).q := rfl

@[simp]
theorem Eqv.lsubst_quot {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K} {r : InS φ Γ L}
   : lsubst ⟦σ⟧ ⟦r⟧ = ⟦r.lsubst σ⟧ := rfl

theorem Eqv.lsubst_toSubst {Γ : Ctx α ε} {L K : LCtx α} {σ : LCtx.InS L K}
  {r : Eqv φ Γ L} : r.lsubst ⟦σ.toSubst⟧ = r.lwk σ := by
  induction r using Quotient.inductionOn
  simp [InS.lsubst_toSubst]

def Subst.Eqv.comp {Γ : Ctx α ε} {L K J : LCtx α} (σ : Subst.Eqv φ Γ K J) (τ : Subst.Eqv φ Γ L K)
  : Subst.Eqv φ Γ L J := Quotient.liftOn₂ σ τ (λσ τ => ⟦σ.comp τ⟧)
    (λ_ _ _ _ hσ hτ => Quotient.sound (Subst.InS.comp_congr hσ hτ))

@[simp]
theorem Subst.Eqv.comp_quot {Γ : Ctx α ε} {L K : LCtx α} {J : LCtx α}
  {σ : Subst.InS φ Γ K J} {τ : Subst.InS φ Γ L K}
  : comp ⟦σ⟧ ⟦τ⟧ = ⟦σ.comp τ⟧ := rfl

theorem Subst.Eqv.get_comp {Γ : Ctx α ε} {L K J : LCtx α}
  {σ : Subst.Eqv φ Γ K J} {τ : Subst.Eqv φ Γ L K} {i : Fin L.length}
  : (σ.comp τ).get i = (τ.get i).lsubst σ.vlift := by
  induction σ using Quotient.inductionOn
  induction τ using Quotient.inductionOn
  rfl

theorem Eqv.lsubst_lsubst {Γ : Ctx α ε} {L K J : LCtx α}
  {σ : Subst.Eqv φ Γ K J} {τ : Subst.Eqv φ Γ L K} {r : Eqv φ Γ L}
  : (r.lsubst τ).lsubst σ = r.lsubst (σ.comp τ) := by
  induction σ using Quotient.inductionOn
  induction τ using Quotient.inductionOn
  induction r using Quotient.inductionOn
  simp [InS.lsubst_lsubst]

@[simp]
theorem Subst.Eqv.get_vlift {Γ : Ctx α ε} {L K : LCtx α} {i : Fin L.length}
  {σ : Subst.Eqv φ Γ L K} : (σ.vlift (head := head)).get i = (σ.get i).vwk1 := by
  induction σ using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.lsubst_br {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.Eqv φ Γ L K}
  {ℓ : ℕ} {a : Term.Eqv φ Γ ⟨A, ⊥⟩} {hℓ : L.Trg ℓ A}
  : (br ℓ a hℓ).lsubst σ = ((σ.get ⟨ℓ, hℓ.length⟩).vwk_id (by simp [hℓ.getElem])).vsubst a.subst0
  := by induction a using Quotient.inductionOn; induction σ using Quotient.inductionOn; rfl

@[simp]
theorem Eqv.lsubst_let1 {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.Eqv φ Γ L K}
  {a : Term.Eqv φ Γ ⟨A, e⟩} {r : Eqv φ (⟨A, ⊥⟩::Γ) L}
  : (let1 a r).lsubst σ = let1 a (r.lsubst σ.vlift) := by
  induction a using Quotient.inductionOn
  induction r using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.lsubst_let2 {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.Eqv φ Γ L K}
  {a : Term.Eqv φ Γ ⟨A.prod B, e⟩} {r : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L}
  : (let2 a r).lsubst σ = let2 a (r.lsubst σ.vliftn₂) := by
  induction a using Quotient.inductionOn
  induction r using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  rfl

@[simp]
theorem Eqv.lsubst_case {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.Eqv φ Γ L K}
  {a : Term.Eqv φ Γ ⟨A.coprod B, e⟩} {r : Eqv φ (⟨A, ⊥⟩::Γ) L} {s : Eqv φ (⟨B, ⊥⟩::Γ) L}
  : (case a r s).lsubst σ = case a (r.lsubst σ.vlift) (s.lsubst σ.vlift) := by
  induction a using Quotient.inductionOn
  induction r using Quotient.inductionOn
  induction s using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  rfl

def Subst.Eqv.slift {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.Eqv φ Γ L K)
  : Subst.Eqv φ Γ (head::L) (head::K)
  := Quotient.liftOn σ
    (λσ => ⟦σ.slift⟧)
    (λ_ _ h => Quotient.sound (Subst.InS.slift_congr h))

@[simp]
theorem Subst.Eqv.slift_quot {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K}
  : slift (head := head) ⟦σ⟧ = ⟦σ.slift⟧ := rfl

@[simp]
theorem Subst.Eqv.get_slift_zero {σ : Subst.Eqv φ Γ L K} : (σ.slift (head := head)).get ⟨0, by simp⟩
  = Region.Eqv.br 0 (Term.Eqv.var 0 Ctx.Var.shead) (by simp)
  := by induction σ using Quotient.inductionOn; rfl

@[simp]
theorem Subst.Eqv.get_slift_eq_zero {σ : Subst.Eqv φ Γ L K}
  : (σ.slift (head := head)).get (0 : Fin (L.length + 1))
  = Region.Eqv.br 0 (Term.Eqv.var 0 Ctx.Var.shead) (by simp)
  := by induction σ using Quotient.inductionOn; rfl

@[simp]
theorem Subst.Eqv.get_slift_succ {σ : Subst.Eqv φ Γ L K} {i : Fin L.length}
  : (σ.slift (head := head)).get i.succ = (σ.get i).lwk0
  := by induction σ using Quotient.inductionOn; rfl

-- theorem Eqv.lsubst_lift_lwk0 {Γ : Ctx α ε} {L K : LCtx α}
--   {σ : Subst.Eqv φ Γ L K} {h : lo ≤ hi} {r : Region.Eqv φ Γ L}
--   : r.lwk0.lsubst (σ.lift h) = (r.lsubst σ).lwk0 := sorry

theorem Eqv.lsubst_slift_lwk0 {Γ : Ctx α ε} {L K : LCtx α}
  {σ : Subst.Eqv φ Γ L K} {r : Region.Eqv φ Γ L}
  : r.lwk0.lsubst (σ.slift (head := head)) = (r.lsubst σ).lwk0 := by
  induction σ using Quotient.inductionOn
  induction r using Quotient.inductionOn
  simp [Region.InS.lsubst_slift_lwk0]

theorem Subst.Eqv.vlift_slift {Γ : Ctx α ε} {L K : LCtx α}
  {σ : Subst.Eqv φ Γ L K}
  : (σ.slift (head := head')).vlift (head := head) = σ.vlift.slift := by
  induction σ using Quotient.inductionOn
  simp [Subst.InS.vlift_slift]

def Subst.Eqv.liftn_append {Γ : Ctx α ε} {L K : LCtx α} (J) (σ : Subst.Eqv φ Γ L K)
  : Subst.Eqv φ Γ (J ++ L) (J ++ K)
  := Quotient.liftOn σ
    (λσ => ⟦σ.liftn_append J⟧)
    (λ_ _ h => Quotient.sound <| Subst.InS.liftn_append_congr h)

theorem Subst.Eqv.vwk1_lsubst_vlift {Γ : Ctx α ε} {L K : LCtx α}
  {σ : Subst.Eqv φ Γ L K} {r : Region.Eqv φ (head::Γ) L}
  : (r.lsubst σ.vlift).vwk1 (inserted := inserted) = r.vwk1.lsubst σ.vlift.vlift := by
  induction σ using Quotient.inductionOn
  induction r using Quotient.inductionOn
  simp [Region.InS.vwk1_lsubst_vlift]

@[simp]
theorem Subst.Eqv.liftn_append_quot {Γ : Ctx α ε} {L K : LCtx α} {J : LCtx α}
  {σ : Subst.InS φ Γ L K}
  : liftn_append J ⟦σ⟧ = ⟦σ.liftn_append J⟧ := rfl

theorem Subst.Eqv.vlift_liftn_append {Γ : Ctx α ε} {L K : LCtx α} {J : LCtx α}
  {σ : Subst.Eqv φ Γ L K}
  : (σ.liftn_append J).vlift (head := head) = σ.vlift.liftn_append J := by
  induction σ using Quotient.inductionOn
  simp [Subst.InS.vlift_liftn_append]

@[simp]
theorem Subst.Eqv.liftn_append_get_le {Γ : Ctx α ε} {L K : LCtx α} {J : LCtx α}
  {σ : Subst.Eqv φ Γ L K} {i : Fin (J ++ L).length}
  (h : i < J.length)
  : (σ.liftn_append J).get i
  = Eqv.br i (Term.Eqv.var 0 Ctx.Var.shead)
    (LCtx.Trg.of_le_getElem
      (by simp only [List.length_append]; omega)
      (by simp [List.getElem_append_left, h]))
  := by
  induction σ using Quotient.inductionOn
  simp [Term.Eqv.var, h]

@[simp]
theorem Subst.Eqv.liftn_append_singleton {Γ : Ctx α ε} {L K : LCtx α} {V : Ty α}
  {σ : Subst.Eqv φ Γ L K}
  : σ.liftn_append [V] = σ.slift
  := by induction σ using Quotient.inductionOn; simp

@[simp]
theorem Subst.Eqv.liftn_append_empty {Γ : Ctx α ε} {L K : LCtx α}
  {σ : Subst.Eqv φ Γ L K}
  : σ.liftn_append [] = σ
  := by induction σ using Quotient.inductionOn; rw [liftn_append_quot]; congr; ext; simp

@[simp]
theorem Eqv.lsubst_cfg {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  {σ : Subst.Eqv φ Γ L K}
  : (cfg R β G).lsubst σ
  = cfg R (β.lsubst (σ.liftn_append _)) (λi => (G i).lsubst (σ.liftn_append _).vlift) := by
  induction σ using Quotient.inductionOn
  induction β using Quotient.inductionOn
  generalize hG : Quotient.finChoice G = G'
  induction G' using Quotient.inductionOn with
  | h G' =>
    have hG := Quotient.forall_of_finChoice_eq hG
    have hG' : G = (λi => G i) := rfl
    simp only [cfg]
    rw [hG']
    simp only [Set.mem_setOf_eq, lsubst_quot, List.get_eq_getElem, hG, Fin.getElem_fin, vwk_id_quot,
      Subst.Eqv.liftn_append_quot, Subst.Eqv.vlift_quot, Quotient.finChoice_eq, Eqv.cfg_inner_quot]
    rfl

theorem Subst.InS.vsubst_congr {Γ Δ : Ctx α ε} {L K : LCtx α}
  {ρ ρ' : Term.Subst.InS φ Γ Δ} {σ σ' : Subst.InS φ Δ L K}
  (hρ : ρ ≈ ρ') (hσ : σ ≈ σ') : σ.vsubst ρ ≈ σ'.vsubst ρ'
  := λi => Region.InS.vsubst_congr (Term.Subst.InS.slift_congr hρ) (hσ i)

theorem Subst.InS.vwk_congr {Γ Δ : Ctx α ε} {L K : LCtx α}
  {ρ ρ' : Γ.InS Δ} {σ σ' : Subst.InS φ Δ L K}
  (hρ : ρ ≈ ρ') (hσ : σ ≈ σ') : σ.vwk ρ ≈ σ'.vwk ρ'
  := λi => Region.InS.vwk_congr (Ctx.InS.slift_congr hρ) (hσ i)

def Subst.Eqv.vwk {Γ Δ : Ctx α ε} {L K : LCtx α}
  (ρ : Γ.InS Δ) (σ : Subst.Eqv φ Δ L K) : Subst.Eqv φ Γ L K
  := Quotient.liftOn σ (λσ => ⟦σ.vwk ρ⟧)
    (λ_ _ hσ => Quotient.sound <| Subst.InS.vwk_congr (by rfl) hσ)

@[simp]
theorem Subst.Eqv.vwk_quot {Γ Δ : Ctx α ε} {L K : LCtx α}
  {ρ : Γ.InS Δ} {σ : Subst.InS φ Δ L K}
  : vwk ρ ⟦σ⟧ = ⟦σ.vwk ρ⟧ := rfl

theorem Subst.Eqv.vwk_wk0 {Γ : Ctx α ε} {σ : Subst.Eqv φ Γ L K}
  : (σ.vwk <| Ctx.InS.wk0 (head := head)) = σ.vlift := by
  induction σ using Quotient.inductionOn; rfl

theorem Subst.Eqv.vwk_vwk {Γ Δ Ξ : Ctx α ε} {L K : LCtx α}
  {ρ : Γ.InS Δ} {τ : Δ.InS Ξ} {σ : Subst.Eqv φ Ξ L K}
  : (σ.vwk τ).vwk ρ = σ.vwk (ρ.comp τ) := by
  induction σ using Quotient.inductionOn
  simp [Subst.InS.vwk_vwk]

theorem Eqv.vwk_lsubst {Γ Δ : Ctx α ε}
  {L K : LCtx α} {σ : Subst.Eqv φ Δ L K} {ρ : Γ.InS Δ}
  {r : Eqv φ Δ L}
  : (r.lsubst σ).vwk ρ = (r.vwk ρ).lsubst (σ.vwk ρ)
  := by
  induction r using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  simp [InS.vwk_lsubst]

def Subst.Eqv.vsubst {Γ Δ : Ctx α ε} {L K : LCtx α}
  (ρ : Term.Subst.Eqv φ Γ Δ) (σ : Subst.Eqv φ Δ L K) : Subst.Eqv φ Γ L K
  := Quotient.liftOn₂ ρ σ (λρ σ => ⟦σ.vsubst ρ⟧)
    (λ_ _ _ _ hρ hσ => Quotient.sound <| Subst.InS.vsubst_congr hρ hσ)

@[simp]
theorem Subst.Eqv.vsubst_quot {Γ Δ : Ctx α ε} {L K : LCtx α}
  {ρ : Term.Subst.InS φ Γ Δ} {σ : Subst.InS φ Δ L K}
  : vsubst ⟦ρ⟧ ⟦σ⟧ = ⟦σ.vsubst ρ⟧ := rfl

theorem Eqv.vsubst_lsubst {Γ Δ : Ctx α ε}
  {L K : LCtx α} {σ : Subst.Eqv φ Δ L K} {ρ : Term.Subst.Eqv φ Γ Δ}
  {r : Eqv φ Δ L}
  : (r.lsubst σ).vsubst ρ = (r.vsubst ρ).lsubst (σ.vsubst ρ)
  := by
  induction σ using Quotient.inductionOn
  induction ρ using Quotient.inductionOn
  induction r using Quotient.inductionOn
  simp [InS.vsubst_lsubst]

theorem InS.cfgSubstCongr {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {G G' : ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)} (hG : G ≈ G')
  : cfgSubst R G ≈ cfgSubst R G' := λi => by
  simp only [List.get_eq_getElem, get_cfgSubst]
  apply InS.cfg_congr
  rfl
  intro i
  apply InS.vwk_congr_right
  exact (hG i)

def Eqv.cfgSubstInner {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α)
  (G : Quotient (α := ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)) inferInstance)
  : Subst.Eqv φ Γ (R ++ L) L
  := Quotient.liftOn G (λG => ⟦InS.cfgSubst R G⟧) (λ_ _ h => Quotient.sound <| InS.cfgSubstCongr h)

def Eqv.cfgSubst {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α) (G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : Subst.Eqv φ Γ (R ++ L) L
  := cfgSubstInner R (Quotient.finChoice G)

@[simp]
theorem Eqv.cfgSubst_quot {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {G : ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : cfgSubst R (λi => ⟦G i⟧) = ⟦InS.cfgSubst R G⟧ := by
  simp [cfgSubst, Quotient.finChoice_eq, cfgSubstInner]

theorem InS.cfgSubstCongr' {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {G G' : ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)} (hG : G ≈ G')
  : cfgSubst' R G ≈ cfgSubst' R G' := λi => by
  simp only [List.get_eq_getElem, get_cfgSubst']
  split
  · apply InS.cfg_congr
    rfl
    intro i
    apply InS.vwk_congr_right
    exact (hG i)
  · rfl

def Eqv.cfgSubstInner' {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α)
  (G : Quotient (α := ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)) inferInstance)
  : Subst.Eqv φ Γ (R ++ L) L
  := Quotient.liftOn G (λG => ⟦InS.cfgSubst' R G⟧)
    (λ_ _ h => Quotient.sound <| InS.cfgSubstCongr' h)

def Eqv.cfgSubst' {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α) (G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : Subst.Eqv φ Γ (R ++ L) L
  := cfgSubstInner' R (Quotient.finChoice G)

@[simp]
theorem Eqv.cfgSubst'_quot {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {G : ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : cfgSubst' R (λi => ⟦G i⟧) = ⟦InS.cfgSubst' R G⟧ := by
  simp [cfgSubst', Quotient.finChoice_eq, cfgSubstInner']

theorem Eqv.cfgSubst_get {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)} {i : Fin (R ++ L).length}
  : (cfgSubst R G).get i = cfg R (br i (Term.Eqv.var 0 Ctx.Var.shead) (by simp)) (λi => (G i).vwk1)
  := by
  induction G using Eqv.choiceInduction
  rw [cfgSubst_quot]
  simp only [List.get_eq_getElem, Subst.Eqv.get_quot, InS.get_cfgSubst, Term.Eqv.var, br_quot, vwk1,
    vwk_quot]
  rw [<-cfg_quot]
  rfl

theorem Eqv.cfgSubst'_get {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)} {i : Fin (R ++ L).length}
  : (cfgSubst' R G).get i = if h : i < R.length then
      cfg R (br i (Term.Eqv.var 0 Ctx.Var.shead) (by simp)) (λi => (G i).vwk1)
    else
      br (i - R.length) (Term.Eqv.var 0 Ctx.Var.shead)
        (by
          simp only [List.get_eq_getElem]
          rw [List.getElem_append_right]
          apply LCtx.Trg.of_getElem
          assumption
          have hi : i < R.length + L.length := List.length_append _ _ ▸ i.prop;
          omega
        )
  := by
  induction G using Eqv.choiceInduction
  rw [cfgSubst'_quot]
  simp only [List.get_eq_getElem, Subst.Eqv.get_quot, InS.get_cfgSubst', vwk1_quot]
  split
  · rw [<-cfg_quot]; rfl
  · rfl

theorem Eqv.cfgSubst'_get_ge  {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)} {i : Fin (R ++ L).length}
  (h : i ≥ R.length) : (cfgSubst' R G).get i = br (i - R.length) (Term.Eqv.var 0 Ctx.Var.shead)
    (by
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right]
      apply LCtx.Trg.of_getElem
      omega
      have hi : i < R.length + L.length := List.length_append _ _ ▸ i.prop;
      omega
    )
  := by rw [Eqv.cfgSubst'_get, dite_cond_eq_false]; simp [h]

theorem Eqv.vlift_cfgSubst {Γ : Ctx α ε} {L : LCtx α} (R : LCtx α)
  (G : ∀i : Fin R.length, Eqv φ ((R.get i, ⊥)::Γ) (R ++ L))
  : (Eqv.cfgSubst R G).vlift = Eqv.cfgSubst R (λi => (G i).vwk1 (inserted := inserted)) := by
  induction G using Eqv.choiceInduction
  rw [cfgSubst_quot]
  simp only [Subst.Eqv.vlift_quot, InS.vlift_cfgSubst]
  rw [<-cfgSubst_quot]
  rfl

def Eqv.ucfg
  (R : LCtx α)
  (β : Eqv φ Γ (R ++ L)) (G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : Eqv φ Γ L := β.lsubst (cfgSubst R G)

theorem Eqv.ucfg_quot
  {R : LCtx α} {β : InS φ Γ (R ++ L)} {G : ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : ucfg R ⟦β⟧ (λi => ⟦G i⟧) = ⟦InS.ucfg R β G⟧ := by rw [ucfg, cfgSubst_quot]; rfl

def Eqv.ucfg'
  (R : LCtx α)
  (β : Eqv φ Γ (R ++ L)) (G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : Eqv φ Γ L := β.lsubst (cfgSubst' R G)

theorem Eqv.ucfg'_quot
  {R : LCtx α} {β : InS φ Γ (R ++ L)} {G : ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : ucfg' R ⟦β⟧ (λi => ⟦G i⟧) = ⟦InS.ucfg' R β G⟧ := by rw [ucfg', cfgSubst'_quot]; rfl

theorem Eqv.cfg_eq_ucfg'
  {R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : cfg R β G = ucfg' R β G := by
  induction β using Quotient.inductionOn
  induction G using Eqv.choiceInduction
  rw [cfg_quot, ucfg'_quot]
  apply Quotient.sound
  apply Uniform.rel
  apply TStep.reduce
  apply InS.coe_wf
  apply InS.coe_wf
  apply Reduce.ucfg'

theorem Eqv.cfg_br_ge {Γ : Ctx α ε} {L : LCtx α}
  {ℓ} {a : Term.Eqv φ Γ ⟨A, ⊥⟩}
  {R : LCtx α} {G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  {hℓ : (R ++ L).Trg ℓ A} (hℓ' : R.length ≤ ℓ)
  : (Eqv.br ℓ a hℓ).cfg R G = Eqv.br (ℓ - R.length) a (hℓ.of_ge hℓ')
  := by
  rw [cfg_eq_ucfg', ucfg', lsubst_br, cfgSubst'_get_ge hℓ']
  simp

theorem Eqv.cfg_br_add {Γ : Ctx α ε} {L : LCtx α}
  {ℓ} {a : Term.Eqv φ Γ ⟨A, ⊥⟩}
  {R : LCtx α} {G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  {hℓ : (R ++ L).Trg (ℓ + R.length) A}
  : (Eqv.br (ℓ + R.length) a hℓ).cfg R G = Eqv.br ℓ a hℓ.of_add
  := by rw [cfg_br_ge] <;> simp

theorem Eqv.cfgSubst_eq_cfgSubst' {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : cfgSubst R G = cfgSubst' R G := by
  ext i;
  rw [cfgSubst_get, cfgSubst'_get]
  split
  case isTrue => rfl
  case isFalse h => rw [Eqv.cfg_br_ge (Nat.ge_of_not_lt h)]

theorem Eqv.ucfg_eq_ucfg'
  {R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : ucfg R β G = ucfg' R β G := by rw [ucfg, ucfg', cfgSubst_eq_cfgSubst']

theorem Eqv.cfg_eq_ucfg
  {R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : cfg R β G = ucfg R β G := by rw [cfg_eq_ucfg', ucfg_eq_ucfg']

theorem Eqv.ucfg'_eq_cfg
  {R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : ucfg' R β G = cfg R β G := Eqv.cfg_eq_ucfg'.symm

theorem Eqv.ucfg_eq_cfg
  {R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : ucfg R β G = cfg R β G := Eqv.cfg_eq_ucfg.symm

theorem Eqv.cfgSubst_get' {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)} {i : Fin (R ++ L).length}
  : (cfgSubst R G).get i = if h : i < R.length then
      cfg R (br i (Term.Eqv.var 0 Ctx.Var.shead) (by simp)) (λi => (G i).vwk1)
    else
      br (i - R.length) (Term.Eqv.var 0 Ctx.Var.shead)
        (by
          simp only [List.get_eq_getElem]
          rw [List.getElem_append_right]
          apply LCtx.Trg.of_getElem
          assumption
          have hi : i < R.length + L.length := List.length_append _ _ ▸ i.prop;
          omega
        )
  := by rw [cfgSubst_eq_cfgSubst', cfgSubst'_get]

theorem Eqv.cfgSubst_get_ge  {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)} {i : Fin (R ++ L).length}
  (h : i ≥ R.length) : (cfgSubst R G).get i = br (i - R.length) (Term.Eqv.var 0 Ctx.Var.shead)
    (by
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right]
      apply LCtx.Trg.of_getElem
      omega
      have hi : i < R.length + L.length := List.length_append _ _ ▸ i.prop;
      omega
    )
  := by rw [Eqv.cfgSubst_get', dite_cond_eq_false]; simp [h]

def Subst.Eqv.fromFCFG {Γ : Ctx α ε} {L K : LCtx α}
  (G : ∀i : Fin L.length, Region.Eqv φ ((L.get i, ⊥)::Γ) K)
  : Subst.Eqv φ Γ L K
  := Quotient.liftOn (Quotient.finChoice G) (λG => ⟦Region.CFG.toSubst G⟧)
      (λ_ _ h => Quotient.sound <| λi => by simp [h i])

theorem Subst.Eqv.fromFCFG_quot {Γ : Ctx α ε} {L K : LCtx α}
  {G : ∀i : Fin L.length, Region.InS φ ((L.get i, ⊥)::Γ) K}
  : fromFCFG (λi => ⟦G i⟧) = ⟦Region.CFG.toSubst G⟧ := by
  simp [fromFCFG, Quotient.finChoice_eq_choice]

theorem Subst.Eqv.get_fromFCFG {Γ : Ctx α ε} {L K : LCtx α}
  {G : ∀i : Fin L.length, Region.Eqv φ ((L.get i, ⊥)::Γ) K} {i : Fin L.length}
  : (fromFCFG G).get i = G i
  := by induction G using Eqv.choiceInduction; rw [Subst.Eqv.fromFCFG_quot]; simp

theorem Subst.Eqv.fromFCFG_get {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.Eqv φ Γ L K}
  : (fromFCFG σ.get) = σ := by ext k; simp [Subst.Eqv.get_fromFCFG]

theorem Subst.Eqv.get_fromFCFG' {Γ : Ctx α ε} {L K : LCtx α}
  {G : ∀i : Fin L.length, Region.Eqv φ ((L.get i, ⊥)::Γ) K}
  : (fromFCFG G).get = G := funext (λ_ => get_fromFCFG)

def Subst.Eqv.fromFCFG_append {Γ : Ctx α ε} {L K R : LCtx α}
  (G : ∀i : Fin L.length, Region.Eqv φ ((L.get i, ⊥)::Γ) (K ++ R))
  : Subst.Eqv φ Γ (L ++ R) (K ++ R)
  := Quotient.liftOn (Quotient.finChoice G) (λG => ⟦Region.CFG.toSubst_append G⟧)
      (λ_ _ h => Quotient.sound <| λi => by
        simp only [CFG.get_toSubst_append]
        split
        · apply InS.cast_congr
          apply h
        · rfl
        )

theorem Subst.Eqv.fromFCFG_append_quot {Γ : Ctx α ε} {L K R : LCtx α}
  {G : ∀i : Fin L.length, Region.InS φ ((L.get i, ⊥)::Γ) (K ++ R)}
  : fromFCFG_append (λi => ⟦G i⟧) = ⟦Region.CFG.toSubst_append G⟧ := by
  simp [fromFCFG_append, Quotient.finChoice_eq_choice]

def _root_.BinSyntax.LCtx.InS.toSubstE {Γ : Ctx α ε} {L K : LCtx α}
  (σ : L.InS K) : Subst.Eqv φ Γ L K := ⟦σ.toSubst⟧

theorem Eqv.lsubst_toSubstE {Γ : Ctx α ε} {L K : LCtx α}
  {r : Eqv φ Γ L} {σ : L.InS K}
  : r.lsubst σ.toSubstE = r.lwk σ := by
  induction r using Quotient.inductionOn
  simp only [lwk_quot, ← InS.lsubst_toSubst]
  rfl

@[simp]
theorem Subst.Eqv.get_toSubstE {Γ : Ctx α ε} {L K : LCtx α}
  {σ : L.InS K} {i : Fin L.length}
  : (σ.toSubstE).get i
  = Eqv.br (φ := φ) (Γ := _::Γ) (σ.val i) (Term.Eqv.var 0 Ctx.Var.shead) (σ.prop i i.prop) := rfl

theorem Eqv.dinaturality {Γ : Ctx α ε} {R R' L : LCtx α}
  {σ : Subst.Eqv φ Γ R (R' ++ L)} {β : Eqv φ Γ (R ++ L)}
  {G : (i : Fin R'.length) → Eqv φ (⟨R'.get i, ⊥⟩::Γ) (R ++ L)}
  : cfg R' (β.lsubst σ.extend_in) (λi => (G i).lsubst σ.extend_in.vlift)
  = cfg R β (λi => (σ.get i).lsubst (Subst.Eqv.fromFCFG_append G).vlift)
  := by
  induction σ using Quotient.inductionOn with | h σ =>
  induction β using Quotient.inductionOn with | h β =>
  induction G using Eqv.choiceInduction with | choice G =>
  convert Quotient.sound <| InS.dinaturality (σ := σ) (β := β) (G := G)
  · simp [<-cfg_quot]
  · rw [<-cfg_quot]
    congr
    funext i
    rw [Subst.Eqv.fromFCFG_append_quot]
    simp [Subst.InS.cfg]

theorem Eqv.dinaturality_rec {Γ : Ctx α ε} {R R' L : LCtx α}
  {σ : Subst.Eqv φ Γ R R'} {β : Eqv φ Γ (R ++ L)}
  {G : (i : Fin R'.length) → Eqv φ (⟨R'.get i, ⊥⟩::Γ) (R ++ L)}
  : cfg R' (β.lsubst σ.extend) (λi => (G i).lsubst σ.extend.vlift)
  = cfg R β (λi => (σ.get i).lsubst (Subst.Eqv.fromFCFG G).vlift)
  := by
  rw [<-Subst.Eqv.extend_in_extend_out, dinaturality]
  congr; funext i
  rw [Subst.Eqv.get_extend_out, lwk_id_eq_lwk, <-Eqv.lsubst_toSubst, lsubst_lsubst]
  congr; ext k
  induction G using Eqv.choiceInduction
  rw [Subst.Eqv.fromFCFG_append_quot, Subst.Eqv.fromFCFG_quot]
  apply Eqv.eq_of_reg_eq
  simp [Subst.fromFCFG, Subst.vlift, Region.vsubst0_var0_vwk1]

theorem Eqv.dinaturality_from_one {Γ : Ctx α ε} {R L : LCtx α}
  {σ : Subst.Eqv φ Γ R (B::L)} {β : Eqv φ Γ (R ++ L)}
  {G : Eqv φ (⟨B, ⊥⟩::Γ) (R ++ L)}
  : cfg [B] (β.lsubst σ.extend_in) (Fin.elim1 $ G.lsubst σ.extend_in.vlift)
  = cfg R β (λi => (σ.get i).lsubst (Subst.Eqv.fromFCFG_append (L := [B]) (Fin.elim1 G)).vlift)
  := dinaturality (Γ := Γ) (R := R) (R' := [B]) (L := L) (σ := σ) (β := β) (G := Fin.elim1 G)

theorem Eqv.dinaturality_from_one_rec {Γ : Ctx α ε} {R L : LCtx α}
  {σ : Subst.Eqv φ Γ R [B]} {β : Eqv φ Γ (R ++ L)}
  {G : Eqv φ (⟨B, ⊥⟩::Γ) (R ++ L)}
  : cfg [B] (β.lsubst σ.extend) (Fin.elim1 $ G.lsubst σ.extend.vlift)
  = cfg R β (λi => (σ.get i).lsubst (Subst.Eqv.fromFCFG (Fin.elim1 G)).vlift)
  := dinaturality_rec (Γ := Γ) (R := R) (R' := [B]) (L := L) (σ := σ) (β := β) (G := Fin.elim1 G)

theorem Eqv.dinaturality_to_one {Γ : Ctx α ε} {R' L : LCtx α}
  {σ : Subst.Eqv φ Γ [A] (R' ++ L)} {β : Eqv φ Γ (A::L)}
  {G : (i : Fin R'.length) → Eqv φ (⟨R'.get i, ⊥⟩::Γ) (A::L)}
  : cfg R' (β.lsubst σ.extend_in) (λi => (G i).lsubst σ.extend_in.vlift)
  = cfg [A] β (Fin.elim1 $ (σ.get _).lsubst (Subst.Eqv.fromFCFG_append G).vlift)
  := dinaturality (Γ := Γ) (R := [A]) (R' := R') (L := L) (σ := σ) (β := β) (G := G)

theorem Eqv.dinaturality_to_one_rec {Γ : Ctx α ε} {R' L : LCtx α}
  {σ : Subst.Eqv φ Γ [A] R'} {β : Eqv φ Γ (A::L)}
  {G : (i : Fin R'.length) → Eqv φ (⟨R'.get i, ⊥⟩::Γ) (A::L)}
  : cfg R' (β.lsubst σ.extend) (λi => (G i).lsubst σ.extend.vlift)
  = cfg [A] β (Fin.elim1 $ (σ.get _).lsubst (Subst.Eqv.fromFCFG G).vlift)
  := dinaturality_rec (Γ := Γ) (R := [A]) (R' := R') (L := L) (σ := σ) (β := β) (G := G)

theorem Eqv.dinaturality_one {Γ : Ctx α ε} {L : LCtx α}
  {σ : Subst.Eqv φ Γ [A] ([B] ++ L)} {β : Eqv φ Γ (A::L)}
  {G : Eqv φ (⟨B, ⊥⟩::Γ) ([A] ++ L)}
  : cfg [B] (β.lsubst σ.extend_in) (Fin.elim1 $ G.lsubst σ.extend_in.vlift)
  = cfg [A] β (Fin.elim1 $ (σ.get _).lsubst (Subst.Eqv.fromFCFG_append (Fin.elim1 G)).vlift)
  := dinaturality (Γ := Γ) (R := [A]) (R' := [B]) (L := L) (σ := σ) (β := β) (G := Fin.elim1 G)

def Subst.InS.initial {Γ : Ctx α ε} {L : LCtx α}
  : Subst.InS φ Γ [] L := ⟨Subst.id, λi => i.elim0⟩

def Subst.Eqv.initial {Γ : Ctx α ε} {L : LCtx α}
  : Subst.Eqv φ Γ [] L := ⟦Subst.InS.initial⟧

theorem Subst.Eqv.initial_eq {Γ : Ctx α ε} {L : LCtx α} {σ σ' : Subst.Eqv φ Γ [] L}
  : σ = σ' := by
  induction σ using Quotient.inductionOn
  induction σ' using Quotient.inductionOn
  apply Quotient.sound
  intro i
  exact i.elim0

def Eqv.csubst {Γ : Ctx α ε} {L : LCtx α} (r : Eqv φ ((A, ⊥)::Γ) L) : Subst.Eqv φ Γ [A] L
  := Quotient.liftOn r (λr => ⟦r.csubst⟧)
    (λ_ _ h => Quotient.sound <| λi => by cases i using Fin.elim1; exact h)

@[simp]
theorem Eqv.csubst_quot {Γ : Ctx α ε} {L : LCtx α} {r : InS φ ((A, ⊥)::Γ) L}
  : csubst ⟦r⟧ = ⟦r.csubst⟧ := rfl

@[simp]
theorem Eqv.csubst_get {Γ : Ctx α ε} {L : LCtx α} {r : Eqv φ ((A, ⊥)::Γ) L} {i : Fin [A].length}
  : (r.csubst).get i = r.cast (by simp) rfl := by
  induction r using Quotient.inductionOn
  rfl

theorem Eqv.fromFCFG_elim1 {Γ : Ctx α ε} {G : Region.Eqv φ ((A, ⊥)::Γ) [A]}
  : Subst.Eqv.fromFCFG (Fin.elim1 G) = G.csubst := by
  ext i
  induction i using Fin.elim1
  induction G using Quotient.inductionOn
  rfl

def Subst.Eqv.id {Γ : Ctx α ε} {L : LCtx α} : Subst.Eqv φ Γ L L := ⟦Subst.InS.id⟧

@[simp]
theorem Subst.Eqv.id_comp {Γ : Ctx α ε} {L : LCtx α} {σ : Subst.Eqv φ Γ L L}
  : id.comp σ = σ := by
  induction σ using Quotient.inductionOn
  simp [id]

@[simp]
theorem Subst.Eqv.comp_id {Γ : Ctx α ε} {L : LCtx α} {σ : Subst.Eqv φ Γ L L}
  : σ.comp id = σ := by
  induction σ using Quotient.inductionOn
  simp [id]

theorem Subst.Eqv.get_id {Γ : Ctx α ε} {L : LCtx α} {i : Fin L.length}
  : (id : Subst.Eqv φ Γ L L).get i = Eqv.br i (Term.Eqv.var 0 Ctx.Var.shead) (by simp) := by
  rfl

@[simp]
theorem Eqv.lsubst_id {Γ : Ctx α ε} {L : LCtx α} {r : Eqv φ Γ L}
  : r.lsubst Subst.Eqv.id = r := by
  induction r using Quotient.inductionOn
  simp [Subst.Eqv.id]

theorem Eqv.lsubst_id' {Γ : Ctx α ε} {L : LCtx α} {r : Eqv φ Γ L} {σ : Subst.Eqv φ Γ L L}
  (h : σ = Subst.Eqv.id) : r.lsubst σ = r := by cases h; simp

-- theorem Eqv.cfg_let1 {Γ : Ctx α ε} {L : LCtx α}
--   (a : Term.Eqv φ Γ ⟨A, ea⟩)
--   (R : LCtx α) (β : Eqv φ (⟨A, ⊥⟩::Γ) (R ++ L))
--   (G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
--     : (let1 a β).cfg R G = (let1 a $ β.cfg R (λi => (G i).vwk1))
--   := by
--   induction a using Quotient.inductionOn
--   simp only [cfg]
--   generalize hG : Quotient.finChoice G = G'
--   induction β using Quotient.inductionOn with
--   | h β =>
--     induction G' using Quotient.inductionOn with
--     | h G' =>
--       have hβ : ⟦β⟧ = β.q := rfl
--       simp only [hβ, InS.let1_q, InS.cfg_inner_q]
--       apply Eq.trans
--       apply Eqv.sound
--       apply InS.cfg_let1
--       rw [<-InS.let1_q, <-InS.cfg_q]
--       congr
--       funext i
--       rw [<-InS.vwk1_q]
--       rw [InS.q]
--       congr
--       apply Eq.symm
--       apply Quotient.forall_of_finChoice_eq hG

-- theorem Eqv.cfg_let2 {Γ : Ctx α ε} {L : LCtx α}
--   (a : Term.Eqv φ Γ ⟨Ty.prod A B, ea⟩)
--   (R : LCtx α) (β : Eqv φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) (R ++ L))
--   (G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
--     : (let2 a β).cfg R G = (let2 a $ β.cfg R (λi => (G i).vwk1.vwk1))
--   := by
--   induction a using Quotient.inductionOn
--   simp only [cfg]
--   generalize hG : Quotient.finChoice G = G'
--   induction β using Quotient.inductionOn with
--   | h β =>
--     induction G' using Quotient.inductionOn with
--     | h G' =>
--       have hβ : ⟦β⟧ = β.q := rfl
--       simp only [hβ, InS.let2_q, InS.cfg_inner_q]
--       apply Eq.trans
--       apply Eqv.sound
--       apply InS.cfg_let2
--       rw [<-InS.let2_q, <-InS.cfg_q]
--       congr
--       funext i
--       simp only [<-InS.vwk1_q]
--       rw [InS.q]
--       congr
--       apply Eq.symm
--       apply Quotient.forall_of_finChoice_eq hG

theorem Eqv.cfg_case {Γ : Ctx α ε} {L : LCtx α}
  (e : Term.Eqv φ Γ ⟨Ty.coprod A B, ea⟩)
  (R : LCtx α)
  (r : Eqv φ (⟨A, ⊥⟩::Γ) (R ++ L))
  (s : Eqv φ (⟨B, ⊥⟩::Γ) (R ++ L))
  (G : (i : Fin R.length) → Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
    : (Eqv.case e r s).cfg R G
    = Eqv.case e (r.cfg R (λi => (G i).vwk1)) (s.cfg R (λi => (G i).vwk1))
  := by
  simp only [cfg_eq_ucfg, ucfg, lsubst_case]
  congr <;> {
    induction G using Eqv.choiceInduction
    simp only [cfgSubst_quot, vwk1_quot, Subst.Eqv.vlift_quot]
    congr
    ext k
    simp [Region.cfgSubst, Region.Subst.vlift, Region.vwk1, Region.vwk_vwk, <-Nat.liftWk_comp]
    rfl
  }
