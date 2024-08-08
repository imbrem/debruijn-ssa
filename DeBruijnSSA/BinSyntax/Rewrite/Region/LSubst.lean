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

theorem InS.lsubst_congr_subst {Γ : Ctx α ε} {L K : LCtx α} {σ τ : Subst.InS φ Γ L K}
  (h : σ ≈ τ) (r : InS φ Γ L) : r.lsubst σ ≈ r.lsubst τ := sorry

theorem InS.lsubst_congr_right {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.InS φ Γ L K)
  {r r' : InS φ Γ L} (h : r ≈ r') : r.lsubst σ ≈ r'.lsubst σ := sorry

theorem InS.lsubst_congr {Γ : Ctx α ε} {L K : LCtx α} {σ σ' : Subst.InS φ Γ L K}
  {r r' : InS φ Γ L} (hσ : σ ≈ σ') (hr : r ≈ r') : r.lsubst σ ≈ r'.lsubst σ'
  := Setoid.trans (lsubst_congr_subst hσ r) (lsubst_congr_right σ' hr)

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
    sorry

def Subst.Eqv.vlift {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.Eqv φ Γ L K)
  : Subst.Eqv φ (head::Γ) L K
  := Quotient.liftOn σ
    (λσ => ⟦σ.vlift⟧)
    sorry

@[simp]
theorem Subst.Eqv.vlift_quot {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K}
  : vlift (head := head) ⟦σ⟧ = ⟦σ.vlift⟧ := rfl

def Subst.Eqv.vliftn₂ {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.Eqv φ Γ L K)
  : Subst.Eqv φ (left::right::Γ) L K
  := Quotient.liftOn σ
    (λσ => ⟦σ.vliftn₂⟧)
    sorry

@[simp]
theorem Subst.Eqv.vliftn₂_quot {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K}
  : vliftn₂ (left := left) (right := right) ⟦σ⟧ = ⟦σ.vliftn₂⟧ := rfl

theorem Subst.Eqv.vliftn₂_eq_vlift_vlift {Γ : Ctx α ε} {L K : LCtx α} (σ : Subst.Eqv φ Γ L K)
  : σ.vliftn₂ (left := left) (right := right) = σ.vlift.vlift := by
  induction σ using Quotient.inductionOn;
  simp [Subst.InS.vliftn₂_eq_vlift_vlift]

def Subst.Eqv.extend {Γ : Ctx α ε} {L K R : LCtx α} (σ : Eqv φ Γ L K) : Eqv φ Γ (L ++ R) (K ++ R)
  := Quotient.liftOn σ (λσ => ⟦σ.extend⟧) sorry

@[simp]
theorem Subst.Eqv.extend_quot {Γ : Ctx α ε} {L K R : LCtx α} {σ : Subst.InS φ Γ L K}
  : extend (R := R) ⟦σ⟧ = ⟦σ.extend⟧ := rfl

def Subst.Eqv.extend_in {Γ : Ctx α ε} {L K R : LCtx α} (σ : Eqv φ Γ L (K ++ R))
  : Eqv φ Γ (L ++ R) (K ++ R)
  := Quotient.liftOn σ (λσ => ⟦σ.extend_in⟧) sorry

@[simp]
theorem Subst.Eqv.extend_in_quot {Γ : Ctx α ε} {L K R : LCtx α} {σ : Subst.InS φ Γ L (K ++ R)}
  : extend_in ⟦σ⟧ = ⟦σ.extend_in⟧ := rfl

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
  : Subst.Eqv φ Γ L J := Quotient.liftOn₂ σ τ (λσ τ => ⟦σ.comp τ⟧) sorry

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
    sorry

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
    sorry

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
theorem Eqv.lsubst_cfg {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  {σ : Subst.Eqv φ Γ L K}
  : (cfg R β G).lsubst σ
  = cfg R (β.lsubst (σ.liftn_append _)) (λi => (G i).lsubst (σ.liftn_append _).vlift) := by
  induction β using Quotient.inductionOn
  sorry

def Subst.Eqv.vsubst {Γ Δ : Ctx α ε} {L K : LCtx α}
  (ρ : Term.Subst.Eqv φ Γ Δ) (σ : Subst.Eqv φ Δ L K) : Subst.Eqv φ Γ L K
  := Quotient.liftOn₂ ρ σ (λρ σ => ⟦σ.vsubst ρ⟧) sorry

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

def Eqv.cfgSubstInner {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α)
  (G : Quotient (α := ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)) inferInstance)
  : Subst.Eqv φ Γ (R ++ L) L
  := Quotient.liftOn G (λG => ⟦InS.cfgSubst R G⟧) sorry

def Eqv.cfgSubst {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α) (G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : Subst.Eqv φ Γ (R ++ L) L
  := cfgSubstInner R (Quotient.finChoice G)

theorem Eqv.cfgSubst_quot {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {G : ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : cfgSubst R (λi => ⟦G i⟧) = ⟦InS.cfgSubst R G⟧ := sorry

def Eqv.cfgSubstInner' {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α)
  (G : Quotient (α := ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)) inferInstance)
  : Subst.Eqv φ Γ (R ++ L) L
  := Quotient.liftOn G (λG => ⟦InS.cfgSubst' R G⟧) sorry

def Eqv.cfgSubst' {Γ : Ctx α ε} {L : LCtx α}
  (R : LCtx α) (G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : Subst.Eqv φ Γ (R ++ L) L
  := cfgSubstInner' R (Quotient.finChoice G)

theorem Eqv.cfgSubst'_quot {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {G : ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : cfgSubst' R (λi => ⟦G i⟧) = ⟦InS.cfgSubst' R G⟧ := sorry

theorem Eqv.cfgSubst_eq_cfgSubst' {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : cfgSubst R G = cfgSubst' R G := sorry

theorem Eqv.cfgSubst_get {Γ : Ctx α ε} {L : LCtx α}
  {R : LCtx α} {G : ∀i : Fin R.length, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)} {i : Fin (R ++ L).length}
  : (cfgSubst R G).get i = cfg R (br i (Term.Eqv.var 0 Ctx.Var.shead) (by simp)) (λi => (G i).vwk1)
  := sorry

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
  := sorry

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

theorem Eqv.vlift_cfgSubst {Γ : Ctx α ε} {L : LCtx α} (R : LCtx α)
  (G : ∀i : Fin R.length, Eqv φ ((R.get i, ⊥)::Γ) (R ++ L))
  : (Eqv.cfgSubst R G).vlift = Eqv.cfgSubst R (λi => (G i).vwk1 (inserted := inserted)) := by
  sorry

def Eqv.ucfg
  (R : LCtx α)
  (β : Eqv φ Γ (R ++ L)) (G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : Eqv φ Γ L := β.lsubst (cfgSubst R G)

theorem Eqv.ucfg_quot
  {R : LCtx α} {β : InS φ Γ (R ++ L)} {G : ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : ucfg R ⟦β⟧ (λi => ⟦G i⟧) = ⟦InS.ucfg R β G⟧ := sorry

def Eqv.ucfg'
  (R : LCtx α)
  (β : Eqv φ Γ (R ++ L)) (G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : Eqv φ Γ L := β.lsubst (cfgSubst' R G)

theorem Eqv.ucfg'_quot
  {R : LCtx α} {β : InS φ Γ (R ++ L)} {G : ∀i, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : ucfg' R ⟦β⟧ (λi => ⟦G i⟧) = ⟦InS.ucfg' R β G⟧ := sorry

theorem Eqv.ucfg_eq_ucfg'
  {R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : ucfg R β G = ucfg' R β G := by rw [ucfg, ucfg', cfgSubst_eq_cfgSubst']

theorem Eqv.cfg_eq_ucfg'
  {R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : cfg R β G = ucfg' R β G := sorry

theorem Eqv.cfg_eq_ucfg
  {R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : cfg R β G = ucfg R β G := by rw [cfg_eq_ucfg', ucfg_eq_ucfg']

theorem Eqv.ucfg'_eq_cfg
  {R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : ucfg' R β G = cfg R β G := Eqv.cfg_eq_ucfg'.symm

theorem Eqv.ucfg_eq_cfg
  {R : LCtx α} {β : Eqv φ Γ (R ++ L)} {G : ∀i, Eqv φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)}
  : ucfg R β G = cfg R β G := Eqv.cfg_eq_ucfg.symm

def Subst.Eqv.fromFCFG {Γ : Ctx α ε} {L K : LCtx α}
  (G : ∀i : Fin L.length, Region.Eqv φ ((L.get i, ⊥)::Γ) K)
  : Subst.Eqv φ Γ L K
  := Quotient.liftOn (Quotient.finChoice G) (λG => ⟦Region.CFG.toSubst G⟧) sorry

def Subst.Eqv.fromFCFG_append {Γ : Ctx α ε} {L K R : LCtx α}
  (G : ∀i : Fin L.length, Region.Eqv φ ((L.get i, ⊥)::Γ) (K ++ R))
  : Subst.Eqv φ Γ (L ++ R) (K ++ R)
  := Quotient.liftOn (Quotient.finChoice G) (λG => ⟦Region.CFG.toSubst_append G⟧) sorry

theorem Eqv.dinaturality {Γ : Ctx α ε} {R R' L : LCtx α}
  {σ : Subst.Eqv φ Γ R (R' ++ L)} {β : Eqv φ Γ (R ++ L)}
  {G : (i : Fin R'.length) → Eqv φ (⟨R'.get i, ⊥⟩::Γ) (R ++ L)}
  : cfg R' (β.lsubst σ.extend_in) (λi => (G i).lsubst σ.extend_in.vlift)
  = cfg R β (λi => (σ.get i).lsubst (Subst.Eqv.fromFCFG_append G).vlift)
  := sorry
