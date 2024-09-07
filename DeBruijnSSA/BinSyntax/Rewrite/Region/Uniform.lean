import DeBruijnSSA.BinSyntax.Typing.Region.Compose
import DeBruijnSSA.BinSyntax.Syntax.Compose.Term
import DeBruijnSSA.BinSyntax.Rewrite.Region.Cong
import DeBruijnSSA.BinSyntax.Rewrite.Term.Setoid

import Discretion.Utils.Quotient

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

open Term

-- Note: this is a PER over well-formed terms

inductive Uniform (P : Ctx α ε → LCtx α → Region φ → Region φ → Prop)
  : Ctx α ε → LCtx α → Region φ → Region φ → Prop
  | case_left : e.Wf Γ ⟨Ty.coprod A B, e'⟩ → Uniform P (⟨A, ⊥⟩::Γ) L r r' → s.Wf (⟨B, ⊥⟩::Γ) L
    → Uniform P Γ L (Region.case e r s) (Region.case e r' s)
  | case_right : e.Wf Γ ⟨Ty.coprod A B, e'⟩ → r.Wf (⟨A, ⊥⟩::Γ) L → Uniform P (⟨B, ⊥⟩::Γ) L s s'
    → Uniform P Γ L (Region.case e r s) (Region.case e r s')
  | let1 : a.Wf Γ ⟨A, e⟩ → Uniform P (⟨A, ⊥⟩::Γ) L r r'
    → Uniform P Γ L (Region.let1 a r) (Region.let1 a r')
  | let2 : a.Wf Γ ⟨Ty.prod A B, e⟩ → Uniform P (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L r r'
    → Uniform P Γ L (Region.let2 a r) (Region.let2 a r')
  | cfg_entry (R : LCtx α) :
    (hR : R.length = n) →
    Uniform P Γ (R ++ L) β β' →
    (∀i : Fin n, (G i).Wf (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    Uniform P Γ L (Region.cfg β n G) (Region.cfg β' n G)
  | cfg_block (R : LCtx α) :
    (hR : R.length = n) →
    β.Wf Γ (R ++ L) →
    (hG : ∀i : Fin n, (G i).Wf (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    (i : Fin n) →
    Uniform P (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L) (G i) g' →
    Uniform P Γ L (Region.cfg β n G) (Region.cfg β n (Function.update G i g'))
  | uniform {e : Term φ} {β r s : Region φ}
    : β.Wf Γ (A::L)
    → e.Wf (⟨A, ⊥⟩::Γ) (B, ⊥)
    → r.Wf (⟨B, ⊥⟩::Γ) (B::L)
    → s.Wf (⟨A, ⊥⟩::Γ) (A::L)
    → Uniform P (⟨A, ⊥⟩::Γ) (B::L) ((ret e).wseq r) (s.wseq (ret e))
    → Uniform P Γ L
      (cfg (β.wrseq (ret e)) 1 (Fin.elim1 r))
      (cfg β 1 (Fin.elim1 s))
  | codiagonal {β G : Region φ}
    : β.Wf Γ (A::L) →
      G.Wf (⟨A, ⊥⟩::Γ) (A::A::L) →
      Uniform P Γ L
        (cfg β 1 (Fin.elim1 $ cfg nil 1 (Fin.elim1 G.vwk1)))
        (cfg β 1 (Fin.elim1 $ G.lsubst nil.lsubst0))
  | ucfg {R : LCtx α} {β : Region φ} {G : Fin n → Region φ}
    : (hR : R.length = n)
      → β.Wf Γ (R ++ L)
      → (∀i : Fin n, (G i).Wf ((R.get (i.cast hR.symm), ⊥)::Γ) (R ++ L)) →
      Uniform P Γ L (cfg β n G) (ucfg' n β G)
  -- | dinaturality {Γ : Ctx α ε} {L R R' : LCtx α} {β : Region φ}
  --   {G : Fin R'.length → Region φ} {σ : Subst φ}
  --   : σ.Wf Γ R (R' ++ L)
  --     → β.Wf Γ (R ++ L)
  --     → (∀i : Fin R'.length, (G i).Wf ((R'.get i, ⊥)::Γ) (R ++ L))
  --     → Uniform P Γ L
  --       (cfg
  --         (β.lsubst (σ.extend R.length R'.length)) R'.length
  --         (λi => (G i).lsubst (σ.extend R.length R'.length).vlift))
  --       (cfg β R.length
  --         (λi => (σ i).lsubst (Subst.fromFCFG R.length G).vlift))
  | refl : r.Wf Γ L → Uniform P Γ L r r
  | rel : P Γ L x y → Uniform P Γ L x y
  | symm : Uniform P Γ L x y → Uniform P Γ L y x
  | trans : Uniform P Γ L x y → Uniform P Γ L y z → Uniform P Γ L x z

theorem Uniform.map {P Q : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ L r r'}
  (f : ∀{Γ L r r'}, P Γ L r r' → Q Γ L r r') (p : Uniform P Γ L r r') : Uniform Q Γ L r r'
  := by induction p with
  | rel h => exact rel (f h)
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir
  | _ => constructor <;> assumption

theorem Uniform.flatten {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ L r r'}
  (p : Uniform (Uniform P) Γ L r r') : Uniform P Γ L r r'
  := by induction p with
  | rel h => exact h
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact Il.trans Ir
  | _ => constructor <;> assumption

theorem Uniform.duplicate {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ L r r'}
  (p : Uniform P Γ L r r') : Uniform (Uniform P) Γ L r r' := p.map Uniform.rel

theorem Uniform.idem {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop}
  : Uniform (Uniform P) = Uniform P := by
  ext Γ L r r'
  exact ⟨flatten, duplicate⟩

-- TODO: HaveType

-- TODO: Uniform ⊤ = HaveType

-- TODO: Uniform ⊥ = Uniform (· = ·) = (HaveType ⊓ (· = ·))

-- TODO: Uniform monotone; is uniform inf-preserving?

theorem Uniform.wf {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ L r r'}
  (toWf : ∀{Γ L r r'}, P Γ L r r' → r.Wf Γ L ∧ r'.Wf Γ L)
  (p : (Uniform P Γ L) r r') : r.Wf Γ L ∧ r'.Wf Γ L
  := by induction p with
  | case_left de _ ds Ir =>
    have ⟨dr, dr'⟩ := Ir
    exact ⟨dr.case de ds, dr'.case de ds⟩
  | case_right de dr _ Is =>
    have ⟨ds, ds'⟩ := Is
    exact ⟨dr.case de ds, dr.case de ds'⟩
  | let1 de _ Ir =>
    have ⟨dr, dr'⟩ := Ir
    exact ⟨dr.let1 de, dr'.let1 de⟩
  | let2 de _ Ir =>
    have ⟨dr, dr'⟩ := Ir
    exact ⟨dr.let2 de, dr'.let2 de⟩
  | cfg_entry R hR _ dG Iβ =>
    have ⟨dβ, dβ'⟩ := Iβ
    exact ⟨dβ.cfg _ R hR dG, dβ'.cfg _ R hR dG⟩
  | cfg_block R hR dβ dG i _ Ig =>
    have ⟨_, dg'⟩ := Ig
    constructor
    exact dβ.cfg _ R hR dG
    apply dβ.cfg _ R hR
    intro k
    simp only [Function.update, eq_rec_constant, dite_eq_ite]
    split
    case isTrue h => exact h ▸ dg'
    case isFalse h => apply dG
  | uniform dβ de dr ds =>
    constructor
    · apply Wf.cfg (R := [_]) (n := 1) (hR := rfl)
      · exact (dβ.wrseq (Wf.ret de))
      · exact Fin.elim1 dr
    · apply Wf.cfg (R := [_]) (n := 1) (hR := rfl)
      · exact dβ
      · exact Fin.elim1 ds
  | codiagonal dβ dG =>
    constructor
    · apply Wf.cfg (R := [_]) (n := 1) (hR := rfl) dβ
      intro i; cases i using Fin.elim1;
      apply Wf.cfg (R := [_]) (n := 1) (hR := rfl) Wf.nil
      intro i; cases i using Fin.elim1;
      exact dG.vwk1
    · apply Wf.cfg (R := [_]) (n := 1) (hR := rfl) dβ
      intro i; cases i using Fin.elim1;
      apply dG.lsubst Wf.nil.lsubst0
  | ucfg hR dβ dG => exact ⟨Wf.cfg _ _ hR dβ dG, Wf.ucfg' _ _ hR dβ dG⟩
  -- | dinaturality hσ dβ dG => exact ⟨
  --     Wf.cfg _ _ rfl (dβ.lsubst hσ.extend_in) (λi => (dG i).lsubst hσ.extend_in.vlift),
  --     Wf.cfg _ _ rfl dβ (λi => (hσ i).lsubst (Subst.Wf.fromFCFG_append dG).vlift)⟩
  | refl h => exact ⟨h, h⟩
  | rel h => exact toWf h
  | symm _ I => exact I.symm
  | trans _ _ Il Ir => exact ⟨Il.1, Ir.2⟩

theorem Uniform.left {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ L r r'}
  (toWf : ∀{Γ L r r'}, P Γ L r r' → r.Wf Γ L ∧ r'.Wf Γ L)
  (p : (Uniform P Γ L) r r') : r.Wf Γ L
  := (Uniform.wf toWf p).1

theorem Uniform.right {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ L r r'}
  (toWf : ∀{Γ L r r'}, P Γ L r r' → r.Wf Γ L ∧ r'.Wf Γ L)
  (p : (Uniform P Γ L) r r') : r'.Wf Γ L
  := (Uniform.wf toWf p).2

theorem Uniform.wf_iff {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ L r}
  (toWf : ∀{Γ L r r'}, P Γ L r r' → r.Wf Γ L ∧ r'.Wf Γ L)
  : (Uniform P Γ L r r) ↔ r.Wf Γ L := ⟨Uniform.left toWf, Uniform.refl⟩

-- TODO: factor these?

theorem vwk_dinaturality_left {β : Region φ}
  {G : Fin n → Region φ} {σ : Subst φ}
  : (cfg (β.lsubst (σ.extend m n)) n (λi => (G i).lsubst (σ.extend m n).vlift)).vwk ρ
    = (cfg ((β.vwk ρ).lsubst (Subst.extend (vwk (Nat.liftWk ρ) ∘ σ) m n)) n
      (λi => ((G i).vwk (Nat.liftWk ρ)).lsubst
        (Subst.extend (vwk (Nat.liftWk ρ) ∘ σ) m n).vlift)) := by
  simp only [vwk_cfg, vwk_lsubst]
  congr
  · funext ℓ
    simp only [Function.comp_apply, Subst.extend]
    split <;> rfl
  · funext i
    congr
    funext ℓ
    simp only [Function.comp_apply, Subst.extend, Subst.vlift]
    split
    · simp only [vwk1, vwk_vwk]; congr; funext k; cases k <;> rfl
    · rfl

theorem vwk_dinaturality_right {β : Region φ}
  {G : Fin n → Region φ} {σ : Subst φ}
  : (cfg β m
          (λi => (σ i).lsubst (Subst.fromFCFG k G).vlift)).vwk ρ
    = (cfg (β.vwk ρ) m
          (λi => ((σ i).vwk (Nat.liftWk ρ)).lsubst
            (Subst.fromFCFG k (vwk (Nat.liftWk ρ) ∘ G)).vlift)) := by
  simp only [vwk_cfg, vwk_lsubst]
  congr
  funext i
  congr
  funext ℓ
  simp only [Function.comp_apply, Subst.fromFCFG, Subst.vlift]
  split
  · simp only [vwk1, vwk_vwk]; congr; funext k; cases k <;> rfl
  · rfl

theorem Uniform.vwk {P Q : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ Δ L r r'}
  (toVwk : ∀{Γ Δ L ρ r r'}, Γ.Wkn Δ ρ → P Δ L r r' → Q Γ L (r.vwk ρ) (r'.vwk ρ))
  (hρ : Γ.Wkn Δ ρ)
  (p : (Uniform P Δ L) r r') : Uniform Q Γ L (r.vwk ρ) (r'.vwk ρ)
  := by induction p generalizing ρ Γ with
  | rel h => exact rel $ toVwk hρ h
  | symm _ I => exact (I hρ).symm
  | trans _ _ Il Ir => exact (Il hρ).trans (Ir hρ)
  | refl h => exact refl (h.vwk hρ)
  | case_left he _hr hs Ir => exact case_left (he.wk hρ) (Ir hρ.slift) (hs.vwk hρ.slift)
  | case_right he hr _hs Is => exact case_right (he.wk hρ) (hr.vwk hρ.slift) (Is hρ.slift)
  | let1 ha _hr Ir => exact let1 (ha.wk hρ) (Ir hρ.slift)
  | let2 ha _hr Ir => exact let2 (ha.wk hρ) (Ir hρ.sliftn₂)
  | cfg_entry R hR _hβ hG Iβ => exact cfg_entry R hR (Iβ hρ) (λi => (hG i).vwk hρ.slift)
  | cfg_block R hR hβ hG i _h IG' =>
    simp only [Region.vwk, Function.comp_update_apply]
    exact cfg_block R hR (hβ.vwk hρ) (λi => (hG i).vwk hρ.slift) i (IG' hρ.slift)
  | uniform dβ de dr ds _ Ih =>
    rw [vwk_cfg1, vwk_wrseq, vwk_cfg1]
    apply uniform
    · exact dβ.vwk hρ
    · exact de.wk hρ.slift
    · exact dr.vwk hρ.slift
    · exact ds.vwk hρ.slift
    · have Ih := Ih hρ.slift
      simp only [vwk_lift_wseq] at Ih
      exact Ih
  | codiagonal dβ dG =>
    simp only [vwk_cfg1, nil_vwk_lift, lsubst_lsubst0_nil, vwk_lwk]
    rw [<-lsubst_lsubst0_nil]
    have h := codiagonal (P := Q) (dβ.vwk hρ) (dG.vwk hρ.slift)
    convert h using 5
    simp only [vwk1, vwk_vwk]
    congr; funext k; cases k <;> rfl
  | ucfg hR dβ dG =>
    simp only [vwk_cfg, vwk_ucfg']
    exact ucfg hR (dβ.vwk hρ) (λi => (dG i).vwk hρ.slift)
  -- | dinaturality hσ dβ dG =>
  --   rename_i L R R' β G σ
  --   rw [vwk_dinaturality_left, vwk_dinaturality_right]
  --   exact dinaturality
  --     (σ := (Region.vwk (Nat.liftWk ρ)) ∘ σ)
  --     (λi => (hσ i).vwk hρ.slift) (dβ.vwk hρ)
  --     (λi => (dG i).vwk hρ.slift)

theorem Uniform.lwk {P Q : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ L K r r'}
  (toLwk : ∀{Γ L K ρ r r'}, L.Wkn K ρ → P Γ L r r' → Q Γ K (r.lwk ρ) (r'.lwk ρ))
  (hρ : L.Wkn K ρ)
  (p : (Uniform P Γ L) r r') : Uniform Q Γ K (r.lwk ρ) (r'.lwk ρ)
  := by induction p generalizing ρ K with
  | rel h => exact rel $ toLwk hρ h
  | symm _ I => exact (I hρ).symm
  | trans _ _ Il Ir => exact (Il hρ).trans (Ir hρ)
  | refl h => exact refl (h.lwk hρ)
  | case_left de _dr ds Ir => exact case_left de (Ir hρ) (ds.lwk hρ)
  | case_right de dr _ds Is => exact case_right de (dr.lwk hρ) (Is hρ)
  | let1 de _dr Ir => exact let1 de (Ir hρ)
  | let2 de _dr Ir => exact let2 de (Ir hρ)
  | cfg_entry R hR _dβ dG Iβ =>
    exact cfg_entry R hR (Iβ (hR ▸ hρ.liftn_append _)) (λi => (dG i).lwk (hR ▸ hρ.liftn_append _))
  | cfg_block R hR dβ dG i _hG' IG' =>
    simp only [Region.lwk, Function.comp_update_apply]
    exact cfg_block R hR
      (dβ.lwk (hR ▸ hρ.liftn_append _))
      (λi => (dG i).lwk (hR ▸ hρ.liftn_append _)) i
      (IG' (hR ▸ hρ.liftn_append _))
  | uniform dβ de dr ds _ Ih =>
    rw [lwk_cfg1, lwk_lift_wrseq, lwk_cfg1]
    apply uniform
    · exact dβ.lwk hρ.slift
    · exact de
    · exact dr.lwk hρ.slift
    · exact ds.lwk hρ.slift
    · have Ih := Ih hρ.slift
      simp only [lwk_lift_wseq] at Ih
      exact Ih
  | codiagonal hβ hG =>
    convert (codiagonal (hβ.lwk hρ.slift) (hG.lwk hρ.slift.slift)) using 1
    · simp only [BinSyntax.Region.lwk, Nat.liftnWk_one, cfg.injEq, heq_eq_eq, true_and]
      funext i
      cases i using Fin.elim1
      simp only [BinSyntax.Region.lwk, Nat.liftnWk, zero_lt_one, ↓reduceIte, nil, ret, Fin.isValue,
        Fin.elim1_zero, cfg.injEq, heq_eq_eq, true_and]
      funext i
      cases i using Fin.elim1
      simp [lwk_vwk1, Nat.liftnWk_one]
    · simp only [BinSyntax.Region.lwk, Nat.liftnWk_one, cfg.injEq, heq_eq_eq, true_and]
      funext i
      cases i using Fin.elim1
      simp only [Fin.isValue, Fin.elim1_zero, ← lsubst_fromLwk, lsubst_lsubst]
      congr
      funext i; cases i <;> rfl
  | ucfg hR dβ dG =>
    simp only [lwk_cfg, lwk_ucfg']
    exact ucfg hR (dβ.lwk (hR ▸ hρ.liftn_append)) (λi => (dG i).lwk (hR ▸ hρ.liftn_append))
  -- | dinaturality hσ hβ hG =>
  --   rename_i L R R' β G σ
  --   convert dinaturality
  --     (σ := (Region.lwk (Nat.liftnWk R'.length ρ)) ∘ σ)
  --     (λi => sorry)
  --     (hβ.lwk (hρ.liftn_append _))
  --     (λi => (hG i).lwk (hρ.liftn_append _)) using 1
  --   · sorry
  --   · sorry

theorem Uniform.vsubst {P Q : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ Δ L r r'}
  (toVsubst : ∀{Γ Δ L σ r r'}, σ.Wf Γ Δ → P Δ L r r' → Q Γ L (r.vsubst σ) (r'.vsubst σ))
  (hσ : σ.Wf Γ Δ)
  (p : (Uniform P Δ L) r r') : Uniform Q Γ L (r.vsubst σ) (r'.vsubst σ)
  := by induction p generalizing σ Γ with
  | rel h => exact rel $ toVsubst hσ h
  | symm _ I => exact (I hσ).symm
  | trans _ _ Il Ir => exact (Il hσ).trans (Ir hσ)
  | refl h => exact refl (h.vsubst hσ)
  | case_left de _dr ds Ir => exact case_left (de.subst hσ) (Ir hσ.slift) (ds.vsubst hσ.slift)
  | case_right de dr _ds Is => exact case_right (de.subst hσ) (dr.vsubst hσ.slift) (Is hσ.slift)
  | let1 de _dr Ir => exact let1 (de.subst hσ) (Ir hσ.slift)
  | let2 de _dr Ir => exact let2 (de.subst hσ) (Ir hσ.sliftn₂)
  | cfg_entry R hR _dβ dG Iβ =>
    exact cfg_entry R hR (Iβ hσ) (λi => (dG i).vsubst hσ.slift)
  | cfg_block R hR dβ dG i _hG' IG' =>
    simp only [Region.vsubst, Function.comp_update_apply]
    exact cfg_block R hR (dβ.vsubst hσ) (λi => (dG i).vsubst hσ.slift) i (IG' hσ.slift)
  | uniform dβ de dr ds _ Ih =>
    rw [vsubst_cfg1, vsubst_wrseq, vsubst_cfg1]
    apply uniform
    · exact dβ.vsubst hσ
    · exact de.subst hσ.slift
    · exact dr.vsubst hσ.slift
    · exact ds.vsubst hσ.slift
    · have Ih := Ih hσ.slift
      simp only [vsubst_lift_wseq] at Ih
      exact Ih
  | codiagonal hβ hG =>
    convert (codiagonal (hβ.vsubst hσ) (hG.vsubst hσ.slift)) using 1
    · simp only [BinSyntax.Region.vsubst, cfg.injEq, heq_eq_eq, true_and]
      funext i; cases i using Fin.elim1
      simp only [BinSyntax.Region.vsubst, subst, Subst.lift_zero, nil, ret, Fin.isValue,
        Fin.elim1_zero, cfg.injEq, heq_eq_eq, true_and]
      funext i; cases i using Fin.elim1
      simp [vsubst_lift₂_vwk1]
    · simp only [BinSyntax.Region.vsubst, cfg.injEq, heq_eq_eq, true_and]
      funext i; cases i using Fin.elim1
      simp only [Fin.isValue, Fin.elim1_zero, vsubst_lsubst]
      congr
      funext i; cases i <;> rfl
  | ucfg hR dβ dG =>
    simp only [vsubst_cfg, vsubst_ucfg']
    exact ucfg hR (dβ.vsubst hσ) (λi => (dG i).vsubst hσ.slift)
  -- | dinaturality hσ hβ hG =>
  --   sorry

theorem Uniform.lsubst {P Q : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ L K r r'}
  (toLsubst : ∀{Γ L K σ r r'}, σ.Wf Γ L K → P Γ L r r' → Q Γ K (r.lsubst σ) (r'.lsubst σ))
  (hσ : σ.Wf Γ L K)
  (p : (Uniform P Γ L) r r') : Uniform Q Γ K (r.lsubst σ) (r'.lsubst σ)
  := by induction p generalizing σ K with
  | rel h => exact rel $ toLsubst hσ h
  | symm _ I => exact (I hσ).symm
  | trans _ _ Il Ir => exact (Il hσ).trans (Ir hσ)
  | refl h => exact refl (h.lsubst hσ)
  | case_left de _dr ds Ir => exact case_left de (Ir hσ.vlift) (ds.lsubst hσ.vlift)
  | case_right de dr _ds Is => exact case_right de (dr.lsubst hσ.vlift) (Is hσ.vlift)
  | let1 de _dr Ir => exact let1 de (Ir hσ.vlift)
  | let2 de _dr Ir => exact let2 de (Ir hσ.vliftn₂)
  | cfg_entry R hR _dβ dG Iβ =>
    exact cfg_entry R hR
      (Iβ (hσ.liftn_append' hR.symm))
      (λi => (dG i).lsubst (hσ.liftn_append' hR.symm).vlift)
  | cfg_block R hR dβ dG i _hG' IG' =>
    simp only [Region.lsubst, Function.comp_update_apply]
    exact cfg_block R hR
      (dβ.lsubst (hσ.liftn_append' hR.symm))
      (λi => (dG i).lsubst (hσ.liftn_append' hR.symm).vlift) i
      (IG' (hσ.liftn_append' hR.symm).vlift)
  | uniform dβ de dr ds _ Ih =>
    rw [lsubst_cfg1, lsubst_lift_wrseq, lsubst_cfg1]
    apply uniform
    · exact dβ.lsubst hσ.slift
    · exact de
    · exact dr.lsubst hσ.slift.vlift
    · exact ds.lsubst hσ.slift.vlift
    · have Ih := Ih hσ.slift.vlift
      simp only [lsubst_vlift_lift_wseq] at Ih
      exact Ih
  | codiagonal hβ hG =>
    convert codiagonal (hβ.lsubst hσ.slift) (hG.lsubst hσ.vlift.slift.slift) using 1
    · simp only [BinSyntax.Region.lsubst, Subst.liftn_one, cfg.injEq, heq_eq_eq, true_and]
      funext i
      cases i using Fin.elim1
      simp [nil, ret]
      funext i
      cases i using Fin.elim1
      simp only [Subst.liftn_one, ← Subst.vlift_lift_comm, Fin.isValue, Fin.elim1_zero, vwk1_lsubst]
      simp [Subst.vlift, <-Function.comp.assoc, vwk2_comp_vwk1]
    · simp only [BinSyntax.Region.lsubst, Subst.liftn_one, cfg.injEq, heq_eq_eq, true_and]
      funext i
      cases i using Fin.elim1
      simp only [Fin.isValue, Fin.elim1_zero, lsubst_lsubst]
      congr
      funext k; cases k using Nat.cases2 with
      | rest k =>
        simp only [Subst.comp, BinSyntax.Region.lsubst, Subst.vlift, Function.comp_apply,
          Subst.lift, vsubst0_var0_vwk1, lwk_lwk]
        simp only [vwk1_lwk]
        simp only [← lsubst_fromLwk, lsubst_lsubst]
        rfl
      | _ => rfl
  | ucfg hR dβ dG =>
    simp only [lsubst_cfg, lsubst_ucfg']
    exact ucfg hR (dβ.lsubst (hσ.liftn_append' hR.symm))
      (λi => (dG i).lsubst (hσ.liftn_append' hR.symm).vlift)
  -- | dinaturality hσ hβ hG =>
  --   sorry

theorem Uniform.vsubst_flatten {P : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ Δ L r r'}
  (toVsubst : ∀{Γ Δ L σ r r'}, σ.Wf Γ Δ → P Δ L r r' → Uniform P Γ L (r.vsubst σ) (r'.vsubst σ))
  (hσ : σ.Wf Γ Δ)
  (p : (Uniform P Δ L) r r') : Uniform P Γ L (r.vsubst σ) (r'.vsubst σ)
  := (p.vsubst (Q := Uniform P) toVsubst hσ).flatten

def Uniform.Setoid (P : Ctx α ε → LCtx α → Region φ → Region φ → Prop) (Γ : Ctx α ε) (L : LCtx α)
  : Setoid (InS φ Γ L) where
  r x y := Uniform P Γ L x y
  iseqv := {
    refl := λx => Uniform.refl x.prop
    symm := Uniform.symm
    trans := Uniform.trans
  }
