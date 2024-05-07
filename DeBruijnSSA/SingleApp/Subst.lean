import DeBruijnSSA.SingleApp.Typing

namespace SingleApp

section Subst

variable
  [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Zero ε]
  {Γ Δ : Ctx α ε} {σ : Subst φ}

def Subst.WfD (Γ Δ : Ctx α ε) (σ : Subst φ) : Type _
  := ∀i : Fin Δ.length, (σ i).WfD Γ (Δ.get i)

def Subst.WfD.lift (hA : A ≤ A') (hσ : σ.WfD Γ Δ) : σ.lift.WfD (A::Γ) (A'::Δ)
  := λi => i.cases (Term.WfD.var (Ctx.Var.head hA _)) (λi => (hσ i).wk (Ctx.Wkn.id _).step)

def Subst.WfD.lift₂ (hA : A ≤ A') (hB : B ≤ B') (hσ : σ.WfD Γ Δ)
  : σ.lift.lift.WfD (A::B::Γ) (A'::B'::Δ)
  := (hσ.lift hB).lift hA

-- TODO: version with nicer defeq?
def Subst.WfD.liftn₂ (hA : A ≤ A') (hB : B ≤ B') (hσ : σ.WfD Γ Δ)
  : (σ.liftn 2).WfD (A::B::Γ) (A'::B'::Δ)
  := Subst.liftn_eq_iterate_lift 2 ▸ hσ.lift₂ hA hB

def Ctx.Var.subst (hσ : σ.WfD Γ Δ) (h : Δ.Var n V) : (σ n).WfD Γ V
  := (hσ ⟨n, h.length⟩).wk_res h.get

def Term.WfD.subst {a : Term φ} (hσ : σ.WfD Γ Δ) : a.WfD Δ V → (a.subst σ).WfD Γ V
  | var h => Ctx.Var.subst hσ h
  | op df de => op df (de.subst hσ)
  | pair dl dr => pair (dl.subst hσ) (dr.subst hσ)
  | unit e => unit e
  | bool b e => bool b e

def Body.WfD.subst {Γ Δ : Ctx α ε} {σ} {b : Body φ} (hσ : σ.WfD Γ Δ)
  : b.WfD Δ V → (b.subst σ).WfD Γ V
  | nil => nil
  | let1 da dt => let1 (da.subst hσ) (dt.subst (hσ.lift (le_refl _)))
  | let2 da dt => let2 (da.subst hσ) (dt.subst (hσ.liftn₂ (le_refl _) (le_refl _)))

def Terminator.WfD.vsubst {t : Terminator φ} (hσ : σ.WfD Γ Δ) : t.WfD Δ V → (t.vsubst σ).WfD Γ V
  | br hL ha => br hL (ha.subst hσ)
  | ite he hs ht => ite (he.subst hσ) (hs.vsubst hσ) (ht.vsubst hσ)

-- TODO: Block

-- TODO: BBRegion

def TRegion.WfD.vsubst {Γ Δ : Ctx α ε} {σ}  {r : TRegion φ} (hσ : σ.WfD Γ Δ)
  : r.WfD Δ L → (r.vsubst σ).WfD Γ L
  | let1 da dt => let1 (da.subst hσ) (dt.vsubst (hσ.lift (le_refl _)))
  | let2 da dt => let2 (da.subst hσ) (dt.vsubst (hσ.liftn₂ (le_refl _) (le_refl _)))
  | cfg n R hR hr hG => cfg n R hR (hr.vsubst hσ) (λi => (hG i).vsubst (hσ.lift (le_refl _)))

def Region.WfD.vsubst {Γ Δ : Ctx α ε} {σ} {r : Region φ} (hσ : σ.WfD Γ Δ)
  : r.WfD Δ L → (r.vsubst σ).WfD Γ L
  | br hL ha => br hL (ha.subst hσ)
  | ite he hs ht => ite (he.subst hσ) (hs.vsubst hσ) (ht.vsubst hσ)
  | let1 da dt => let1 (da.subst hσ) (dt.vsubst (hσ.lift (le_refl _)))
  | let2 da dt => let2 (da.subst hσ) (dt.vsubst (hσ.liftn₂ (le_refl _) (le_refl _)))
  | cfg n R hR hr hG => cfg n R hR (hr.vsubst hσ) (λi => (hG i).vsubst (hσ.lift (le_refl _)))

end Subst

end SingleApp
