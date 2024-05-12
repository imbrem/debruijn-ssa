import DeBruijnSSA.SingleApp.Typing

namespace SingleApp

section Subst

variable
  [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]
  {Γ Δ : Ctx α ε} {σ : Subst φ}

def Subst.WfD (Γ Δ : Ctx α ε) (σ : Subst φ) : Type _
  := ∀i : Fin Δ.length, (σ i).WfD Γ (Δ.get i)

def Subst.WfD.lift (h : V ≤ V') (hσ : σ.WfD Γ Δ) : σ.lift.WfD (V::Γ) (V'::Δ)
  := λi => i.cases (Term.WfD.var (Ctx.Var.head h _)) (λi => (hσ i).wk (Ctx.Wkn.id _).step)

def Subst.WfD.slift (V) (hσ : σ.WfD Γ Δ) : σ.lift.WfD (V::Γ) (V::Δ)
  := hσ.lift (le_refl V)

def Subst.WfD.lift₂ (h₁ : V₁ ≤ V₁') (h₂ : V₂ ≤ V₂') (hσ : σ.WfD Γ Δ)
  : σ.lift.lift.WfD (V₁::V₂::Γ) (V₁'::V₂'::Δ)
  := (hσ.lift h₂).lift h₁

def Subst.WfD.slift₂ (V₁ V₂) (hσ : σ.WfD Γ Δ) : σ.lift.lift.WfD (V₁::V₂::Γ) (V₁::V₂::Δ)
  := hσ.lift₂ (le_refl _) (le_refl _)

-- TODO: version with nicer defeq?
def Subst.WfD.liftn_append (Ξ : Ctx α ε) (hσ : σ.WfD Γ Δ) : (σ.liftn Ξ.length).WfD (Ξ ++ Γ) (Ξ ++ Δ)
  := match Ξ with
  | [] => by rw [List.nil_append, List.nil_append, List.length_nil, liftn_zero]; exact hσ
  | A::Ξ => by rw [List.length_cons, liftn_succ]; exact (hσ.liftn_append Ξ).slift _

def Subst.WfD.liftn_append_cons (V) (Ξ : Ctx α ε) (hσ : σ.WfD Γ Δ)
  : (σ.liftn (Ξ.length + 1)).WfD (V::(Ξ ++ Γ)) (V::(Ξ ++ Δ))
  := liftn_append (V::Ξ) hσ

-- TODO: version with nicer defeq?
def Subst.WfD.liftn₂ (h₁ : V₁ ≤ V₁') (h₂ : V₂ ≤ V₂') (hσ : σ.WfD Γ Δ)
  : (σ.liftn 2).WfD (V₁::V₂::Γ) (V₁'::V₂'::Δ)
  := Subst.liftn_eq_iterate_lift 2 ▸ hσ.lift₂ h₁ h₂

def Subst.WfD.sliftn₂ (V₁ V₂) (hσ : σ.WfD Γ Δ) : (σ.liftn 2).WfD (V₁::V₂::Γ) (V₁::V₂::Δ)
  := hσ.liftn₂ (le_refl _) (le_refl _)

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
  | let1 da dt => let1 (da.subst hσ) (dt.subst (hσ.slift _))
  | let2 da dt => let2 (da.subst hσ) (dt.subst (hσ.sliftn₂ _ _))

def Terminator.WfD.vsubst {t : Terminator φ} (hσ : σ.WfD Γ Δ) : t.WfD Δ V → (t.vsubst σ).WfD Γ V
  | br hL ha => br hL (ha.subst hσ)
  | ite he hs ht => ite (he.subst hσ) (hs.vsubst hσ) (ht.vsubst hσ)

def Block.WfD.vsubst {b : Block φ} (hσ : σ.WfD Γ Δ) (hb : b.WfD Δ Ξ L) : (b.vsubst σ).WfD Γ Ξ L
  where
  body := hb.body.subst hσ
  terminator := hb.terminator.vsubst (hb.body.num_defs_eq_length ▸ hσ.liftn_append Ξ)

def BBRegion.WfD.vsubst {Γ Δ : Ctx α ε} {σ} {r : BBRegion φ} (hσ : σ.WfD Γ Δ)
  : r.WfD Δ L → (r.vsubst σ).WfD Γ L
  | cfg n R hR hb hG => cfg n R hR (hb.vsubst hσ)
    (λi => (hG i).vsubst (hb.body.num_defs_eq_length ▸ hσ.liftn_append_cons _ _))

def TRegion.WfD.vsubst {Γ Δ : Ctx α ε} {σ}  {r : TRegion φ} (hσ : σ.WfD Γ Δ)
  : r.WfD Δ L → (r.vsubst σ).WfD Γ L
  | let1 da dt => let1 (da.subst hσ) (dt.vsubst (hσ.slift _))
  | let2 da dt => let2 (da.subst hσ) (dt.vsubst (hσ.sliftn₂ _ _))
  | cfg n R hR hr hG => cfg n R hR (hr.vsubst hσ) (λi => (hG i).vsubst (hσ.slift _))

def Region.WfD.vsubst {Γ Δ : Ctx α ε} {σ} {r : Region φ} (hσ : σ.WfD Γ Δ)
  : r.WfD Δ L → (r.vsubst σ).WfD Γ L
  | br hL ha => br hL (ha.subst hσ)
  | ite he hs ht => ite (he.subst hσ) (hs.vsubst hσ) (ht.vsubst hσ)
  | let1 da dt => let1 (da.subst hσ) (dt.vsubst (hσ.slift _))
  | let2 da dt => let2 (da.subst hσ) (dt.vsubst (hσ.sliftn₂ _ _))
  | cfg n R hR hr hG => cfg n R hR (hr.vsubst hσ) (λi => (hG i).vsubst (hσ.slift _))

end Subst

section TSubst

variable
  [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]
  {Γ Δ : Ctx α ε} {σ : TSubst φ}

end TSubst

end SingleApp
