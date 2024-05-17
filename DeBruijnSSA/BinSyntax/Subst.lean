import DeBruijnSSA.BinSyntax.Typing
import DeBruijnSSA.BinSyntax.Syntax.Subst

namespace BinSyntax

section Subst

variable
  [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]
  {Γ Δ : Ctx α ε} {σ : Term.Subst φ}

def Term.Subst.WfD (Γ Δ : Ctx α ε) (σ : Subst φ) : Type _
  := ∀i : Fin Δ.length, (σ i).WfD Γ (Δ.get i)

def Term.Subst.WfD.lift (h : V ≤ V') (hσ : σ.WfD Γ Δ) : σ.lift.WfD (V::Γ) (V'::Δ)
  := λi => i.cases (Term.WfD.var (Ctx.Var.head h _)) (λi => (hσ i).wk (Ctx.Wkn.id _).step)

def Term.Subst.WfD.slift (V) (hσ : σ.WfD Γ Δ) : σ.lift.WfD (V::Γ) (V::Δ)
  := hσ.lift (le_refl V)

def Term.Subst.WfD.lift₂ (h₁ : V₁ ≤ V₁') (h₂ : V₂ ≤ V₂') (hσ : σ.WfD Γ Δ)
  : σ.lift.lift.WfD (V₁::V₂::Γ) (V₁'::V₂'::Δ)
  := (hσ.lift h₂).lift h₁

def Term.Subst.WfD.slift₂ (V₁ V₂) (hσ : σ.WfD Γ Δ) : σ.lift.lift.WfD (V₁::V₂::Γ) (V₁::V₂::Δ)
  := hσ.lift₂ (le_refl _) (le_refl _)

-- TODO: version with nicer defeq?
def Term.Subst.WfD.liftn_append (Ξ : Ctx α ε) (hσ : σ.WfD Γ Δ)
  : (σ.liftn Ξ.length).WfD (Ξ ++ Γ) (Ξ ++ Δ) := match Ξ with
  | [] => by rw [List.nil_append, List.nil_append, List.length_nil, liftn_zero]; exact hσ
  | A::Ξ => by rw [List.length_cons, liftn_succ]; exact (hσ.liftn_append Ξ).slift _

def Term.Subst.WfD.liftn_append' {Ξ : Ctx α ε} (hn : n = Ξ.length) (hσ : σ.WfD Γ Δ)
  : (σ.liftn n).WfD (Ξ ++ Γ) (Ξ ++ Δ)
  := hn ▸ hσ.liftn_append Ξ

def Term.Subst.WfD.liftn_append_cons (V) (Ξ : Ctx α ε) (hσ : σ.WfD Γ Δ)
  : (σ.liftn (Ξ.length + 1)).WfD (V::(Ξ ++ Γ)) (V::(Ξ ++ Δ))
  := liftn_append (V::Ξ) hσ

-- TODO: version with nicer defeq?
def Term.Subst.WfD.liftn₂ (h₁ : V₁ ≤ V₁') (h₂ : V₂ ≤ V₂') (hσ : σ.WfD Γ Δ)
  : (σ.liftn 2).WfD (V₁::V₂::Γ) (V₁'::V₂'::Δ)
  := Subst.liftn_eq_iterate_lift 2 ▸ hσ.lift₂ h₁ h₂

def Term.Subst.WfD.sliftn₂ (V₁ V₂) (hσ : σ.WfD Γ Δ) : (σ.liftn 2).WfD (V₁::V₂::Γ) (V₁::V₂::Δ)
  := hσ.liftn₂ (le_refl _) (le_refl _)

def Ctx.Var.subst (hσ : σ.WfD Γ Δ) (h : Δ.Var n V) : (σ n).WfD Γ V
  := (hσ ⟨n, h.length⟩).wk_res h.get

def Term.WfD.subst {a : Term φ} (hσ : σ.WfD Γ Δ) : a.WfD Δ V → (a.subst σ).WfD Γ V
  | var h => Ctx.Var.subst hσ h
  | op df de => op df (de.subst hσ)
  | pair dl dr => pair (dl.subst hσ) (dr.subst hσ)
  | inl d => inl (d.subst hσ)
  | inr d => inr (d.subst hσ)
  | unit e => unit e

def Term.WfD.subst0 {a : Term φ} (ha : a.WfD Δ V) : a.subst0.WfD Δ (V::Δ)
  := λi => i.cases ha (λi => Term.WfD.var ⟨by simp, by simp⟩)

def Body.WfD.subst {Γ Δ : Ctx α ε} {σ} {b : Body φ} (hσ : σ.WfD Γ Δ)
  : b.WfD Δ V → (b.subst σ).WfD Γ V
  | nil => nil
  | let1 da dt => let1 (da.subst hσ) (dt.subst (hσ.slift _))
  | let2 da dt => let2 (da.subst hσ) (dt.subst (hσ.sliftn₂ _ _))

def Terminator.WfD.vsubst {Γ Δ : Ctx α ε} {σ} {t : Terminator φ} (hσ : σ.WfD Γ Δ)
  : t.WfD Δ V → (t.vsubst σ).WfD Γ V
  | br hL ha => br hL (ha.subst hσ)
  | case he hs ht => case (he.subst hσ) (hs.vsubst (hσ.slift _)) (ht.vsubst (hσ.slift _))

def Block.WfD.vsubst {b : Block φ} (hσ : σ.WfD Γ Δ) (hb : b.WfD Δ Ξ L) : (b.vsubst σ).WfD Γ Ξ L
  where
  body := hb.body.subst hσ
  terminator := hb.terminator.vsubst (hσ.liftn_append'
    (by rw [hb.body.num_defs_eq_length, Ctx.reverse, List.length_reverse]))

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
  | case he hs ht => case (he.subst hσ) (hs.vsubst (hσ.slift _)) (ht.vsubst (hσ.slift _))
  | let1 da dt => let1 (da.subst hσ) (dt.vsubst (hσ.slift _))
  | let2 da dt => let2 (da.subst hσ) (dt.vsubst (hσ.sliftn₂ _ _))
  | cfg n R hR hr hG => cfg n R hR (hr.vsubst hσ) (λi => (hG i).vsubst (hσ.slift _))

end Subst

section TerminatorSubst

variable
  [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [OrderBot ε]
  {Γ Δ : Ctx α ε} {σ : Terminator.Subst φ}

def Terminator.Subst.WfD (Γ : Ctx α ε) (L K : LCtx α) (σ : Terminator.Subst φ) : Type _
  := ∀i : Fin L.length, (σ i).WfD (⟨L.get i, ⊥⟩::Γ) K

def Terminator.Subst.WfD.lift (h : A ≤ A') (hσ : σ.WfD Γ L K) : σ.lift.WfD Γ (A::L) (A'::K)
  := λi => i.cases
    (Terminator.WfD.br ⟨by simp, h⟩ (Term.WfD.var (Ctx.Var.head (le_refl _) _))) -- TODO: factor
    (λi => (hσ i).lwk (LCtx.Wkn.id _).step)

def Terminator.Subst.WfD.slift (A) (hσ : σ.WfD Γ L K) : σ.lift.WfD Γ (A::L) (A::K)
  := hσ.lift (le_refl A)

def Terminator.Subst.WfD.liftn_append (J : LCtx α) (hσ : σ.WfD Γ L K)
  : (σ.liftn J.length).WfD Γ (J ++ L) (J ++ K)
  := match J with
  | [] => by rw [List.nil_append, List.nil_append, List.length_nil, liftn_zero]; exact hσ
  | A::J => by rw [List.length_cons, liftn_succ]; exact (hσ.liftn_append J).slift _

def Terminator.Subst.WfD.vlift (V) (hσ : σ.WfD Γ L K) : σ.vlift.WfD (V::Γ) L K
  := λi => (hσ i).vwk ((Ctx.Wkn.id Γ).step.slift _)

def Terminator.Subst.WfD.vliftn_append (Ξ : Ctx α ε) (hσ : σ.WfD Γ L K)
  : (σ.vliftn Ξ.length).WfD (Ξ ++ Γ) L K
  := λi => (hσ i).vwk (((Ctx.Wkn.id Γ).stepn_append Ξ).slift _)

def Terminator.Subst.WfD.vliftn_append' {Ξ : Ctx α ε} (hn : n = Ξ.length) (hσ : σ.WfD Γ L K)
  : (σ.vliftn n).WfD (Ξ ++ Γ) L K
  := λi => (hσ i).vwk (((Ctx.Wkn.id Γ).stepn_append' hn).slift _)

def LCtx.Trg.subst (hσ : σ.WfD Γ L K) (h : L.Trg n A) : (σ n).WfD (⟨A, ⊥⟩::Γ)  K
  := (hσ ⟨n, h.length⟩).vwk_id ((Ctx.Wkn.id Γ).lift_id (by simp [h.get]))

def LCtx.Trg.subst0
  {a : Term φ} (hσ : σ.WfD Γ L K) (h : L.Trg n A) (ha : a.WfD Γ ⟨A, ⊥⟩)
  : ((σ n).vsubst a.subst0).WfD Γ K
  := (h.subst hσ).vsubst ha.subst0

def Terminator.WfD.lsubst {Γ : Ctx α ε} {σ} {t : Terminator φ} (hσ : σ.WfD Γ L K)
  : t.WfD Γ L → (t.lsubst σ).WfD Γ K
  | br hL ha => hL.subst0 hσ ha
  | case he hs ht => case he (hs.lsubst (hσ.vlift _)) (ht.lsubst (hσ.vlift _))

def Block.WfD.lsubst {b : Block φ} (hσ : σ.WfD Γ L K) (hb : b.WfD Γ Ξ L) : (b.lsubst σ).WfD Γ Ξ K
  where
  body := hb.body
  terminator := hb.terminator.lsubst (hσ.vliftn_append'
    (by rw [hb.body.num_defs_eq_length, Ctx.reverse, List.length_reverse]))

-- def BBRegion.WfD.lsubst {Γ : Ctx α ε} {L} {σ} {r : BBRegion φ} (hσ : σ.WfD Γ L K)
--   : r.WfD Γ L → (r.lsubst σ).WfD Γ K
--   | cfg n R hR hb hG => cfg n R hR (hb.lsubst sorry) (λi => (hG i).lsubst sorry)

end TerminatorSubst

end BinSyntax
