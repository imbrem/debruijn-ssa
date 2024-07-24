import DeBruijnSSA.BinSyntax.Typing.Region.VSubst

namespace BinSyntax

section RegionSubst

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [OrderBot ε]
  {Γ Δ : Ctx α ε} {σ : Region.Subst φ}

def Region.Subst.WfD (Γ : Ctx α ε) (L K : LCtx α) (σ : Region.Subst φ) : Type _
  := ∀i : Fin L.length, (σ i).WfD (⟨L.get i, ⊥⟩::Γ) K

def Region.Subst.Wf (Γ : Ctx α ε) (L K : LCtx α) (σ : Region.Subst φ) : Prop
  := ∀i : Fin L.length, (σ i).Wf (⟨L.get i, ⊥⟩::Γ) K

def Region.Subst.InS (φ) [EffInstSet φ (Ty α) ε] (Γ : Ctx α ε) (L K : LCtx α) : Type _
  := {σ : Region.Subst φ | σ.Wf Γ L K}

def Region.Subst.InS.get (r : Region.Subst.InS φ Γ L K) (i : Fin L.length)
  : Region.InS φ (⟨L.get i, ⊥⟩::Γ) K
  := ⟨r.1 i, r.2 i⟩

instance Region.Subst.InS.instCoeOut {Γ : Ctx α ε} {L K : LCtx α}
  : CoeOut (Region.Subst.InS φ Γ L K) (Region.Subst φ)
  := ⟨λr => r.1⟩

theorem Region.Subst.Wf.nonempty (hσ : σ.Wf Γ L K) : Nonempty (σ.WfD Γ L K)
  := ⟨λi => Classical.choice (hσ i).nonempty⟩

theorem Region.Subst.WfD.toWf (hσ : σ.WfD Γ L K) : σ.Wf Γ L K
  := λi => (hσ i).toWf

theorem Region.Subst.Wf.nonempty_iff : σ.Wf Γ L K ↔ Nonempty (σ.WfD Γ L K)
  := ⟨Region.Subst.Wf.nonempty, λ⟨h⟩ => h.toWf⟩

def Region.Subst.WfD.lift (h : A ≤ A') (hσ : σ.WfD Γ L K) : σ.lift.WfD Γ (A::L) (A'::K)
  := λi => i.cases
    (Region.WfD.br ⟨by simp, h⟩ (Term.WfD.var (Ctx.Var.head (le_refl _) _))) -- TODO: factor
    (λi => (hσ i).lwk (LCtx.Wkn.id _).step)

theorem Region.Subst.Wf.lift (h : A ≤ A') (hσ : σ.Wf Γ L K) : σ.lift.Wf Γ (A::L) (A'::K)
  := λi => i.cases
    (Region.Wf.br ⟨by simp, h⟩ (Term.Wf.var (Ctx.Var.head (le_refl _) _))) -- TODO: factor
    (λi => (hσ i).lwk (LCtx.Wkn.id _).step)

def Region.Subst.InS.lift (h : A ≤ A') (σ : Region.Subst.InS φ Γ L K)
  : Region.Subst.InS φ Γ (A::L) (A'::K)
  := ⟨Subst.lift σ, σ.prop.lift h⟩

@[simp]
theorem Region.Subst.InS.coe_lift (h : A ≤ A') (σ : Region.Subst.InS φ Γ L K)
  : (σ.lift h : Region.Subst φ) = (σ : Region.Subst φ).lift
  := rfl

def Region.Subst.WfD.slift (A) (hσ : σ.WfD Γ L K) : σ.lift.WfD Γ (A::L) (A::K)
  := hσ.lift (le_refl A)

-- @[simp]
-- theorem Region.Subst.InS.coe_slift (σ : Region.Subst.InS φ Γ L K)
--   : (σ.slift : Region.Subst φ) = (σ : Region.Subst φ).slift A
--   := rfl

def Region.Subst.WfD.liftn_append (J : LCtx α) (hσ : σ.WfD Γ L K)
  : (σ.liftn J.length).WfD Γ (J ++ L) (J ++ K)
  := match J with
  | [] => by rw [List.nil_append, List.nil_append, List.length_nil, liftn_zero]; exact hσ
  | A::J => by rw [List.length_cons, liftn_succ]; exact (hσ.liftn_append J).slift _

def Region.Subst.WfD.liftn_append' {J : LCtx α} (hn : n = J.length) (hσ : σ.WfD Γ L K)
  : (σ.liftn n).WfD Γ (J ++ L) (J ++ K)
  := hn ▸ hσ.liftn_append J

def Region.Subst.WfD.liftn_append_cons (V : Ty α) (J : LCtx α) (hσ : σ.WfD Γ L K)
  : (σ.liftn (J.length + 1)).WfD Γ (V::(J ++ L)) (V::(J ++ K))
  := liftn_append (V::J) hσ

def Region.Subst.WfD.liftn_append_cons' (V : Ty α) {J : LCtx α} (hn : n = J.length + 1) (hσ : σ.WfD Γ L K)
  : (σ.liftn n).WfD Γ (V::(J ++ L)) (V::(J ++ K))
  := hn ▸ hσ.liftn_append_cons V J

def Region.Subst.WfD.vlift (hσ : σ.WfD Γ L K) : σ.vlift.WfD (head::Γ) L K
  := λi => (hσ i).vwk (Ctx.Wkn.id.step.slift)

theorem Region.Subst.Wf.vlift (hσ : σ.Wf Γ L K) : σ.vlift.Wf (head::Γ) L K
  := λi => (hσ i).vwk (Ctx.Wkn.id.step.slift)

def Region.Subst.InS.vlift (σ : Region.Subst.InS φ Γ L K) : InS φ (head::Γ) L K
  := ⟨Subst.vlift σ, σ.prop.vlift⟩

def Region.Subst.WfD.vlift₂ (hσ : σ.WfD Γ L K) : σ.vlift.vlift.WfD (left::right::Γ) L K
  := hσ.vlift.vlift

def Region.Subst.WfD.vliftn₂ (hσ : σ.WfD Γ L K) : (σ.vliftn 2).WfD (left::right::Γ) L K
  := Region.Subst.vliftn_eq_iterate_vlift 2 ▸ hσ.vlift₂

theorem Region.Subst.Wf.vliftn₂ (hσ : σ.Wf Γ L K) : (σ.vliftn 2).Wf (left::right::Γ) L K
  := let ⟨d⟩ := hσ.nonempty; (d.vliftn₂).toWf

def Region.Subst.InS.vliftn₂ (σ : Region.Subst.InS φ Γ L K) : InS φ (left::right::Γ) L K
  := ⟨Subst.vliftn 2 σ, σ.prop.vliftn₂⟩

theorem Region.Subst.InS.vliftn₂_eq_vlift_vlift (σ : Region.Subst.InS φ Γ L K)
  : σ.vliftn₂ (left := left) (right := right) = σ.vlift.vlift
  := by simp [vliftn₂, vlift, vliftn_succ]

def Region.Subst.WfD.vliftn_append (Ξ : Ctx α ε) (hσ : σ.WfD Γ L K)
  : (σ.vliftn Ξ.length).WfD (Ξ ++ Γ) L K
  := λi => (hσ i).vwk (Ctx.Wkn.id.stepn_append Ξ).slift

def Region.Subst.WfD.vliftn_append' {Ξ : Ctx α ε} (hn : n = Ξ.length) (hσ : σ.WfD Γ L K)
  : (σ.vliftn n).WfD (Ξ ++ Γ) L K
  := λi => (hσ i).vwk ((Ctx.Wkn.id.stepn_append' hn).slift)

def Region.Subst.WfD.vliftn_append_cons (V) (Ξ : Ctx α ε) (hσ : σ.WfD Γ L K)
  : (σ.vliftn (Ξ.length + 1)).WfD (V::(Ξ ++ Γ)) L K
  := vliftn_append (V::Ξ) hσ

def Region.Subst.WfD.vliftn_append_cons' (V) {Ξ : Ctx α ε} (hn : n = Ξ.length + 1) (hσ : σ.WfD Γ L K)
  : (σ.vliftn n).WfD (V::(Ξ ++ Γ)) L K
  := hn ▸ hσ.vliftn_append_cons V Ξ

def LCtx.Trg.rsubst (hσ : σ.WfD Γ L K) (h : L.Trg n A) : (σ n).WfD (⟨A, ⊥⟩::Γ)  K
  := (hσ ⟨n, h.length⟩).vwk_id (Ctx.Wkn.id.lift_id (by
    simp only [List.get_eq_getElem, Prod.mk_le_mk, le_refl, and_true]
    exact h.get
    ))

def LCtx.Trg.rsubst0
  {a : Term φ} (hσ : σ.WfD Γ L K) (h : L.Trg n A) (ha : a.WfD Γ ⟨A, ⊥⟩)
  : ((σ n).vsubst a.subst0).WfD Γ K
  := (h.rsubst hσ).vsubst ha.subst0

def Region.WfD.lsubst {Γ : Ctx α ε} {L} {σ} {r : Region φ} (hσ : σ.WfD Γ L K)
  : r.WfD Γ L → (r.lsubst σ).WfD Γ K
  | br hL ha => hL.rsubst0 hσ ha
  | case he hs ht => case he (hs.lsubst hσ.vlift) (ht.lsubst hσ.vlift)
  | let1 da dt => let1 da (dt.lsubst hσ.vlift)
  | let2 da dt => let2 da (dt.lsubst hσ.vliftn₂)
  | cfg n R hR hr hG => cfg n R hR
    (hr.lsubst (hσ.liftn_append' hR.symm))
    (λi => (hG i).lsubst (hσ.liftn_append' hR.symm).vlift)

theorem Region.Wf.lsubst {Γ : Ctx α ε} {L} {σ} {r : Region φ} (hσ : σ.Wf Γ L K) (h : r.Wf Γ L)
  : (r.lsubst σ).Wf Γ K
  := let ⟨d⟩ := h.nonempty; let ⟨hσ⟩ := hσ.nonempty; (d.lsubst hσ).toWf

def Region.InS.lsubst {Γ : Ctx α ε} (σ : Region.Subst.InS φ Γ L K) (r : InS φ Γ L) : InS φ Γ K
  := ⟨(r : Region φ).lsubst σ, r.prop.lsubst σ.prop⟩

@[simp]
theorem Region.InS.coe_lsubst {Γ : Ctx α ε} (σ : Region.Subst.InS φ Γ L K) (r : InS φ Γ L)
  : (r.lsubst σ : Region φ) = (r : Region φ).lsubst σ
  := rfl

def Region.Subst.WfD.comp {Γ : Ctx α ε} {σ : Region.Subst φ} {τ : Region.Subst φ}
  (hσ : σ.WfD Γ K J) (hτ : τ.WfD Γ L K) : (σ.comp τ).WfD Γ L J
  := λi => (hτ i).lsubst hσ.vlift

theorem Region.Subst.Wf.comp {Γ : Ctx α ε} {σ : Region.Subst φ} {τ : Region.Subst φ}
  (hσ : σ.Wf Γ K J) (hτ : τ.Wf Γ L K) : (σ.comp τ).Wf Γ L J
  := λi => (hτ i).lsubst hσ.vlift

end RegionSubst

end BinSyntax
