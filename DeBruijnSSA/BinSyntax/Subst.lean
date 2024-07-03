import DeBruijnSSA.BinSyntax.Typing
import DeBruijnSSA.BinSyntax.Syntax.Subst

namespace BinSyntax

section Subst

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]
  {Γ Δ : Ctx α ε} {σ : Term.Subst φ}

def Term.Subst.WfD (Γ Δ : Ctx α ε) (σ : Subst φ) : Type _
  := ∀i : Fin Δ.length, (σ i).WfD Γ (Δ.get i)

def Term.Subst.Wf (Γ Δ : Ctx α ε) (σ : Subst φ) : Prop
  := ∀i : Fin Δ.length, (σ i).Wf Γ (Δ.get i)

def Term.Subst.InS (φ) [EffInstSet φ (Ty α) ε] (Γ Δ : Ctx α ε) : Type _ := {σ : Subst φ | σ.Wf Γ Δ}

instance Term.Subst.InS.instCoeOut {Γ Δ : Ctx α ε} : CoeOut (Term.Subst.InS φ Γ Δ) (Subst φ)
  := ⟨λr => r.1⟩

theorem Term.Subst.InS.eq_of_coe_eq {σ τ : Term.Subst.InS φ Γ Δ} (h : (σ : Subst φ) = τ) : σ = τ
  := by cases σ; cases τ; cases h; rfl

instance Term.Subst.InS.instSetoid {Γ Δ : Ctx α ε} : Setoid (Term.Subst.InS φ Γ Δ) where
  r σ τ := ∀i, i < Δ.length → σ.val i = τ.val i
  iseqv := {
    refl := (λ_ _ _ => rfl)
    symm := (λh _ hi => (h _ hi).symm)
    trans := (λhl hr _ hi => (hl _ hi).trans (hr _ hi))
  }

theorem Term.Subst.Wf.nonempty (hσ : σ.Wf Γ Δ) : Nonempty (σ.WfD Γ Δ)
  := ⟨λi => Classical.choice (hσ i).nonempty⟩

theorem Term.Subst.WfD.toWf (hσ : σ.WfD Γ Δ) : σ.Wf Γ Δ
  := λi => (hσ i).toWf

theorem Term.Subst.Wf.nonempty_iff : σ.Wf Γ Δ ↔ Nonempty (σ.WfD Γ Δ)
  := ⟨Term.Subst.Wf.nonempty, λ⟨h⟩ => h.toWf⟩

def Term.Subst.WfD.lift (h : V ≤ V') (hσ : σ.WfD Γ Δ) : σ.lift.WfD (V::Γ) (V'::Δ)
  := λi => i.cases (Term.WfD.var (Ctx.Var.head h _)) (λi => (hσ i).wk Ctx.Wkn.id.step)

theorem Term.Subst.Wf.lift (h : V ≤ V') (hσ : σ.Wf Γ Δ) : σ.lift.Wf (V::Γ) (V'::Δ)
  := λi => i.cases (Term.Wf.var (Ctx.Var.head h _)) (λi => (hσ i).wk Ctx.Wkn.id.step)

def Term.Subst.InS.lift (h : V ≤ V') (σ : InS φ Γ Δ) : InS φ (V::Γ) (V'::Δ)
  := ⟨Subst.lift σ, σ.prop.lift h⟩

@[simp]
theorem Term.Subst.coe_lift {h : V ≤ V'} {σ : InS φ Γ Δ}
  : (σ.lift h : Subst φ) = Subst.lift σ
  := rfl

def Term.Subst.WfD.slift {head} (hσ : σ.WfD Γ Δ) : σ.lift.WfD (head::Γ) (head::Δ)
  := hσ.lift (le_refl head)

theorem Term.Subst.Wf.slift {head} (hσ : σ.Wf Γ Δ) : σ.lift.Wf (head::Γ) (head::Δ)
  := hσ.lift (le_refl head)

def Term.Subst.WfD.lift₂ (h₁ : V₁ ≤ V₁') (h₂ : V₂ ≤ V₂') (hσ : σ.WfD Γ Δ)
  : σ.lift.lift.WfD (V₁::V₂::Γ) (V₁'::V₂'::Δ)
  := (hσ.lift h₂).lift h₁

theorem Term.Subst.Wf.lift₂ (h₁ : V₁ ≤ V₁') (h₂ : V₂ ≤ V₂') (hσ : σ.Wf Γ Δ)
  : σ.lift.lift.Wf (V₁::V₂::Γ) (V₁'::V₂'::Δ)
  := (hσ.lift h₂).lift h₁

def Term.Subst.WfD.slift₂ {left right} (hσ : σ.WfD Γ Δ)
  : σ.lift.lift.WfD (left::right::Γ) (left::right::Δ)
  := hσ.lift₂ (le_refl _) (le_refl _)

theorem Term.Subst.Wf.slift₂ {left right} (hσ : σ.Wf Γ Δ)
  : σ.lift.lift.Wf (left::right::Γ) (left::right::Δ)
  := hσ.lift₂ (le_refl _) (le_refl _)

-- TODO: version with nicer defeq?
def Term.Subst.WfD.liftn_append (Ξ : Ctx α ε) (hσ : σ.WfD Γ Δ)
  : (σ.liftn Ξ.length).WfD (Ξ ++ Γ) (Ξ ++ Δ) := match Ξ with
  | [] => by rw [List.nil_append, List.nil_append, List.length_nil, liftn_zero]; exact hσ
  | A::Ξ => by rw [List.length_cons, liftn_succ]; exact (hσ.liftn_append Ξ).slift

theorem Term.Subst.Wf.liftn_append (Ξ : Ctx α ε) (hσ : σ.Wf Γ Δ)
  : (σ.liftn Ξ.length).Wf (Ξ ++ Γ) (Ξ ++ Δ) := match Ξ with
  | [] => by rw [List.nil_append, List.nil_append, List.length_nil, liftn_zero]; exact hσ
  | A::Ξ => by rw [List.length_cons, liftn_succ]; exact (hσ.liftn_append Ξ).slift

def Term.Subst.WfD.liftn_append' {Ξ : Ctx α ε} (hn : n = Ξ.length) (hσ : σ.WfD Γ Δ)
  : (σ.liftn n).WfD (Ξ ++ Γ) (Ξ ++ Δ)
  := hn ▸ hσ.liftn_append Ξ

theorem Term.Subst.Wf.liftn_append' {Ξ : Ctx α ε} (hn : n = Ξ.length) (hσ : σ.Wf Γ Δ)
  : (σ.liftn n).Wf (Ξ ++ Γ) (Ξ ++ Δ)
  := hn ▸ hσ.liftn_append Ξ

def Term.Subst.WfD.liftn_append_cons (V) (Ξ : Ctx α ε) (hσ : σ.WfD Γ Δ)
  : (σ.liftn (Ξ.length + 1)).WfD (V::(Ξ ++ Γ)) (V::(Ξ ++ Δ))
  := liftn_append (V::Ξ) hσ

theorem Term.Subst.Wf.liftn_append_cons (V) (Ξ : Ctx α ε) (hσ : σ.Wf Γ Δ)
  : (σ.liftn (Ξ.length + 1)).Wf (V::(Ξ ++ Γ)) (V::(Ξ ++ Δ))
  := liftn_append (V::Ξ) hσ

def Term.Subst.WfD.liftn_append_cons' (V) {Ξ : Ctx α ε} (hn : n = Ξ.length + 1) (hσ : σ.WfD Γ Δ)
  : (σ.liftn n).WfD (V::(Ξ ++ Γ)) (V::(Ξ ++ Δ))
  := hn ▸ hσ.liftn_append_cons V Ξ

theorem Term.Subst.Wf.liftn_append_cons' (V) {Ξ : Ctx α ε} (hn : n = Ξ.length + 1) (hσ : σ.Wf Γ Δ)
  : (σ.liftn n).Wf (V::(Ξ ++ Γ)) (V::(Ξ ++ Δ))
  := hn ▸ hσ.liftn_append_cons V Ξ

-- TODO: version with nicer defeq?
def Term.Subst.WfD.liftn₂ (h₁ : V₁ ≤ V₁') (h₂ : V₂ ≤ V₂') (hσ : σ.WfD Γ Δ)
  : (σ.liftn 2).WfD (V₁::V₂::Γ) (V₁'::V₂'::Δ)
  := Subst.liftn_eq_iterate_lift 2 ▸ hσ.lift₂ h₁ h₂

theorem Term.Subst.Wf.liftn₂ (h₁ : V₁ ≤ V₁') (h₂ : V₂ ≤ V₂') (hσ : σ.Wf Γ Δ)
  : (σ.liftn 2).Wf (V₁::V₂::Γ) (V₁'::V₂'::Δ)
  := Subst.liftn_eq_iterate_lift 2 ▸ hσ.lift₂ h₁ h₂

def Term.Subst.WfD.sliftn₂ {left right} (hσ : σ.WfD Γ Δ)
  : (σ.liftn 2).WfD (left::right::Γ) (left::right::Δ)
  := hσ.liftn₂ (le_refl _) (le_refl _)

theorem Term.Subst.Wf.sliftn₂ {left right} (hσ : σ.Wf Γ Δ)
  : (σ.liftn 2).Wf (left::right::Γ) (left::right::Δ)
  := hσ.liftn₂ (le_refl _) (le_refl _)

def Ctx.Var.subst (hσ : σ.WfD Γ Δ) (h : Δ.Var n V) : (σ n).WfD Γ V
  := (hσ ⟨n, h.length⟩).wk_res h.get

theorem Ctx.Var.subst' (hσ : σ.Wf Γ Δ) (h : Δ.Var n V) : (σ n).Wf Γ V
  := (hσ ⟨n, h.length⟩).wk_res h.get

def Term.WfD.subst {a : Term φ} (hσ : σ.WfD Γ Δ) : a.WfD Δ V → (a.subst σ).WfD Γ V
  | var h => Ctx.Var.subst hσ h
  | op df de => op df (de.subst hσ)
  | pair dl dr => pair (dl.subst hσ) (dr.subst hσ)
  | inl d => inl (d.subst hσ)
  | inr d => inr (d.subst hσ)
  | abort d => abort (d.subst hσ)
  | unit e => unit e

theorem Term.Wf.subst {a : Term φ} (hσ : σ.Wf Γ Δ) (h : a.Wf Δ V) : (a.subst σ).Wf Γ V
  := let ⟨d⟩ := h.nonempty; let ⟨hσ⟩ := hσ.nonempty; (d.subst hσ).toWf

def Term.InS.subst (σ : Subst.InS φ Γ Δ) (a : InS φ Δ V) : InS φ Γ V
  := ⟨(a : Term φ).subst σ, a.prop.subst σ.prop⟩

@[simp]
theorem Term.InS.coe_subst {σ : Subst.InS φ Γ Δ} {a : InS φ Δ V}
  : (a.subst σ : Term φ) = (a : Term φ).subst σ
  := rfl

theorem Term.InS.subst_equiv {σ τ : Subst.InS φ Γ Δ} (a : InS φ Δ V)
  (h : σ ≈ τ) : a.subst σ = a.subst τ
  := sorry

def Term.WfD.subst0 {a : Term φ} (ha : a.WfD Δ V) : a.subst0.WfD Δ (V::Δ)
  := λi => i.cases ha (λi => Term.WfD.var ⟨by simp, by simp⟩)

theorem Term.Wf.subst0 {a : Term φ} (ha : a.Wf Δ V) : a.subst0.Wf Δ (V::Δ)
  := λi => i.cases ha (λi => Term.Wf.var ⟨by simp, by simp⟩)

def Term.InS.subst0 (a : InS φ Γ V) : Subst.InS φ Γ (V::Γ)
  := ⟨(a : Term φ).subst0, a.prop.subst0⟩

@[simp]
theorem Term.InS.coe_subst0 {a : InS φ Γ V}
  : (a.subst0 : Subst φ) = (a : Term φ).subst0
  := rfl

def Term.Subst.WfD.comp {Γ Δ Ξ : Ctx α ε} {σ : Term.Subst φ} {τ : Term.Subst φ}
  (hσ : σ.WfD Γ Δ) (hτ : τ.WfD Δ Ξ) : (σ.comp τ).WfD Γ Ξ
  := λi => (hτ i).subst hσ

theorem Term.Subst.Wf.comp {Γ Δ Ξ : Ctx α ε} {σ : Term.Subst φ} {τ : Term.Subst φ}
  (hσ : σ.Wf Γ Δ) (hτ : τ.Wf Δ Ξ) : (σ.comp τ).Wf Γ Ξ
  := λi => (hτ i).subst hσ

def Term.Subst.InS.comp {Γ Δ Ξ : Ctx α ε} (σ : Term.Subst.InS φ Γ Δ) (τ : Term.Subst.InS φ Δ Ξ)
  : Term.Subst.InS φ Γ Ξ
  := ⟨Subst.comp σ τ, σ.prop.comp τ.prop⟩

@[simp]
theorem Term.Subst.InS.coe_comp {Γ Δ Ξ : Ctx α ε}
  {σ : Term.Subst.InS φ Γ Δ} {τ : Term.Subst.InS φ Δ Ξ}
  : (σ.comp τ : Subst φ) = Subst.comp σ τ
  := rfl

theorem Term.InS.subst_subst {Γ Δ Ξ : Ctx α ε} {σ : Term.Subst.InS φ Γ Δ} {τ : Term.Subst.InS φ Δ Ξ}
  (a : InS φ Ξ V) : (a.subst τ).subst σ = a.subst (σ.comp τ)
  := by ext; simp [Term.subst_subst]

-- TODO: Term.Subst.InS.comp_id, id_comp ==> this is a category!

theorem Term.Subst.InS.comp_assoc {Γ Δ Ξ Ω : Ctx α ε}
  {σ : Term.Subst.InS φ Γ Δ} {τ : Term.Subst.InS φ Δ Ξ} {υ : Term.Subst.InS φ Ξ Ω}
  : (σ.comp τ).comp υ = σ.comp (τ.comp υ)
  := by apply eq_of_coe_eq; simp [Subst.comp_assoc]

def Body.WfD.subst {Γ Δ : Ctx α ε} {σ} {b : Body φ} (hσ : σ.WfD Γ Δ)
  : b.WfD Δ V → (b.subst σ).WfD Γ V
  | nil => nil
  | let1 da dt => let1 (da.subst hσ) (dt.subst hσ.slift)
  | let2 da dt => let2 (da.subst hσ) (dt.subst hσ.sliftn₂)

def Terminator.WfD.vsubst {Γ Δ : Ctx α ε} {σ} {t : Terminator φ} (hσ : σ.WfD Γ Δ)
  : t.WfD Δ V → (t.vsubst σ).WfD Γ V
  | br hL ha => br hL (ha.subst hσ)
  | case he hs ht => case (he.subst hσ) (hs.vsubst hσ.slift) (ht.vsubst hσ.slift)

def Block.WfD.vsubst {b : Block φ} (hσ : σ.WfD Γ Δ) (hb : b.WfD Δ Ξ L) : (b.vsubst σ).WfD Γ Ξ L
  where
  body := hb.body.subst hσ
  terminator := hb.terminator.vsubst (hσ.liftn_append'
    (by rw [hb.body.num_defs_eq_length, Ctx.reverse, List.length_reverse]))

def BBRegion.WfD.vsubst {Γ Δ : Ctx α ε} {σ} {r : BBRegion φ} (hσ : σ.WfD Γ Δ)
  : r.WfD Δ L → (r.vsubst σ).WfD Γ L
  | cfg n R hR hb hG => cfg n R hR (hb.vsubst hσ)
    (λi => (hG i).vsubst (hσ.liftn_append_cons' _ (by rw [hb.body.num_defs_eq_length])))

def TRegion.WfD.vsubst {Γ Δ : Ctx α ε} {σ}  {r : TRegion φ} (hσ : σ.WfD Γ Δ)
  : r.WfD Δ L → (r.vsubst σ).WfD Γ L
  | let1 da dt => let1 (da.subst hσ) (dt.vsubst hσ.slift)
  | let2 da dt => let2 (da.subst hσ) (dt.vsubst hσ.sliftn₂)
  | cfg n R hR hr hG => cfg n R hR (hr.vsubst hσ) (λi => (hG i).vsubst hσ.slift)

def Region.WfD.vsubst {Γ Δ : Ctx α ε} {σ} {r : Region φ} (hσ : σ.WfD Γ Δ)
  : r.WfD Δ L → (r.vsubst σ).WfD Γ L
  | br hL ha => br hL (ha.subst hσ)
  | case he hs ht => case (he.subst hσ) (hs.vsubst hσ.slift) (ht.vsubst hσ.slift)
  | let1 da dt => let1 (da.subst hσ) (dt.vsubst hσ.slift)
  | let2 da dt => let2 (da.subst hσ) (dt.vsubst hσ.sliftn₂)
  | cfg n R hR hr hG => cfg n R hR (hr.vsubst hσ) (λi => (hG i).vsubst hσ.slift)

theorem Region.Wf.vsubst {Γ Δ : Ctx α ε} {σ} {r : Region φ} (hσ : σ.Wf Γ Δ) (h : r.Wf Δ L)
  : (r.vsubst σ).Wf Γ L
  := let ⟨d⟩ := h.nonempty; let ⟨hσ⟩ := hσ.nonempty; (d.vsubst hσ).toWf

def Region.InS.vsubst {Γ Δ : Ctx α ε} (σ : Term.Subst.InS φ Γ Δ) (r : InS φ Δ L) : InS φ Γ L
  := ⟨(r : Region φ).vsubst σ, r.prop.vsubst σ.prop⟩

@[simp]
theorem Region.InS.coe_vsubst {Γ Δ : Ctx α ε} {σ : Term.Subst.InS φ Γ Δ} {r : InS φ Δ L}
  : (r.vsubst σ : Region φ) = (r : Region φ).vsubst σ
  := rfl

theorem Region.InS.vsubst_equiv {Γ Δ : Ctx α ε} {σ τ : Term.Subst.InS φ Γ Δ}
  (r : InS φ Δ L) (h : σ ≈ τ) : r.vsubst σ = r.vsubst τ
  := sorry

end Subst

section TerminatorSubst

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [OrderBot ε]
  {Γ Δ : Ctx α ε} {σ : Terminator.Subst φ}

def Terminator.Subst.WfD (Γ : Ctx α ε) (L K : LCtx α) (σ : Terminator.Subst φ) : Type _
  := ∀i : Fin L.length, (σ i).WfD (⟨L.get i, ⊥⟩::Γ) K

def Terminator.Subst.WfD.lift (h : A ≤ A') (hσ : σ.WfD Γ L K) : σ.lift.WfD Γ (A::L) (A'::K)
  := λi => i.cases
    (Terminator.WfD.br ⟨by simp, h⟩ (Term.WfD.var (Ctx.Var.head (le_refl _) _))) -- TODO: factor
    (λi => (hσ i).lwk (LCtx.Wkn.id _).step)

def Terminator.Subst.WfD.slift {head} (hσ : σ.WfD Γ L K) : σ.lift.WfD Γ (head::L) (head::K)
  := hσ.lift (le_refl head)

def Terminator.Subst.WfD.liftn_append (J : LCtx α) (hσ : σ.WfD Γ L K)
  : (σ.liftn J.length).WfD Γ (J ++ L) (J ++ K)
  := match J with
  | [] => by rw [List.nil_append, List.nil_append, List.length_nil, liftn_zero]; exact hσ
  | A::J => by rw [List.length_cons, liftn_succ]; exact (hσ.liftn_append J).slift

def Terminator.Subst.WfD.liftn_append' {J : LCtx α} (hn : n = J.length) (hσ : σ.WfD Γ L K)
  : (σ.liftn n).WfD Γ (J ++ L) (J ++ K)
  := hn ▸ hσ.liftn_append J

def Terminator.Subst.WfD.liftn_append_cons (V : Ty α) (J : LCtx α) (hσ : σ.WfD Γ L K)
  : (σ.liftn (J.length + 1)).WfD Γ (V::(J ++ L)) (V::(J ++ K))
  := liftn_append (V::J) hσ

def Terminator.Subst.WfD.liftn_append_cons' (V : Ty α) {J : LCtx α} (hn : n = J.length + 1) (hσ : σ.WfD Γ L K)
  : (σ.liftn n).WfD Γ (V::(J ++ L)) (V::(J ++ K))
  := hn ▸ hσ.liftn_append_cons V J

def Terminator.Subst.WfD.vlift {head} (hσ : σ.WfD Γ L K) : σ.vlift.WfD (head::Γ) L K
  := λi => (hσ i).vwk Ctx.Wkn.wk1

def Terminator.Subst.WfD.vlift₂ {left right} (hσ : σ.WfD Γ L K)
  : σ.vlift.vlift.WfD (left::right::Γ) L K
  := hσ.vlift.vlift

def Terminator.Subst.WfD.vliftn₂ {left right} (hσ : σ.WfD Γ L K)
  : (σ.vliftn 2).WfD (left::right::Γ) L K
  := Terminator.Subst.vliftn_eq_iterate_vlift 2 ▸ hσ.vlift₂

def Terminator.Subst.WfD.vliftn_append (Ξ : Ctx α ε) (hσ : σ.WfD Γ L K)
  : (σ.vliftn Ξ.length).WfD (Ξ ++ Γ) L K
  := λi => (hσ i).vwk (Ctx.Wkn.id.stepn_append Ξ).slift

def Terminator.Subst.WfD.vliftn_append' {Ξ : Ctx α ε} (hn : n = Ξ.length) (hσ : σ.WfD Γ L K)
  : (σ.vliftn n).WfD (Ξ ++ Γ) L K
  := λi => (hσ i).vwk (Ctx.Wkn.id.stepn_append' hn).slift

def Terminator.Subst.WfD.vliftn_append_cons (V) (Ξ : Ctx α ε) (hσ : σ.WfD Γ L K)
  : (σ.vliftn (Ξ.length + 1)).WfD (V::(Ξ ++ Γ)) L K
  := vliftn_append (V::Ξ) hσ

def Terminator.Subst.WfD.vliftn_append_cons' (V) {Ξ : Ctx α ε} (hn : n = Ξ.length + 1) (hσ : σ.WfD Γ L K)
  : (σ.vliftn n).WfD (V::(Ξ ++ Γ)) L K
  := hn ▸ hσ.vliftn_append_cons V Ξ

def LCtx.Trg.subst (hσ : σ.WfD Γ L K) (h : L.Trg n A) : (σ n).WfD (⟨A, ⊥⟩::Γ)  K
  := (hσ ⟨n, h.length⟩).vwk_id (Ctx.Wkn.id.lift_id (by
    simp only [List.get_eq_getElem, Prod.mk_le_mk, le_refl, and_true]
    exact h.get
  ))

def LCtx.Trg.subst0
  {a : Term φ} (hσ : σ.WfD Γ L K) (h : L.Trg n A) (ha : a.WfD Γ ⟨A, ⊥⟩)
  : ((σ n).vsubst a.subst0).WfD Γ K
  := (h.subst hσ).vsubst ha.subst0

def Terminator.WfD.lsubst {Γ : Ctx α ε} {σ} {t : Terminator φ} (hσ : σ.WfD Γ L K)
  : t.WfD Γ L → (t.lsubst σ).WfD Γ K
  | br hL ha => hL.subst0 hσ ha
  | case he hs ht => case he (hs.lsubst hσ.vlift) (ht.lsubst hσ.vlift)

def Terminator.Subst.WfD.comp {Γ : Ctx α ε} {σ : Terminator.Subst φ} {τ : Terminator.Subst φ}
  (hσ : σ.WfD Γ K J) (hτ : τ.WfD Γ L K) : (σ.comp τ).WfD Γ L J
  := λi => (hτ i).lsubst hσ.vlift

def Block.WfD.lsubst {b : Block φ} (hσ : σ.WfD Γ L K) (hb : b.WfD Γ Ξ L) : (b.lsubst σ).WfD Γ Ξ K
  where
  body := hb.body
  terminator := hb.terminator.lsubst (hσ.vliftn_append'
    (by rw [hb.body.num_defs_eq_length, Ctx.reverse, List.length_reverse]))

def BBRegion.WfD.lsubst {Γ : Ctx α ε} {L} {σ} {r : BBRegion φ} (hσ : σ.WfD Γ L K)
  : r.WfD Γ L → (r.lsubst σ).WfD Γ K
  | cfg n R hR hb hG => cfg n R hR
    (hb.lsubst (hσ.liftn_append' hR.symm))
    (λi => (hG i).lsubst
      ((hσ.liftn_append' hR.symm).vliftn_append_cons' _ (by rw [hb.body.num_defs_eq_length])))

def TRegion.WfD.lsubst {Γ : Ctx α ε} {L} {σ} {r : TRegion φ} (hσ : σ.WfD Γ L K)
  : r.WfD Γ L → (r.lsubst σ).WfD Γ K
  | let1 da dt => let1 da (dt.lsubst hσ.vlift)
  | let2 da dt => let2 da (dt.lsubst hσ.vliftn₂)
  | cfg n R hR hr hG => cfg n R hR
    (hr.lsubst (hσ.liftn_append' hR.symm))
    (λi => (hG i).lsubst (hσ.liftn_append' hR.symm).vlift)

end TerminatorSubst

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

def Region.Subst.WfD.slift (A) (hσ : σ.WfD Γ L K) : σ.lift.WfD Γ (A::L) (A::K)
  := hσ.lift (le_refl A)

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

def Region.Subst.WfD.vlift (V) (hσ : σ.WfD Γ L K) : σ.vlift.WfD (V::Γ) L K
  := λi => (hσ i).vwk (Ctx.Wkn.id.step.slift)

theorem Region.Subst.Wf.vlift (V) (hσ : σ.Wf Γ L K) : σ.vlift.Wf (V::Γ) L K
  := λi => (hσ i).vwk (Ctx.Wkn.id.step.slift)

def Region.Subst.WfD.vlift₂ (V₁ V₂) (hσ : σ.WfD Γ L K) : σ.vlift.vlift.WfD (V₁::V₂::Γ) L K
  := (hσ.vlift _).vlift _

def Region.Subst.WfD.vliftn₂ (V₁ V₂) (hσ : σ.WfD Γ L K) : (σ.vliftn 2).WfD (V₁::V₂::Γ) L K
  := Region.Subst.vliftn_eq_iterate_vlift 2 ▸ hσ.vlift₂ _ _

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
  | case he hs ht => case he (hs.lsubst (hσ.vlift _)) (ht.lsubst (hσ.vlift _))
  | let1 da dt => let1 da (dt.lsubst (hσ.vlift _))
  | let2 da dt => let2 da (dt.lsubst (hσ.vliftn₂ _ _))
  | cfg n R hR hr hG => cfg n R hR
    (hr.lsubst (hσ.liftn_append' hR.symm))
    (λi => (hG i).lsubst ((hσ.liftn_append' hR.symm).vlift _))

theorem Region.Wf.lsubst {Γ : Ctx α ε} {L} {σ} {r : Region φ} (hσ : σ.Wf Γ L K) (h : r.Wf Γ L)
  : (r.lsubst σ).Wf Γ K
  := let ⟨d⟩ := h.nonempty; let ⟨hσ⟩ := hσ.nonempty; (d.lsubst hσ).toWf

def Region.InS.lsubst {Γ : Ctx α ε} (σ : Region.Subst.InS φ Γ L K) (r : InS φ Γ L) : InS φ Γ K
  := ⟨(r : Region φ).lsubst σ, r.prop.lsubst σ.prop⟩

def Region.Subst.WfD.comp {Γ : Ctx α ε} {σ : Region.Subst φ} {τ : Region.Subst φ}
  (hσ : σ.WfD Γ K J) (hτ : τ.WfD Γ L K) : (σ.comp τ).WfD Γ L J
  := λi => (hτ i).lsubst (hσ.vlift _)

theorem Region.Subst.Wf.comp {Γ : Ctx α ε} {σ : Region.Subst φ} {τ : Region.Subst φ}
  (hσ : σ.Wf Γ K J) (hτ : τ.Wf Γ L K) : (σ.comp τ).Wf Γ L J
  := λi => (hτ i).lsubst (hσ.vlift _)

end RegionSubst

end BinSyntax
