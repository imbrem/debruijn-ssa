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

@[simp]
theorem Region.Subst.InS.coe_get (r : Region.Subst.InS φ Γ L K) (i : Fin L.length)
  : (r.get i : Region φ) = r.1 i
  := rfl

instance Region.Subst.InS.instCoeOut {Γ : Ctx α ε} {L K : LCtx α}
  : CoeOut (Region.Subst.InS φ Γ L K) (Region.Subst φ)
  := ⟨λr => r.1⟩

@[ext]
theorem Region.Subst.InS.ext (σ τ : Region.Subst.InS φ Γ L K)
  (h : ∀i, σ.val i = τ.val i) : σ = τ
  := Subtype.eq (funext h)

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

@[simp]
theorem Region.Subst.InS.get_lift_zero {σ : Region.Subst.InS φ Γ L K} {h : lo ≤ hi}
  : (σ.lift h).get ⟨0, by simp⟩ = Region.InS.br 0 (Term.InS.var 0 Ctx.Var.shead) (by simp [h])
  := rfl

@[simp]
theorem Region.Subst.InS.get_lift_succ
  {σ : Region.Subst.InS φ Γ L K} {h : lo ≤ hi} {i : Fin L.length}
  : (σ.lift h).get i.succ = (σ.get i).lwk0
  := rfl

def Region.Subst.WfD.slift {head} (hσ : σ.WfD Γ L K) : σ.lift.WfD Γ (head::L) (head::K)
  := hσ.lift (le_refl head)

theorem Region.Subst.Wf.slift {head} (hσ : σ.Wf Γ L K) : σ.lift.Wf Γ (head::L) (head::K)
  := hσ.lift (le_refl head)

def Region.Subst.InS.slift {head} (σ : Region.Subst.InS φ Γ L K)
  : Region.Subst.InS φ Γ (head::L) (head::K)
  := σ.lift (le_refl head)

@[simp]
theorem Region.Subst.InS.coe_slift (σ : Region.Subst.InS φ Γ L K)
  : (σ.slift (head := head) : Region.Subst φ) = (σ : Region.Subst φ).lift
  := rfl

@[simp]
theorem Region.Subst.InS.get_slift_zero {σ : Region.Subst.InS φ Γ L K}
  : (σ.slift (head := head)).get (0 : Fin (L.length + 1))
  = Region.InS.br 0 (Term.InS.var 0 Ctx.Var.shead) (by simp)
  := rfl

@[simp]
theorem Region.Subst.InS.get_slift_succ {σ : Region.Subst.InS φ Γ L K} {i : Fin L.length}
  : (σ.slift (head := head)).get i.succ = (σ.get i).lwk0
  := rfl

def Region.Subst.WfD.liftn_append (J : LCtx α) (hσ : σ.WfD Γ L K)
  : (σ.liftn J.length).WfD Γ (J ++ L) (J ++ K)
  := match J with
  | [] => by rw [List.nil_append, List.nil_append, List.length_nil, liftn_zero]; exact hσ
  | A::J => by rw [List.length_cons, liftn_succ]; exact (hσ.liftn_append J).slift

theorem Region.Subst.Wf.liftn_append (J : LCtx α) (hσ : σ.Wf Γ L K)
  : (σ.liftn J.length).Wf Γ (J ++ L) (J ++ K)
  := match J with
  | [] => by rw [List.nil_append, List.nil_append, List.length_nil, liftn_zero]; exact hσ
  | A::J => by rw [List.length_cons, liftn_succ]; exact (hσ.liftn_append J).slift

def Region.Subst.InS.liftn_append (J : LCtx α) (σ : Region.Subst.InS φ Γ L K)
  : Region.Subst.InS φ Γ (J ++ L) (J ++ K)
  := ⟨σ.val.liftn J.length, σ.prop.liftn_append J⟩

@[simp]
theorem Region.Subst.InS.coe_liftn_append {Γ : Ctx α ε} {L K J : LCtx α}
  {σ : Subst.InS φ Γ L K}
  : (σ.liftn_append J : Region.Subst φ) = (σ : Region.Subst φ).liftn J.length
  := rfl

@[simp]
theorem Region.Subst.InS.liftn_append_get_le {Γ : Ctx α ε} {L K J : LCtx α}
  {σ : Subst.InS φ Γ L K} {i : Fin (J ++ L).length}
  (h : i < J.length)
  : (σ.liftn_append J).get i
  = InS.br i (Term.InS.var 0 Ctx.Var.shead)
    (LCtx.Trg.of_le_getElem
      (by simp only [List.length_append]; omega)
      (by simp [List.getElem_append_left, h]))
  := by ext; simp [Region.Subst.liftn, h]

@[simp]
theorem Region.Subst.InS.liftn_append_singleton {Γ : Ctx α ε} {L K : LCtx α} {V : Ty α}
  {σ : Subst.InS φ Γ L K}
  : σ.liftn_append [V] = σ.slift
  := by ext; simp [liftn_one]

def Region.Subst.WfD.liftn_append' {J : LCtx α} (hn : n = J.length) (hσ : σ.WfD Γ L K)
  : (σ.liftn n).WfD Γ (J ++ L) (J ++ K)
  := hn ▸ hσ.liftn_append J

theorem Region.Subst.Wf.liftn_append' {J : LCtx α} (hn : n = J.length) (hσ : σ.Wf Γ L K)
  : (σ.liftn n).Wf Γ (J ++ L) (J ++ K)
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

@[simp]
theorem Region.Subst.InS.coe_vlift (σ : Region.Subst.InS φ Γ L K)
  : (σ.vlift (head := head) : Region.Subst φ) = Subst.vlift σ
  := rfl

def Region.Subst.WfD.vlift₂ (hσ : σ.WfD Γ L K) : σ.vlift.vlift.WfD (left::right::Γ) L K
  := hσ.vlift.vlift

def Region.Subst.WfD.vliftn₂ (hσ : σ.WfD Γ L K) : (σ.vliftn 2).WfD (left::right::Γ) L K
  := Region.Subst.vliftn_eq_iterate_vlift 2 ▸ hσ.vlift₂

theorem Region.Subst.Wf.vliftn₂ (hσ : σ.Wf Γ L K) : (σ.vliftn 2).Wf (left::right::Γ) L K
  := let ⟨d⟩ := hσ.nonempty; (d.vliftn₂).toWf

def Region.Subst.InS.vliftn₂ (σ : Region.Subst.InS φ Γ L K) : InS φ (left::right::Γ) L K
  := ⟨Subst.vliftn 2 σ, σ.prop.vliftn₂⟩

@[simp]
theorem Region.Subst.InS.coe_vliftn₂ (σ : Region.Subst.InS φ Γ L K)
  : (σ.vliftn₂ (left := left) (right := right) : Region.Subst φ) = Subst.vliftn 2 σ
  := rfl

theorem Region.Subst.InS.vliftn₂_eq_vlift_vlift (σ : Region.Subst.InS φ Γ L K)
  : σ.vliftn₂ (left := left) (right := right) = σ.vlift.vlift
  := by simp [vliftn₂, vlift, vliftn_succ]

def Region.Subst.WfD.vliftn_append (Ξ : Ctx α ε) (hσ : σ.WfD Γ L K)
  : (σ.vliftn Ξ.length).WfD (Ξ ++ Γ) L K
  := λi => (hσ i).vwk (Ctx.Wkn.id.stepn_append Ξ).slift

theorem Region.Subst.Wf.vlift_append (Ξ : Ctx α ε) (hσ : σ.Wf Γ L K)
  : (σ.vliftn Ξ.length).Wf (Ξ ++ Γ) L K
  := λi => (hσ i).vwk (Ctx.Wkn.id.stepn_append Ξ).slift

def Region.Subst.WfD.vliftn_append' {Ξ : Ctx α ε} (hn : n = Ξ.length) (hσ : σ.WfD Γ L K)
  : (σ.vliftn n).WfD (Ξ ++ Γ) L K
  := λi => (hσ i).vwk ((Ctx.Wkn.id.stepn_append' hn).slift)

theorem Region.Subst.Wf.vlift_append' {Ξ : Ctx α ε} (hn : n = Ξ.length) (hσ : σ.Wf Γ L K)
  : (σ.vliftn n).Wf (Ξ ++ Γ) L K
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

def Region.Subst.InS.comp {Γ : Ctx α ε}
  (σ : Region.Subst.InS φ Γ K J) (τ : Region.Subst.InS φ Γ L K) : Region.Subst.InS φ Γ L J
  := ⟨σ.val.comp τ.val, σ.prop.comp τ.prop⟩

@[simp]
theorem Region.Subst.InS.coe_comp {Γ : Ctx α ε}
  {σ : Region.Subst.InS φ Γ K J} {τ : Region.Subst.InS φ Γ L K}
  : (σ.comp τ : Region.Subst φ) = (σ : Region.Subst φ).comp τ := rfl

theorem Region.InS.lsubst_lsubst {Γ : Ctx α ε}
  {σ : Region.Subst.InS φ Γ K J} {τ : Region.Subst.InS φ Γ L K}
  {r : Region.InS φ Γ L}
  : (r.lsubst τ).lsubst σ = r.lsubst (σ.comp τ)
  := by ext; simp [Region.lsubst_lsubst]

def Region.Subst.InS.vsubst {Γ Δ : Ctx α ε}
  (ρ : Term.Subst.InS φ Γ Δ) (σ : Region.Subst.InS φ Δ L K)
  : Region.Subst.InS φ Γ L K
  := ⟨Region.vsubst ρ.val.lift ∘ σ.val, (λi => (σ.prop i).vsubst ρ.prop.slift)⟩

@[simp]
theorem Region.Subst.InS.coe_vsubst {Γ Δ : Ctx α ε}
  (ρ : Term.Subst.InS φ Γ Δ) (σ : Region.Subst.InS φ Δ L K)
  : (σ.vsubst ρ : Region.Subst φ) = Region.vsubst ρ.val.lift ∘ (σ : Region.Subst φ)
  := rfl

-- TODO: vsubst_id, vsubst_comp, and other lore...

theorem Region.InS.vsubst_lsubst {Γ Δ : Ctx α ε}
  {σ : Region.Subst.InS φ Δ L K} {ρ : Term.Subst.InS φ Γ Δ}
  {r : Region.InS φ Δ L}
  : (r.lsubst σ).vsubst ρ = (r.vsubst ρ).lsubst (σ.vsubst ρ)
  := by ext; simp [Region.vsubst_lsubst]

def LCtx.InS.toSubst {Γ : Ctx α ε} {L K : LCtx α} (ρ : L.InS K) : Region.Subst.InS φ Γ L K
  := ⟨Region.Subst.fromLwk ρ, λℓ => Region.Wf.br (ρ.prop ℓ ℓ.prop) (Term.Wf.var Ctx.Var.shead)⟩

@[simp]
theorem LCtx.InS.coe_toSubst {Γ : Ctx α ε} {L K : LCtx α} {ρ : L.InS K}
  : (ρ.toSubst (φ := φ) (Γ := Γ) : Region.Subst φ) = Region.Subst.fromLwk ρ
  := rfl

def Region.InS.lsubst_toSubst {Γ : Ctx α ε} {L K : LCtx α} {ρ : L.InS K} {r : Region.InS φ Γ L}
  : r.lsubst (ρ.toSubst) = r.lwk ρ
  := by ext; simp [Region.lsubst_fromLwk]

@[simp]
theorem Region.InS.get_toSubst {Γ : Ctx α ε} {L K : LCtx α} {ρ : L.InS K} {ℓ : Fin L.length}
  : ((ρ.toSubst (φ := φ) (Γ := Γ)).get ℓ)
  = InS.br (ρ.val ℓ) (Term.InS.var 0 Ctx.Var.shead) (ρ.prop ℓ ℓ.prop)
  := rfl

@[simp]
theorem Region.InS.lsubst_br {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K}
  {ℓ : ℕ} {a : Term.InS φ Γ ⟨A, ⊥⟩} {hℓ : L.Trg ℓ A}
  : (br ℓ a hℓ).lsubst σ = ((σ.get ⟨ℓ, hℓ.length⟩).vwk_id (by simp [hℓ.getElem])).vsubst a.subst0
  := rfl

@[simp]
theorem Region.InS.lsubst_case {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K}
  {e : Term.InS φ Γ (A.coprod B, ⊥)}
  {s : Region.InS φ ((A, ⊥)::Γ) L} {t : Region.InS φ ((B, ⊥)::Γ) L}
  : (case e s t).lsubst σ = case e (s.lsubst σ.vlift) (t.lsubst σ.vlift)
  := rfl

@[simp]
theorem Region.InS.lsubst_let1 {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K}
  {a : Term.InS φ Γ ⟨A, e⟩} {t : Region.InS φ ((A, ⊥)::Γ) L}
  : (let1 a t).lsubst σ = let1 a (t.lsubst σ.vlift)
  := rfl

@[simp]
theorem Region.InS.lsubst_let2 {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K}
  {a : Term.InS φ Γ ⟨A.prod B, e⟩} {t : Region.InS φ ((B, ⊥)::(A, ⊥)::Γ) L}
  : (let2 a t).lsubst σ = let2 a (t.lsubst σ.vliftn₂)
  := rfl

@[simp]
theorem Region.InS.lsubst_cfg {Γ : Ctx α ε} {L K : LCtx α} {σ : Subst.InS φ Γ L K}
  {R : LCtx α} {β : Region.InS φ Γ (R ++ L)}
  {G : ∀i : Fin R.length, Region.InS φ ((R.get i, ⊥)::Γ) (R ++ L)}
  : (cfg R β G).lsubst σ
  = cfg R (β.lsubst (σ.liftn_append R)) (λi => (G i).lsubst (σ.liftn_append R).vlift)
  := rfl

theorem Region.InS.lsubst_lift_lwk0 {Γ : Ctx α ε} {L K : LCtx α}
  {σ : Subst.InS φ Γ L K} {h : lo ≤ hi} {r : Region.InS φ Γ L}
  : r.lwk0.lsubst (σ.lift h) = (r.lsubst σ).lwk0 := by
  ext
  simp only [coe_lsubst, Subst.InS.coe_lift, coe_lwk0, Region.lwk0, ←lsubst_fromLwk,
    Region.lsubst_lsubst]
  congr
  funext k
  simp only [Subst.comp, Region.lsubst, Subst.vlift, Nat.succ_eq_add_one,
    Function.comp_apply, Subst.lift, Region.Subst.vwk1_comp_fromLwk]
  simp only [<-Region.vsubst_fromWk, Region.vwk1, Region.vsubst_vsubst]
  rw [Region.vsubst_id', Region.lsubst_fromLwk]
  funext k
  cases k <;> rfl

theorem Region.InS.lsubst_slift_lwk0 {Γ : Ctx α ε} {L K : LCtx α}
  {σ : Subst.InS φ Γ L K} {r : Region.InS φ Γ L}
  : r.lwk0.lsubst (σ.slift (head := head)) = (r.lsubst σ).lwk0 := Region.InS.lsubst_lift_lwk0

theorem Region.Subst.InS.vlift_lift {Γ : Ctx α ε} {L K : LCtx α}
  {σ : Subst.InS φ Γ L K} {h : lo ≤ hi}
  : (σ.lift h).vlift (head := head) = σ.vlift.lift h := by ext; simp [Region.Subst.vlift_lift_comm]

theorem Region.Subst.InS.vlift_slift {Γ : Ctx α ε} {L K : LCtx α}
  {σ : Subst.InS φ Γ L K}
  : (σ.slift (head := head')).vlift (head := head) = σ.vlift.slift := vlift_lift

theorem Region.InS.vwk1_lsubst_vlift {Γ : Ctx α ε} {L K : LCtx α}
  {σ : Subst.InS φ Γ L K} {r : Region.InS φ (head::Γ) L}
  : (r.lsubst σ.vlift).vwk1 (inserted := inserted) = r.vwk1.lsubst σ.vlift.vlift := by
  ext
  simp only [Set.mem_setOf_eq, vwk1, coe_vwk, Ctx.InS.coe_wk1, coe_lsubst, Subst.InS.coe_vlift,
    Subst.vlift, vwk_lsubst]
  congr
  simp only [<-Function.comp.assoc, Region.vwk1, <-Region.vwk_comp]
  apply congrFun
  apply congrArg
  apply congrArg
  funext k
  cases k <;> rfl

end RegionSubst

end BinSyntax
