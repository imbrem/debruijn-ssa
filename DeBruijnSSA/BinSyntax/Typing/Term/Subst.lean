import DeBruijnSSA.BinSyntax.Typing.Term.Basic
import DeBruijnSSA.BinSyntax.Syntax.Subst

namespace BinSyntax

section Subst

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]
  {Γ Δ : Ctx α ε} {σ : Term.Subst φ}

namespace Term

def Subst.WfD (Γ Δ : Ctx α ε) (σ : Subst φ) : Type _
  := ∀i : Fin Δ.length, (σ i).WfD Γ (Δ.get i)

def Subst.Wf (Γ Δ : Ctx α ε) (σ : Subst φ) : Prop
  := ∀i : Fin Δ.length, (σ i).Wf Γ (Δ.get i)

def Subst.InS (φ) [EffInstSet φ (Ty α) ε] (Γ Δ : Ctx α ε) : Type _ := {σ : Subst φ | σ.Wf Γ Δ}

instance Subst.InS.instCoeOut {Γ Δ : Ctx α ε} : CoeOut (Subst.InS φ Γ Δ) (Subst φ)
  := ⟨λr => r.1⟩

theorem Subst.InS.eq_of_coe_eq {σ τ : Subst.InS φ Γ Δ} (h : (σ : Subst φ) = τ) : σ = τ
  := by cases σ; cases τ; cases h; rfl

theorem Subst.Wf.nonempty (hσ : σ.Wf Γ Δ) : Nonempty (σ.WfD Γ Δ)
  := ⟨λi => Classical.choice (hσ i).nonempty⟩

theorem Subst.WfD.toWf (hσ : σ.WfD Γ Δ) : σ.Wf Γ Δ
  := λi => (hσ i).toWf

theorem Subst.Wf.nonempty_iff : σ.Wf Γ Δ ↔ Nonempty (σ.WfD Γ Δ)
  := ⟨Subst.Wf.nonempty, λ⟨h⟩ => h.toWf⟩

def Subst.WfD.lift (h : V ≤ V') (hσ : σ.WfD Γ Δ) : σ.lift.WfD (V::Γ) (V'::Δ)
  := λi => i.cases (WfD.var (Ctx.Var.head h _)) (λi => (hσ i).wk Ctx.Wkn.id.step)

theorem Subst.Wf.lift (h : V ≤ V') (hσ : σ.Wf Γ Δ) : σ.lift.Wf (V::Γ) (V'::Δ)
  := λi => i.cases (Wf.var (Ctx.Var.head h _)) (λi => (hσ i).wk Ctx.Wkn.id.step)

def Subst.InS.lift (h : V ≤ V') (σ : InS φ Γ Δ) : InS φ (V::Γ) (V'::Δ)
  := ⟨Subst.lift σ, σ.prop.lift h⟩

@[simp]
theorem Subst.coe_lift {h : V ≤ V'} {σ : InS φ Γ Δ}
  : (σ.lift h : Subst φ) = Subst.lift σ
  := rfl

def Subst.WfD.slift {head} (hσ : σ.WfD Γ Δ) : σ.lift.WfD (head::Γ) (head::Δ)
  := hσ.lift (le_refl head)

theorem Subst.Wf.slift {head} (hσ : σ.Wf Γ Δ) : σ.lift.Wf (head::Γ) (head::Δ)
  := hσ.lift (le_refl head)

def Subst.WfD.lift₂ (h₁ : V₁ ≤ V₁') (h₂ : V₂ ≤ V₂') (hσ : σ.WfD Γ Δ)
  : σ.lift.lift.WfD (V₁::V₂::Γ) (V₁'::V₂'::Δ)
  := (hσ.lift h₂).lift h₁

theorem Subst.Wf.lift₂ (h₁ : V₁ ≤ V₁') (h₂ : V₂ ≤ V₂') (hσ : σ.Wf Γ Δ)
  : σ.lift.lift.Wf (V₁::V₂::Γ) (V₁'::V₂'::Δ)
  := (hσ.lift h₂).lift h₁

def Subst.WfD.slift₂ {left right} (hσ : σ.WfD Γ Δ)
  : σ.lift.lift.WfD (left::right::Γ) (left::right::Δ)
  := hσ.lift₂ (le_refl _) (le_refl _)

theorem Subst.Wf.slift₂ {left right} (hσ : σ.Wf Γ Δ)
  : σ.lift.lift.Wf (left::right::Γ) (left::right::Δ)
  := hσ.lift₂ (le_refl _) (le_refl _)

-- TODO: version with nicer defeq?
def Subst.WfD.liftn_append (Ξ : Ctx α ε) (hσ : σ.WfD Γ Δ)
  : (σ.liftn Ξ.length).WfD (Ξ ++ Γ) (Ξ ++ Δ) := match Ξ with
  | [] => by rw [List.nil_append, List.nil_append, List.length_nil, liftn_zero]; exact hσ
  | A::Ξ => by rw [List.length_cons, liftn_succ]; exact (hσ.liftn_append Ξ).slift

theorem Subst.Wf.liftn_append (Ξ : Ctx α ε) (hσ : σ.Wf Γ Δ)
  : (σ.liftn Ξ.length).Wf (Ξ ++ Γ) (Ξ ++ Δ) := match Ξ with
  | [] => by rw [List.nil_append, List.nil_append, List.length_nil, liftn_zero]; exact hσ
  | A::Ξ => by rw [List.length_cons, liftn_succ]; exact (hσ.liftn_append Ξ).slift

def Subst.WfD.liftn_append' {Ξ : Ctx α ε} (hn : n = Ξ.length) (hσ : σ.WfD Γ Δ)
  : (σ.liftn n).WfD (Ξ ++ Γ) (Ξ ++ Δ)
  := hn ▸ hσ.liftn_append Ξ

theorem Subst.Wf.liftn_append' {Ξ : Ctx α ε} (hn : n = Ξ.length) (hσ : σ.Wf Γ Δ)
  : (σ.liftn n).Wf (Ξ ++ Γ) (Ξ ++ Δ)
  := hn ▸ hσ.liftn_append Ξ

def Subst.WfD.liftn_append_cons (V) (Ξ : Ctx α ε) (hσ : σ.WfD Γ Δ)
  : (σ.liftn (Ξ.length + 1)).WfD (V::(Ξ ++ Γ)) (V::(Ξ ++ Δ))
  := liftn_append (V::Ξ) hσ

theorem Subst.Wf.liftn_append_cons (V) (Ξ : Ctx α ε) (hσ : σ.Wf Γ Δ)
  : (σ.liftn (Ξ.length + 1)).Wf (V::(Ξ ++ Γ)) (V::(Ξ ++ Δ))
  := liftn_append (V::Ξ) hσ

def Subst.WfD.liftn_append_cons' (V) {Ξ : Ctx α ε} (hn : n = Ξ.length + 1) (hσ : σ.WfD Γ Δ)
  : (σ.liftn n).WfD (V::(Ξ ++ Γ)) (V::(Ξ ++ Δ))
  := hn ▸ hσ.liftn_append_cons V Ξ

theorem Subst.Wf.liftn_append_cons' (V) {Ξ : Ctx α ε} (hn : n = Ξ.length + 1) (hσ : σ.Wf Γ Δ)
  : (σ.liftn n).Wf (V::(Ξ ++ Γ)) (V::(Ξ ++ Δ))
  := hn ▸ hσ.liftn_append_cons V Ξ

-- TODO: version with nicer defeq?
def Subst.WfD.liftn₂ (h₁ : V₁ ≤ V₁') (h₂ : V₂ ≤ V₂') (hσ : σ.WfD Γ Δ)
  : (σ.liftn 2).WfD (V₁::V₂::Γ) (V₁'::V₂'::Δ)
  := Subst.liftn_eq_iterate_lift 2 ▸ hσ.lift₂ h₁ h₂

theorem Subst.Wf.liftn₂ (h₁ : V₁ ≤ V₁') (h₂ : V₂ ≤ V₂') (hσ : σ.Wf Γ Δ)
  : (σ.liftn 2).Wf (V₁::V₂::Γ) (V₁'::V₂'::Δ)
  := Subst.liftn_eq_iterate_lift 2 ▸ hσ.lift₂ h₁ h₂

def Subst.InS.liftn₂ (h₁ : V₁ ≤ V₁') (h₂ : V₂ ≤ V₂') (σ : Subst.InS φ Γ Δ)
  : Subst.InS φ (V₁::V₂::Γ) (V₁'::V₂'::Δ)
  := ⟨Subst.liftn 2 σ, σ.prop.liftn₂ h₁ h₂⟩

theorem Subst.InS.lift_lift (h₁ : V₁ ≤ V₁') (h₂ : V₂ ≤ V₂') (σ : Subst.InS φ Γ Δ)
  : (σ.lift h₂).lift h₁ = (σ.liftn₂ h₁ h₂)
  := by simp [lift, liftn₂, Subst.liftn_succ]

def Subst.WfD.sliftn₂ {left right} (hσ : σ.WfD Γ Δ)
  : (σ.liftn 2).WfD (left::right::Γ) (left::right::Δ)
  := hσ.liftn₂ (le_refl _) (le_refl _)

theorem Subst.Wf.sliftn₂ {left right} (hσ : σ.Wf Γ Δ)
  : (σ.liftn 2).Wf (left::right::Γ) (left::right::Δ)
  := hσ.liftn₂ (le_refl _) (le_refl _)

def Ctx.Var.subst (hσ : σ.WfD Γ Δ) (h : Δ.Var n V) : (σ n).WfD Γ V
  := (hσ ⟨n, h.length⟩).wk_res h.get

theorem Ctx.Var.subst' (hσ : σ.Wf Γ Δ) (h : Δ.Var n V) : (σ n).Wf Γ V
  := (hσ ⟨n, h.length⟩).wk_res h.get

def WfD.subst {Γ Δ : Ctx α ε} {σ} (hσ : σ.WfD Γ Δ) {a : Term φ}
  : a.WfD Δ V → (a.subst σ).WfD Γ V
  | var h => Ctx.Var.subst hσ h
  | op df de => op df (de.subst hσ)
  | let1 da dt => let1 (da.subst hσ) (dt.subst hσ.slift)
  | pair dl dr => pair (dl.subst hσ) (dr.subst hσ)
  | let2 da dt => let2 (da.subst hσ) (dt.subst hσ.sliftn₂)
  | inl d => inl (d.subst hσ)
  | inr d => inr (d.subst hσ)
  | case de dl dr => case (de.subst hσ) (dl.subst hσ.slift) (dr.subst hσ.slift)
  | abort d => abort (d.subst hσ)
  | unit e => unit e

theorem Wf.subst {a : Term φ} (hσ : σ.Wf Γ Δ) (h : a.Wf Δ V) : (a.subst σ).Wf Γ V
  := let ⟨d⟩ := h.nonempty; let ⟨hσ⟩ := hσ.nonempty; (d.subst hσ).toWf


def InS.subst (σ : Subst.InS φ Γ Δ) (a : InS φ Δ V) : InS φ Γ V
  := ⟨(a : Term φ).subst σ, a.prop.subst σ.prop⟩

@[simp]
theorem InS.coe_subst {σ : Subst.InS φ Γ Δ} {a : InS φ Δ V}
  : (a.subst σ : Term φ) = (a : Term φ).subst σ
  := rfl

def Subst.InS.get (n) (h : Δ.Var n V) (σ : Subst.InS φ Γ Δ) : Term.InS φ Γ V
  := ⟨σ.val n, Ctx.Var.subst' σ.prop h⟩

@[simp]
theorem InS.subst_var (σ : Subst.InS φ Γ Δ) (h : Δ.Var n V) :
  (var n h).subst σ = σ.get n h
  := rfl

@[simp]
theorem InS.subst_op (σ : Subst.InS φ Γ Δ) (df : Φ.EFn f A B e) (de : InS φ Δ ⟨A, e⟩) :
  (op f df de).subst σ = op f df (de.subst σ)
  := rfl

@[simp]
theorem InS.subst_pair (σ : Subst.InS φ Γ Δ) (dl : InS φ Δ ⟨A, e⟩) (dr : InS φ Δ ⟨B, e⟩) :
  (pair dl dr).subst σ = pair (dl.subst σ) (dr.subst σ)
  := rfl

@[simp]
theorem InS.subst_inl (σ : Subst.InS φ Γ Δ) (d : InS φ Δ ⟨A, e⟩) :
  (inl (right := right) d).subst σ = inl (d.subst σ)
  := rfl

@[simp]
theorem InS.subst_inr (σ : Subst.InS φ Γ Δ) (d : InS φ Δ ⟨B, e⟩) :
  (inr (left := left) d).subst σ = inr (d.subst σ)
  := rfl

@[simp]
theorem InS.subst_abort (σ : Subst.InS φ Γ Δ) (d : InS φ Δ ⟨Ty.empty, e⟩) :
  (abort (tyOut := tyOut) d).subst σ = abort (tyOut := tyOut) (d.subst σ)
  := rfl

@[simp]
theorem InS.subst_unit (σ : Subst.InS φ Γ Δ) (e : ε) :
  (unit e).subst σ = unit e
  := rfl

def WfD.subst0 {a : Term φ} (ha : a.WfD Δ V) : a.subst0.WfD Δ (V::Δ)
  := λi => i.cases ha (λi => WfD.var ⟨by simp, by simp⟩)

theorem Wf.subst0 {a : Term φ} (ha : a.Wf Δ V) : a.subst0.Wf Δ (V::Δ)
  := λi => i.cases ha (λi => Wf.var ⟨by simp, by simp⟩)

def InS.subst0 (a : InS φ Γ V) : Subst.InS φ Γ (V::Γ)
  := ⟨(a : Term φ).subst0, a.prop.subst0⟩

@[simp]
theorem InS.coe_subst0 {a : InS φ Γ V}
  : (a.subst0 : Subst φ) = (a : Term φ).subst0
  := rfl

@[simp]
theorem Subst.InS.get_0_subst0 (a : Term.InS φ Δ ty)
  : a.subst0.get 0 (by simp) = a
  := rfl

@[simp]
theorem Subst.InS.get_succ_lift (n)
  (h : Ctx.Var _ (n + 1) ty) (σ : Subst.InS φ Γ Δ)
  (hv : lo ≤ hi)
  : (σ.lift hv).get (n + 1) h = (σ.get n h.tail).wk ⟨Nat.succ, by simp⟩
  := rfl

def Subst.WfD.comp {Γ Δ Ξ : Ctx α ε} {σ : Subst φ} {τ : Subst φ}
  (hσ : σ.WfD Γ Δ) (hτ : τ.WfD Δ Ξ) : (σ.comp τ).WfD Γ Ξ
  := λi => (hτ i).subst hσ

theorem Subst.Wf.comp {Γ Δ Ξ : Ctx α ε} {σ : Subst φ} {τ : Subst φ}
  (hσ : σ.Wf Γ Δ) (hτ : τ.Wf Δ Ξ) : (σ.comp τ).Wf Γ Ξ
  := λi => (hτ i).subst hσ

def Subst.InS.comp {Γ Δ Ξ : Ctx α ε} (σ : Subst.InS φ Γ Δ) (τ : Subst.InS φ Δ Ξ)
  : Subst.InS φ Γ Ξ
  := ⟨Subst.comp σ τ, σ.prop.comp τ.prop⟩

@[simp]
theorem Subst.InS.coe_comp {Γ Δ Ξ : Ctx α ε}
  {σ : Subst.InS φ Γ Δ} {τ : Subst.InS φ Δ Ξ}
  : (σ.comp τ : Subst φ) = Subst.comp σ τ
  := rfl

theorem InS.subst_subst {Γ Δ Ξ : Ctx α ε} {σ : Subst.InS φ Γ Δ} {τ : Subst.InS φ Δ Ξ}
  (a : InS φ Ξ V) : (a.subst τ).subst σ = a.subst (σ.comp τ)
  := by ext; simp [Term.subst_subst]

-- TODO: Subst.InS.comp_id, id_comp ==> this is a category!

theorem Subst.InS.comp_assoc {Γ Δ Ξ Ω : Ctx α ε}
  {σ : Subst.InS φ Γ Δ} {τ : Subst.InS φ Δ Ξ} {υ : Subst.InS φ Ξ Ω}
  : (σ.comp τ).comp υ = σ.comp (τ.comp υ)
  := by apply eq_of_coe_eq; simp [Subst.comp_assoc]
