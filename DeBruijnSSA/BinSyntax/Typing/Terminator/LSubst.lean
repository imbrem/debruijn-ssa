import DeBruijnSSA.BinSyntax.Typing.Terminator.VSubst
import DeBruijnSSA.BinSyntax.Typing.Term.Subst

namespace BinSyntax

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
