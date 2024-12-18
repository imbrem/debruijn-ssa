import Discretion.Wk.List
import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Fv.Basic
import DeBruijnSSA.BinSyntax.Syntax.Effect.Definitions

import DeBruijnSSA.BinSyntax.Typing.Ctx
import DeBruijnSSA.BinSyntax.Typing.LCtx
import DeBruijnSSA.BinSyntax.Typing.Term.Basic

namespace BinSyntax

section Basic

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε]

theorem Ctx.Wkn.toFinWk_id {Γ Δ : Ctx α ε} {L L' R S : LCtx α} {ρ : Fin R.length → Fin S.length}
  (hρ : (R ++ L).Wkn (S ++ L') (Fin.toNatWk ρ)) (i : Fin R.length)
  (h : Γ.Wkn Δ _root_.id)
  : Wkn (⟨R[i], e⟩::Γ) (⟨S[ρ i], e⟩::Δ) _root_.id := by
  simp only [Fin.getElem_fin, lift_id_iff, ge_iff_le, Prod.mk_le_mk, le_refl, and_true, h]
  exact hρ.toFinWk_append i

variable [Bot ε]

namespace Region

inductive WfD : Ctx α ε → Region φ → LCtx α → Type _
  | br : L.Trg n A → a.WfD Γ ⟨A, ⊥⟩ → WfD Γ (br n a) L
  | case : a.WfD Γ ⟨Ty.coprod A B, e⟩
    → s.WfD (⟨A, ⊥⟩::Γ) L
    → t.WfD (⟨B, ⊥⟩::Γ) L
    → WfD Γ (case a s t) L
  | let1 : a.WfD Γ ⟨A, e⟩ → t.WfD (⟨A, ⊥⟩::Γ) L → (let1 a t).WfD Γ L
  | let2 : a.WfD Γ ⟨(Ty.prod A B), e⟩ → t.WfD (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L → (let2 a t).WfD Γ L
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.WfD Γ (R ++ L) →
    (∀i : Fin n, (G i).WfD (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    WfD Γ (cfg β n G) L

inductive Wf : Ctx α ε → Region φ → LCtx α → Prop
  | br : L.Trg n A → a.Wf Γ ⟨A, ⊥⟩ → Wf Γ (br n a) L
  | case : a.Wf Γ ⟨Ty.coprod A B, e⟩
    → s.Wf (⟨A, ⊥⟩::Γ) L
    → t.Wf (⟨B, ⊥⟩::Γ) L
    → Wf Γ (case a s t) L
  | let1 : a.Wf Γ ⟨A, e⟩ → t.Wf (⟨A, ⊥⟩::Γ) L → (let1 a t).Wf Γ L
  | let2 : a.Wf Γ ⟨(Ty.prod A B), e⟩ → t.Wf (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L → (let2 a t).Wf Γ L
  | cfg (n) {G} (R : LCtx α) :
    (hR : R.length = n) → β.Wf Γ (R ++ L) →
    (∀i : Fin n, (G i).Wf (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L)) →
    Wf Γ (cfg β n G) L

def WfD.src {Γ : Ctx α ε} {r : Region φ} {L} (_ : r.WfD Γ L) := Γ

def WfD.trg {Γ : Ctx α ε} {r : Region φ} {L} (_ : r.WfD Γ L) := L

def WfD.tm {Γ : Ctx α ε} {r : Region φ} {L} (_ : r.WfD Γ L) := r

def WfD.cfg_arity {Γ : Ctx α ε} {β : Region φ} {n G} {L}
  (_ : (Region.cfg β n G).WfD Γ L) : ℕ := n

theorem WfD.toWf {Γ : Ctx α ε} {r : Region φ} {L} : r.WfD Γ L → r.Wf Γ L
  | WfD.br hℓ da => Wf.br hℓ da.toWf
  | WfD.case ea es et => Wf.case ea.toWf es.toWf et.toWf
  | WfD.let1 da dt => Wf.let1 da.toWf dt.toWf
  | WfD.let2 da dt => Wf.let2 da.toWf dt.toWf
  | WfD.cfg n R hR dβ dG => Wf.cfg n R hR dβ.toWf (λi => (dG i).toWf)

theorem Wf.nonempty {Γ : Ctx α ε} {r : Region φ} {L} : r.Wf Γ L → Nonempty (r.WfD Γ L)
  | Wf.br hℓ da => let ⟨da⟩ := da.nonempty; ⟨WfD.br hℓ da⟩
  | Wf.case ea es et =>
    let ⟨ea⟩ := ea.nonempty; let ⟨es⟩ := es.nonempty; let ⟨et⟩ := et.nonempty;
    ⟨WfD.case ea es et⟩
  | Wf.let1 da dt => let ⟨da⟩ := da.nonempty; let ⟨dt⟩ := dt.nonempty; ⟨WfD.let1 da dt⟩
  | Wf.let2 da dt => let ⟨da⟩ := da.nonempty; let ⟨dt⟩ := dt.nonempty; ⟨WfD.let2 da dt⟩
  | Wf.cfg n R hR dβ dG => by
    let ⟨dβ⟩ := dβ.nonempty;
    have dG := (λi => (dG i).nonempty);
    rw [<-Classical.nonempty_pi] at dG;
    let ⟨dG⟩ := dG
    exact ⟨WfD.cfg n R hR dβ dG⟩

theorem Wf.nonempty_iff {Γ : Ctx α ε} {r : Region φ} {L} : r.Wf Γ L ↔ Nonempty (r.WfD Γ L)
  := ⟨Wf.nonempty, λ⟨h⟩ => h.toWf⟩

theorem Wf.br_iff {Γ : Ctx α ε} {ℓ} {a : Term φ} {L}
  : (Region.br ℓ a).Wf Γ L ↔ ∃A, L.Trg ℓ A ∧ a.Wf Γ ⟨A, ⊥⟩
  := ⟨λ| Wf.br hℓ da => ⟨_, hℓ, da⟩, λ⟨_, hℓ, da⟩ => Wf.br hℓ da⟩

@[simp]
theorem Wf.case_iff {Γ : Ctx α ε} {a : Term φ} {s t : Region φ} {L}
  : (Region.case a s t).Wf Γ L
  ↔ ∃A B e, a.Wf Γ ⟨Ty.coprod A B, e⟩ ∧ s.Wf (⟨A, ⊥⟩::Γ) L ∧ t.Wf (⟨B, ⊥⟩::Γ) L
  := ⟨λ| Wf.case ea es et => ⟨_, _, _, ea, es, et⟩, λ⟨_, _, _, ea, es, et⟩ => Wf.case ea es et⟩

@[simp]
theorem Wf.let1_iff {Γ : Ctx α ε} {a : Term φ} {t : Region φ} {L}
  : (Region.let1 a t).Wf Γ L ↔ ∃A e, a.Wf Γ ⟨A, e⟩ ∧ t.Wf (⟨A, ⊥⟩::Γ) L
  := ⟨λ| Wf.let1 da dt => ⟨_, _, da, dt⟩, λ⟨_, _, da, dt⟩ => Wf.let1 da dt⟩

@[simp]
theorem Wf.let2_iff {Γ : Ctx α ε} {a : Term φ} {t : Region φ} {L}
  : (Region.let2 a t).Wf Γ L ↔ ∃A B e, a.Wf Γ ⟨Ty.prod A B, e⟩ ∧ t.Wf (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L
  := ⟨λ| Wf.let2 da dt => ⟨_, _, _, da, dt⟩, λ⟨_, _, _, da, dt⟩ => Wf.let2 da dt⟩

@[simp]
theorem Wf.cfg_iff {Γ : Ctx α ε} {n} {G} {β : Region φ} {L}
  : (Region.cfg β n G).Wf Γ L ↔ ∃R : LCtx α, ∃h : R.length = n,
    β.Wf Γ (R ++ L) ∧ ∀i : Fin n, (G i).Wf (⟨R.get (i.cast h.symm), ⊥⟩::Γ) (R ++ L)
  := ⟨λ| Wf.cfg n _ hR dβ dG => ⟨_, hR, dβ, dG⟩, λ⟨_, hR, dβ, dG⟩ => Wf.cfg n _ hR dβ dG⟩

def InS (φ) [EffInstSet φ (Ty α) ε] (Γ : Ctx α ε) (L : LCtx α) : Type _
  := {r : Region φ | r.Wf Γ L}

instance InS.instCoeOut {Γ : Ctx α ε} {L : LCtx α} : CoeOut (InS φ Γ L) (Region φ)
  := ⟨λr => r.1⟩

@[simp]
theorem InS.coe_wf {Γ : Ctx α ε} {L : LCtx α} {r : InS φ Γ L} : (r : Region φ).Wf Γ L
  := r.2

def InS.cast {Γ Γ' : Ctx α ε} {L L' : LCtx α} (hΓ : Γ = Γ') (hL : L = L') (r : InS φ Γ L)
  : InS φ Γ' L'
  := ⟨r, hΓ ▸ hL ▸ r.2⟩

@[simp]
theorem InS.coe_cast {Γ Γ' : Ctx α ε} {L L' : LCtx α}
  (hΓ : Γ = Γ') (hL : L = L') (r : InS φ Γ L)
  : (r.cast hΓ hL : Region φ) = (r : Region φ)
  := rfl

@[ext]
theorem InS.ext {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ Γ L}
  (h : (r : Region φ) = r') : r = r'
  := by cases r; cases r'; cases h; rfl

theorem InS.ext_iff' {Γ : Ctx α ε} {L : LCtx α} {r r' : InS φ Γ L}
  : r = r' ↔ (r : Region φ) = r'
  := ⟨congrArg _, λh => InS.ext h⟩

theorem InS.hext {Γ Γ' : Ctx α ε} {L L' : LCtx α} {r : InS φ Γ L} {r' : InS φ Γ' L'}
  (hΓ : Γ = Γ') (hL : L = L') (h : (r : Region φ) = r') : HEq r r'
  := by cases hΓ; cases hL; simp [ext h]

@[simp]
theorem InS.cast_inj {Γ Γ' : Ctx α ε} {L L' : LCtx α} {r r' : InS φ Γ L}
  {hΓ : Γ = Γ'} {hL : L = L'}
  : r.cast hΓ hL = r'.cast hΓ hL ↔ r = r'
  := by simp [ext_iff']

def Wf.toInS {Γ : Ctx α ε} {r : Region φ} {L} (h : r.Wf Γ L) : InS φ Γ L
  := ⟨r, h⟩

@[simp]
theorem Wf.coe_toInS {Γ : Ctx α ε} {r : Region φ} {L} {h : r.Wf Γ L}
  : h.toInS.val = r := rfl

def WfD.toInS {Γ : Ctx α ε} {r : Region φ} {L} (h : r.WfD Γ L) : InS φ Γ L
  := ⟨r, h.toWf⟩

@[simp]
theorem WfD.coe_toInS {Γ : Ctx α ε} {r : Region φ} {L} {h : r.WfD Γ L}
  : h.toInS.val = r := rfl

def InS.br {Γ : Ctx α ε} {L : LCtx α} (ℓ) (a : Term.InS φ Γ ⟨A, ⊥⟩)
  (hℓ : L.Trg ℓ A) : InS φ Γ L
  := ⟨Region.br ℓ a, Wf.br hℓ a.2⟩

@[simp]
theorem InS.coe_br {Γ : Ctx α ε} {L : LCtx α} (ℓ) (a : Term.InS φ Γ ⟨A, ⊥⟩)
  (hℓ : L.Trg ℓ A) : (InS.br ℓ a hℓ : Region φ) = Region.br ℓ a
  := rfl

def InS.let1 {Γ : Ctx α ε} {L : LCtx α} {A e}
  (a : Term.InS φ Γ ⟨A, e⟩)
  (t : InS φ (⟨A, ⊥⟩::Γ) L) : InS φ Γ L
  := ⟨Region.let1 a t, Wf.let1 a.prop t.prop⟩

@[simp]
theorem InS.coe_let1 {Γ : Ctx α ε} {L : LCtx α} {A e}
  (a : Term.InS φ Γ ⟨A, e⟩) (t : InS φ (⟨A, ⊥⟩::Γ) L) : (t.let1 a : Region φ) = Region.let1 a t
  := rfl

def InS.let2 {Γ : Ctx α ε} {L : LCtx α} {A B e}
  (a : Term.InS φ Γ ⟨(Ty.prod A B), e⟩) (t : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L) : InS φ Γ L
  := ⟨Region.let2 a t, Wf.let2 a.prop t.prop⟩

@[simp]
theorem InS.coe_let2 {Γ : Ctx α ε} {L : LCtx α} {A B e}
  (a : Term.InS φ Γ ⟨(Ty.prod A B), e⟩) (t : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L)
  : (t.let2 a : Region φ) = Region.let2 a t
  := rfl

def InS.case {Γ : Ctx α ε} {L : LCtx α} {A B e}
  (a : Term.InS φ Γ ⟨Ty.coprod A B, e⟩) (s : InS φ (⟨A, ⊥⟩::Γ) L) (t : InS φ (⟨B, ⊥⟩::Γ) L) : InS φ Γ L
  := ⟨Region.case a s t, Wf.case a.prop s.prop t.prop⟩

@[simp]
theorem InS.coe_case {Γ : Ctx α ε} {L : LCtx α} {A B e}
  (a : Term.InS φ Γ ⟨Ty.coprod A B, e⟩) (s : InS φ (⟨A, ⊥⟩::Γ) L) (t : InS φ (⟨B, ⊥⟩::Γ) L)
  : (s.case a t : Region φ) = Region.case a s t
  := rfl

def InS.cfg {Γ : Ctx α ε} {L : LCtx α} (R : LCtx α) (dβ : InS φ Γ (R ++ L))
  (dG : ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : InS φ Γ L
  := ⟨Region.cfg dβ.1 R.length (λi => (dG i).1), Wf.cfg R.length R rfl dβ.2 (λi => (dG i).2)⟩

@[simp]
theorem InS.coe_cfg {Γ : Ctx α ε} {L : LCtx α} (R : LCtx α) (dβ : InS φ Γ (R ++ L))
  (dG : ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : (InS.cfg R dβ dG : Region φ) = Region.cfg dβ R.length (λi => (dG i))
  := rfl

def InS.cfg' {Γ : Ctx α ε} {L : LCtx α} (n) (R : LCtx α)
  (hR : R.length = n) (dβ : InS φ Γ (R ++ L))
  (dG : ∀i : Fin n, InS φ (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L))
  : InS φ Γ L
  := ⟨Region.cfg dβ.1 n (λi => (dG i).1), Wf.cfg n R hR dβ.2 (λi => (dG i).2)⟩

@[simp]
theorem InS.coe_cfg' {Γ : Ctx α ε} {L : LCtx α} (n) (R : LCtx α)
  (hR : R.length = n) (dβ : InS φ Γ (R ++ L))
  (dG : ∀i : Fin n, InS φ (⟨R.get (i.cast hR.symm), ⊥⟩::Γ) (R ++ L))
  : (InS.cfg' n R hR dβ dG : Region φ) = Region.cfg dβ n (λi => (dG i))
  := rfl

theorem InS.coe_update {ι : Type _} [DecidableEq ι] {Γ : ι → Ctx α ε} {L : ι → LCtx α}
  {G : (i : ι) → InS φ (Γ i) (L i)} {i : ι} {g' : InS φ (Γ i) (L i)}
  : (λk => (Function.update G i g' k : Region φ)) = Function.update (λi => (G i : Region φ)) i g'
  := by funext k; simp only [Function.update]; split
        case isTrue h => cases h; rfl
        case isFalse h => rfl

def InS.ccfg {Γ : Ctx α ε} {L D : LCtx α} (R : LCtx α) (dβ : InS φ Γ D) (hD : D = R ++ L)
  (dG : ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : InS φ Γ L := InS.cfg R (dβ.cast rfl hD) dG

@[simp]
theorem InS.coe_ccfg {Γ : Ctx α ε} {L D : LCtx α} (R : LCtx α) (dβ : InS φ Γ D) (hD : D = R ++ L)
  (dG : ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : (InS.ccfg R dβ hD dG : Region φ) = (InS.cfg R (dβ.cast rfl hD) dG : Region φ)
  := rfl

theorem InS.ccfg_rfl {Γ : Ctx α ε} {L : LCtx α} (R : LCtx α) (dβ : InS φ Γ (R ++ L))
  (dG : ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L))
  : ccfg R dβ rfl dG = cfg R dβ dG := rfl

theorem InS.induction
  {motive : (Γ : Ctx α ε) → (L : LCtx α) → InS φ Γ L → Prop}
  (br : ∀{Γ L A} (ℓ) (a : Term.InS φ Γ ⟨A, ⊥⟩) (hℓ : L.Trg ℓ A), motive Γ L (InS.br ℓ a hℓ))
  (let1 : ∀{Γ L A e} (a : Term.InS φ Γ ⟨A, e⟩) (t : InS φ (⟨A, ⊥⟩::Γ) L),
    motive _ _ t → motive Γ L (InS.let1 a t))
  (let2 : ∀{Γ L A B e} (a : Term.InS φ Γ ⟨Ty.prod A B, e⟩) (t : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L),
    motive _ _ t → motive Γ L (InS.let2 a t))
  (case : ∀{Γ L A B e} (a : Term.InS φ Γ ⟨Ty.coprod A B, e⟩)
    (s : InS φ (⟨A, ⊥⟩::Γ) L) (t : InS φ (⟨B, ⊥⟩::Γ) L),
    motive _ _ s → motive _ _ t → motive Γ L (InS.case a s t))
  (cfg : ∀{Γ L} (R)
    (dβ : InS φ Γ (R ++ L))
    (dG : ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)),
    motive _ _ dβ → (∀i, motive _ _ (dG i)) → motive Γ L (InS.cfg R dβ dG))
  {Γ L} : (h : InS φ Γ L) → motive _ _ h
  | ⟨r, hr⟩ => by induction hr with
  | br hℓ ha => exact br _ ⟨_, ha⟩ hℓ
  | let1 ha hr Ir => exact let1 ⟨_, ha⟩ ⟨_, hr⟩ Ir
  | let2 ha hr Ir => exact let2 ⟨_, ha⟩ ⟨_, hr⟩ Ir
  | case ha hl hr Il Ir => exact case ⟨_, ha⟩ ⟨_, hl⟩ ⟨_, hr⟩ Il Ir
  | cfg n R hR dβ dG Iβ IG =>
    cases hR
    simp only [Fin.cast_eq_self] at *
    exact cfg R ⟨_, dβ⟩ (λi => ⟨_, dG i⟩) Iβ IG

theorem InS.induction_ccfg
  {motive : (Γ : Ctx α ε) → (L : LCtx α) → InS φ Γ L → Prop}
  (br : ∀{Γ L A} (ℓ) (a : Term.InS φ Γ ⟨A, ⊥⟩) (hℓ : L.Trg ℓ A), motive Γ L (InS.br ℓ a hℓ))
  (let1 : ∀{Γ L A e} (a : Term.InS φ Γ ⟨A, e⟩) (t : InS φ (⟨A, ⊥⟩::Γ) L),
    motive _ _ t → motive Γ L (InS.let1 a t))
  (let2 : ∀{Γ L A B e} (a : Term.InS φ Γ ⟨Ty.prod A B, e⟩) (t : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) L),
    motive _ _ t → motive Γ L (InS.let2 a t))
  (case : ∀{Γ L A B e} (a : Term.InS φ Γ ⟨Ty.coprod A B, e⟩)
    (s : InS φ (⟨A, ⊥⟩::Γ) L) (t : InS φ (⟨B, ⊥⟩::Γ) L),
    motive _ _ s → motive _ _ t → motive Γ L (InS.case a s t))
  (ccfg : ∀{Γ L D} (R)
    (dβ : InS φ Γ D)
    (hD : D = R ++ L)
    (dG : ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::Γ) (R ++ L)),
    motive _ _ dβ → (∀i, motive _ _ (dG i)) → motive Γ L (InS.ccfg R dβ hD dG))
  {Γ L} : (h : InS φ Γ L) → motive _ _ h
  | ⟨r, hr⟩ => by induction hr with
  | br hℓ ha => exact br _ ⟨_, ha⟩ hℓ
  | let1 ha hr Ir => exact let1 ⟨_, ha⟩ ⟨_, hr⟩ Ir
  | let2 ha hr Ir => exact let2 ⟨_, ha⟩ ⟨_, hr⟩ Ir
  | case ha hl hr Il Ir => exact case ⟨_, ha⟩ ⟨_, hl⟩ ⟨_, hr⟩ Il Ir
  | cfg n R hR dβ dG Iβ IG =>
    cases hR
    simp only [Fin.cast_eq_self] at *
    exact ccfg R ⟨_, dβ⟩ rfl (λi => ⟨_, dG i⟩) Iβ IG

def InS.shf {Γ : Ctx α ε} {L : LCtx α} {R : LCtx α} {Y : Ty α}
  (d : InS φ Γ (R ++ (Y::L))) : InS φ Γ ((LCtx.shf_first R Y L)::(LCtx.shf_rest R Y L))
  := d.cast rfl LCtx.shf_eq

def InS.ushf {Γ : Ctx α ε} {L : LCtx α} {R : LCtx α} {Y : Ty α}
  (d : InS φ Γ ((LCtx.shf_first R Y L)::(LCtx.shf_rest R Y L))) : InS φ Γ (R ++ (Y::L))
  := d.cast rfl LCtx.shf_eq.symm

@[simp]
theorem InS.shf_ushf {Γ : Ctx α ε} {L : LCtx α} {R : LCtx α} {Y : Ty α}
  (d : InS φ Γ (R ++ (Y::L))) : d.shf.ushf = d
  := by cases d; rfl

@[simp]
theorem InS.ushf_shf {Γ : Ctx α ε} {L : LCtx α} {R : LCtx α} {Y : Ty α}
  (d : InS φ Γ ((LCtx.shf_first R Y L)::(LCtx.shf_rest R Y L))) : d.ushf.shf = d
  := by cases d; rfl

@[simp]
theorem InS.coe_shf {Γ : Ctx α ε} {L : LCtx α} {R : LCtx α} {Y : Ty α}
  (d : InS φ Γ (R ++ (Y::L))) : (d.shf : Region φ) = (d : Region φ)
  := rfl

@[simp]
theorem InS.coe_ushf {Γ : Ctx α ε} {L : LCtx α} {R : LCtx α} {Y : Ty α}
  (d : InS φ Γ ((LCtx.shf_first R Y L)::(LCtx.shf_rest R Y L)))
  : (d.ushf : Region φ) = (d : Region φ)
  := rfl

@[simp]
theorem InS.shf_inj {Γ : Ctx α ε} {L : LCtx α} {R : LCtx α} {Y : Ty α}
  {r r' : InS φ Γ (R ++ (Y::L))} : r.shf = r'.shf ↔ r = r'
  := cast_inj

@[simp]
theorem InS.ushf_inj {Γ : Ctx α ε} {L : LCtx α} {R : LCtx α} {Y : Ty α}
  {r r' : InS φ Γ ((LCtx.shf_first R Y L)::(LCtx.shf_rest R Y L))} : r.ushf = r'.ushf ↔ r = r'
  := cast_inj

theorem InS.arrow_induction
  {motive : (X : Ty α) → (Γ : Ctx α ε) → (Y : Ty α) → (L : LCtx α)
    → InS φ ((X, ⊥)::Γ) (Y::L) → Prop}
  (br : ∀{X Γ Y L A} (ℓ)
    (a : Term.InS φ ((X, ⊥)::Γ) ⟨A, ⊥⟩) (hℓ : LCtx.Trg (Y::L) ℓ A), motive X Γ Y L (InS.br ℓ a hℓ))
  (let1 : ∀{X Γ Y L A e} (a : Term.InS φ ((X, ⊥)::Γ) ⟨A, e⟩) (t : InS φ (⟨A, ⊥⟩::⟨X, ⊥⟩::Γ) (Y::L)),
    motive _ _ _ _ t → motive _ Γ _ L (InS.let1 a t))
  (let2 : ∀{X Γ Y L A B e}
    (a : Term.InS φ ((X, ⊥)::Γ) ⟨Ty.prod A B, e⟩) (t : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::⟨X, ⊥⟩::Γ) (Y::L)),
    motive _ _ _ _ t → motive _ Γ _ L (InS.let2 a t))
  (case : ∀{X Γ Y L A B e} (a : Term.InS φ ((X, ⊥)::Γ) ⟨Ty.coprod A B, e⟩)
    (s : InS φ (⟨A, ⊥⟩::⟨X, ⊥⟩::Γ) (Y::L)) (t : InS φ (⟨B, ⊥⟩::⟨X, ⊥⟩::Γ) (Y::L)),
    motive _ _ _ _ s → motive _ _ _ _ t → motive _ Γ _ L (InS.case a s t))
  (cfg : ∀{X Γ Y L} (R)
    (dβ : InS φ ((X, ⊥)::Γ) (R ++ (Y :: L)))
    (dG : ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::⟨X, ⊥⟩::Γ) (R ++ (Y :: L))),
    motive X Γ _ _ dβ.shf
    → (∀i, motive _ _ _ _ ((dG i).shf))
    → motive _ Γ _ L (InS.cfg R dβ dG))
  {X Γ Y L} : (h : InS φ ((X, ⊥)::Γ) (Y::L)) → motive _ _ _ _ h
  | ⟨r, hr⟩ => by
    let Γr := (X, ⊥)::Γ
    generalize hΓ' : Γr = Γ'
    have hΓ' : (X, ⊥)::Γ = Γ' := hΓ'
    let Lr := Y::L
    generalize hL' : Lr = L'
    have hL' : Y::L = L' := hL'
    rw [hΓ', hL'] at hr
    induction hr generalizing X Γ Y L with
    | br hℓ ha =>
      cases hΓ'
      cases hL'
      exact br _ ⟨_, ha⟩ hℓ
    | let1 ha hr Ir =>
      cases hΓ'
      cases hL'
      exact let1 ⟨_, ha⟩ ⟨_, hr⟩ (Ir hr rfl rfl rfl rfl)
    | let2 ha hr Ir =>
      cases hΓ'
      cases hL'
      exact let2 ⟨_, ha⟩ ⟨_, hr⟩ (Ir hr rfl rfl rfl rfl)
    | case ha hl hr Il Ir =>
      cases hΓ'
      cases hL'
      exact case ⟨_, ha⟩ ⟨_, hl⟩ ⟨_, hr⟩ (Il hl rfl rfl rfl rfl) (Ir hr rfl rfl rfl rfl)
    | cfg n R hR dβ dG Iβ IG =>
      cases hΓ'
      cases hL'
      cases hR
      simp only [Fin.cast_eq_self] at *
      apply cfg R ⟨_, dβ⟩ (λi => ⟨_, dG i⟩)
      exact Iβ (LCtx.shf_eq (α := α) ▸ dβ) rfl rfl
        LCtx.shf_eq.symm
        LCtx.shf_eq.symm
      intro i
      apply IG i (LCtx.shf_eq (α := α) ▸ dG i) rfl rfl
        LCtx.shf_eq.symm
        LCtx.shf_eq.symm

def InD (φ) [EffInstSet φ (Ty α) ε] (Γ : Ctx α ε) (L : LCtx α) : Type _
  := Σr : Region φ, r.WfD Γ L

def InD.toInS {Γ : Ctx α ε} {L : LCtx α} (r : InD φ Γ L) : InS φ Γ L
  := ⟨r.1, r.2.toWf⟩

def WfD.vwk {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} {L} {r : Region φ} (h : Γ.Wkn Δ ρ)
  : WfD Δ r L → WfD Γ (r.vwk ρ) L
  | br hL ha => br hL (ha.wk h)
  | case he hs ht => case (he.wk h) (hs.vwk h.slift) (ht.vwk h.slift)
  | let1 ha ht => let1 (ha.wk h) (ht.vwk h.slift)
  | let2 ha ht => let2 (ha.wk h) (ht.vwk h.sliftn₂)
  | cfg n R hR hr hG => cfg n R hR (hr.vwk h) (λi => (hG i).vwk h.slift)

-- def WfD.vwk_inv {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} {L} {r : Region φ} (h : Γ.EWkn Δ ρ)
--   (d: WfD Γ (r.vwk ρ) L) (hr : r.fvi ≤ Δ.length) : WfD Δ r L := match r, d with
--   | Region.br _ _, br hL ha => br hL (ha.wk_inv h hr)
--   | Region.case _ _ _, case he hs ht
--     => case (he.wk_inv h (fvi_case_le_disc hr))
--         (hs.vwk_inv h.lift (fvi_case_le_left hr))
--         (ht.vwk_inv h.lift (fvi_case_le_right hr))
--   | Region.let1 _ _, let1 ha ht
--     => let1 (ha.wk_inv h (fvi_let1_le_bind hr)) (ht.vwk_inv h.lift (fvi_let1_le_rest hr))
--   | Region.let2 _ _, let2 ha ht
--     => let2 (ha.wk_inv h (fvi_let2_le_bind hr)) (ht.vwk_inv h.liftn₂ (fvi_let2_le_rest hr))
--   | Region.cfg _ _ _,cfg n R hR dr hG => cfg n R hR (dr.vwk_inv h (fvi_cfg_le_entry hr))
--                                           (λi => (hG i).vwk_inv h.lift (fvi_cfg_le_blocks hr i))

theorem Wf.fvs {r : Region φ} (h : Wf Γ r L) : r.fvs ⊆ Set.Iio Γ.length
  := by induction h with
  | br _ ha => simp [ha.fvs]
  | case he hs ht Is It =>
    simp only [Region.fvs, Set.union_subset_iff, he.fvs, true_and]
    constructor <;>
    intro k <;>
    rw [Set.mem_liftFv] <;>
    intro hk <;>
    apply Nat.lt_of_succ_lt_succ
    exact Is hk
    exact It hk
  | let1 ha ht It =>
    simp only [Region.fvs, Set.union_subset_iff, ha.fvs, true_and]
    intro k
    rw [Set.mem_liftFv]
    exact λhk => Nat.lt_of_succ_lt_succ $ It hk
  | let2 ha ht It =>
    simp only [Region.fvs, Set.union_subset_iff, ha.fvs, true_and]
    intro k
    rw [Set.mem_liftnFv]
    exact λhk => Nat.lt_of_add_lt_add_right (n := 2) $ It hk
  | cfg n R hR hr hG Iβ IG =>
    simp only [Region.fvs, Set.union_subset_iff, Iβ, Set.iUnion_subset_iff, true_and]
    intro i k
    rw [Set.mem_liftFv]
    exact λhk => Nat.lt_of_succ_lt_succ $ IG _ hk

def WfD.vwk1 {Γ : Ctx α ε} {L} {r : Region φ} (dr : WfD (A::Γ) r L) : WfD (A::B::Γ) r.vwk1 L
  := dr.vwk Ctx.Wkn.wk1

def WfD.vwk0 {Γ : Ctx α ε} {L} {r : Region φ} (dr : WfD Γ r L)
  : WfD (A::Γ) (r.vwk Nat.succ) L
  := dr.vwk Ctx.Wkn.succ

def WfD.vwk_id {Γ Δ : Ctx α ε} {L} {r : Region φ} (h : Γ.Wkn Δ id)
  : WfD Δ r L → WfD Γ r L
  | br hL ha => br hL (ha.wk_id h)
  | case he hs ht => case (he.wk_id h) (hs.vwk_id h.slift_id) (ht.vwk_id h.slift_id)
  | let1 ha ht => let1 (ha.wk_id h) (ht.vwk_id h.slift_id)
  | let2 ha ht => let2 (ha.wk_id h) (ht.vwk_id (h.slift_id₂ _ _))
  | cfg n R hR hr hG => cfg n R hR (hr.vwk_id h) (λi => (hG i).vwk_id h.slift_id)

def WfD.lwk {Γ : Ctx α ε} {ρ : ℕ → ℕ} {L K : LCtx α} {r : Region φ} (h : L.Wkn K ρ)
  : WfD Γ r L → WfD Γ (r.lwk ρ) K
  | br hL ha => br (hL.wk h) ha
  | case he hs ht => case he (hs.lwk h) (ht.lwk h)
  | let1 ha ht => let1 ha (ht.lwk h)
  | let2 ha ht => let2 ha (ht.lwk h)
  | cfg n R hR hβ hG =>
    have trg_wk : (R ++ L).Wkn (R ++ K) (Nat.liftnWk n ρ) := hR ▸ h.liftn_append R
    cfg n R hR (hβ.lwk trg_wk) (λi => (hG i).lwk trg_wk)

theorem Wf.vwk {Γ Δ : Ctx α ε} {ρ : ℕ → ℕ} {L} {r : Region φ} (h : Γ.Wkn Δ ρ)
  (d : Wf Δ r L) : Wf Γ (r.vwk ρ) L
  := have ⟨d⟩ := d.nonempty; (d.vwk h).toWf

theorem Wf.vwk_id {Γ Δ : Ctx α ε} {L} {r : Region φ} (h : Γ.Wkn Δ id)
  (d : Wf Δ r L) : Wf Γ r L
  := have ⟨d⟩ := d.nonempty; (d.vwk_id h).toWf

theorem Wf.wk0 {Γ : Ctx α ε} {L} {r : Region φ} (d : Wf Γ r L) : Wf (A::Γ) r.vwk0 L
  := d.vwk Ctx.Wkn.succ

theorem Wf.vwk1 {Γ : Ctx α ε} {L} {r : Region φ} (d : Wf (A::Γ) r L) : Wf (A::B::Γ) r.vwk1 L
  := d.vwk Ctx.Wkn.wk1

theorem Wf.lwk {Γ : Ctx α ε} {ρ : ℕ → ℕ} {L K} {r : Region φ} (h : L.Wkn K ρ)
  (d : Wf Γ r L) : Wf Γ (r.lwk ρ) K
  := have ⟨d⟩ := d.nonempty; (d.lwk h).toWf

theorem Wf.lwk_id {Γ : Ctx α ε} {L} {r : Region φ} (h : L.Wkn K id)
  (d : Wf Γ r L) : Wf Γ r K
  := r.lwk_id ▸ d.lwk h

theorem Wf.extend {Γ : Ctx α ε} {L} {r : Region φ} (d : Wf Γ r L) : Wf Γ r (L ++ R)
  := d.lwk_id LCtx.Wkn.id_right_append

theorem Wf.lwk0 {Γ : Ctx α ε} {L} {r : Region φ} (d : Wf Γ r L) : Wf Γ r.lwk0 (head::L)
  := d.lwk LCtx.Wkn.succ

theorem Wf.lwk1 {Γ : Ctx α ε} {L} {r : Region φ} (d : Wf Γ r (head::L))
  : Wf Γ r.lwk1 (head::inserted::L)
  := d.lwk LCtx.Wkn.wk1

theorem Wf.fls {r : Region φ} (h : Wf Γ r L) : r.fls ⊆ Set.Iio L.length
  := by induction h with
  | br hℓ => simp [hℓ.length]
  | cfg _ _ hR _  _ Iβ IG =>
    simp only [BinSyntax.Region.fls, Set.union_subset_iff, Set.iUnion_subset_iff]
    constructor
    · intro x
      simp only [Set.mem_liftnFv, Set.mem_Iio]
      intro hx
      have hx' := Iβ hx
      simp only [List.length_append, hR, Set.mem_Iio] at hx'
      omega
    · intro i x
      simp only [Set.mem_liftnFv, Set.mem_Iio]
      intro hx
      have hx' := IG i hx
      simp only [List.length_append, hR, Set.mem_Iio] at hx'
      omega
  | _ => simp [*]

def InS.vwk {Γ Δ : Ctx α ε} (ρ : Γ.InS Δ) {L} (r : InS φ Δ L) : InS φ Γ L
  := ⟨(r : Region φ).vwk ρ, r.prop.vwk ρ.prop⟩

@[simp]
theorem InS.vwk_br {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ} {L} {ℓ} {a : Term.InS φ Δ ⟨A, ⊥⟩}
  {hℓ : LCtx.Trg L ℓ A}
  : (InS.br ℓ a hℓ).vwk ρ = InS.br ℓ (a.wk ρ) hℓ
  := rfl

@[simp]
theorem InS.vwk_let1 {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ} {L} {A e}
  {a : Term.InS φ Δ ⟨A, e⟩} {t : InS φ (⟨A, ⊥⟩::Δ) L}
  : (t.let1 a).vwk ρ = (t.vwk ρ.slift).let1 (a.wk ρ) := rfl

@[simp]
theorem InS.vwk_let2 {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ} {L} {A B e}
  {a : Term.InS φ Δ ⟨(Ty.prod A B), e⟩} {t : InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Δ) L}
  : (t.let2 a).vwk ρ = (t.vwk ρ.sliftn₂).let2 (a.wk ρ) := rfl

@[simp]
theorem InS.vwk_case {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ} {L} {A B e}
  {a : Term.InS φ Δ ⟨Ty.coprod A B, e⟩} {s : InS φ (⟨A, ⊥⟩::Δ) L} {t : InS φ (⟨B, ⊥⟩::Δ) L}
  : (s.case a t).vwk ρ = (s.vwk ρ.slift).case (a.wk ρ) (t.vwk ρ.slift) := rfl

@[simp]
theorem InS.vwk_cfg {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ} {L} {R : LCtx α}
  {dβ : InS φ Δ (R ++ L)}
  {dG : ∀i : Fin R.length, InS φ (⟨R.get i, ⊥⟩::Δ) (R ++ L)}
  : (InS.cfg R dβ dG).vwk ρ = InS.cfg R (dβ.vwk ρ) (λi => (dG i).vwk ρ.slift) := rfl

theorem InS.vwk_equiv {Γ Δ : Ctx α ε} {ρ ρ' : Γ.InS Δ} {L} (r : InS φ Δ L) (h : ρ ≈ ρ')
  : r.vwk ρ = r.vwk ρ'
  := by induction r using InS.induction generalizing Γ with
  | br ℓ a hℓ => simp [a.wk_equiv h]
  | let1 a r Ir => simp [a.wk_equiv h, Ir (Ctx.InS.slift_congr h)]
  | let2 a r Ir => simp [a.wk_equiv h, Ir (Ctx.InS.sliftn₂_congr h)]
  | case a s t Is It => simp [a.wk_equiv h, Is (Ctx.InS.slift_congr h), It (Ctx.InS.slift_congr h)]
  | cfg R dβ dG Iβ IG =>
    simp only [vwk_cfg, Iβ h, List.get_eq_getElem]
    congr
    funext i
    simp [IG i (Ctx.InS.slift_congr h)]

@[simp]
theorem InS.coe_vwk {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ} {L} {r : InS φ Δ L}
  : (r.vwk ρ : Region φ) = (r : Region φ).vwk ρ := rfl

theorem InS.vwk_vwk {Γ Δ Ξ : Ctx α ε} {ρ : Γ.InS Δ} {σ : Δ.InS Ξ}
  {L} {r : InS φ Ξ L}
  : (r.vwk σ).vwk ρ = r.vwk (ρ.comp σ) := by
  cases r; simp [vwk, Region.vwk_vwk]

def InS.vwk_id {Γ Δ : Ctx α ε} (h : Γ.Wkn Δ id) {L} (r : InS φ Δ L) : InS φ Γ L
  := ⟨r, r.2.vwk_id h⟩

@[simp]
theorem InS.coe_vwk_id {Γ Δ : Ctx α ε} {h : Γ.Wkn Δ id} {L} {r : InS φ Δ L}
  : (r.vwk_id h : Region φ) = (r : Region φ) := rfl

theorem InS.vwk_id_eq_vwk {Γ Δ : Ctx α ε} {h : Γ.Wkn Δ id} {L} {r : InS φ Δ L}
  : r.vwk_id h = r.vwk ⟨id, h⟩ := by simp [vwk, vwk_id]

-- TODO: Ctx.Wkn.comp_id

theorem InS.vwk_vwk_id {Γ Δ Ξ : Ctx α ε} {ρ : Γ.InS Δ} {h : Δ.Wkn Ξ id}
  {L} {r : InS φ Ξ L}
  : (r.vwk_id h).vwk ρ = r.vwk ⟨ρ, ρ.prop.comp h⟩ := by
  cases r; simp [vwk, vwk_id, vwk_vwk]

theorem InS.vwk_id_vwk {Γ Δ Ξ : Ctx α ε} {h : Γ.Wkn Δ id} {ρ : Δ.InS Ξ}
  {L} {r : InS φ Ξ L}
  : (r.vwk ρ).vwk_id h = r.vwk ⟨ρ, h.comp ρ.prop⟩ := by
  cases r; simp [vwk, vwk_id, vwk_vwk]

def InS.vwk0 {Γ : Ctx α ε} {L} (r : InS φ Γ L) : InS φ (head::Γ) L
  := r.vwk ⟨Nat.succ, Ctx.Wkn.succ⟩

@[simp]
theorem InS.coe_vwk0 {Γ : Ctx α ε} (r : InS φ Γ L)
  : (r.vwk0 (head := head) : Region φ) = r.vwk0 (head := head) := rfl

def InS.vwk1 {Γ : Ctx α ε} {L} (r : InS φ (head::Γ) L) : InS φ (head::inserted::Γ) L
  := r.vwk Ctx.InS.wk1

@[simp]
theorem InS.coe_vwk1 {Γ : Ctx α ε} {L} {r : InS φ (head::Γ) L}
  : (r.vwk1 (inserted := inserted) : Region φ) = (r : Region φ).vwk1 := rfl

def InS.vwk2 {Γ : Ctx α ε} {L} (r : InS φ (left::right::Γ) L) : InS φ (left::right::inserted::Γ) L
  := r.vwk Ctx.InS.wk2

@[simp]
theorem InS.coe_vwk2 {Γ : Ctx α ε} {L} {r : InS φ (left::right::Γ) L}
  : (r.vwk2 (inserted := inserted) : Region φ) = (r : Region φ).vwk2 := rfl

@[simp]
theorem InS.vwk1_br {Γ : Ctx α ε} {L : LCtx α}
  {ℓ} {a : Term.InS φ (⟨head, ⊥⟩::Γ) ⟨A, ⊥⟩} {hℓ : L.Trg ℓ A}
  : (InS.br ℓ a hℓ).vwk1 (inserted := inserted) = InS.br (φ := φ) ℓ a.wk1 hℓ
  := rfl

@[simp]
theorem InS.vwk1_let1 {Γ : Ctx α ε} {L : LCtx α} {A e}
  {a : Term.InS φ (⟨head, ⊥⟩::Γ) ⟨A, e⟩} {t : InS φ (⟨A, ⊥⟩::⟨head, ⊥⟩::Γ) L}
  : (t.let1 a).vwk1 (inserted := inserted) = let1 a.wk1 t.vwk2
  := by ext; simp [Region.vwk1, Nat.liftnWk_two, Region.vwk2, Term.wk1]

def InS.vwk3 {Γ : Ctx α ε} {L} (r : InS φ (left::middle::right::Γ) L)
  : InS φ (left::middle::right::inserted::Γ) L
  := r.vwk Ctx.InS.wk3

@[simp]
theorem InS.coe_vwk3 {Γ : Ctx α ε} {L} {r : InS φ (left::middle::right::Γ) L}
  : (r.vwk3 (inserted := inserted) : Region φ) = (r : Region φ).vwk3 := rfl

def InS.vswap01 {Γ : Ctx α ε} {L} (r : InS φ (left::right::Γ) L) : InS φ (right::left::Γ) L
  := r.vwk Ctx.InS.swap01

@[simp]
theorem InS.coe_vswap01 {Γ : Ctx α ε} {L} {r : InS φ (left::right::Γ) L}
  : (r.vswap01 : Region φ) = r.vswap01 := rfl

def InS.vswap02 {Γ : Ctx α ε} {L} (r : InS φ (left::mid::right::Γ) L)
  : InS φ (mid::right::left::Γ) L
  := r.vwk Ctx.InS.swap02

@[simp]
theorem InS.coe_vswap02 {Γ : Ctx α ε} {L} {r : InS φ (left::mid::right::Γ) L}
  : (r.vswap02 : Region φ) = r.vswap02 := rfl

def InS.vswap03 {Γ : Ctx α ε} {L} (r : InS φ (first::second::third::fourth::Γ) L)
  : InS φ (second::third::fourth::first::Γ) L
  := r.vwk Ctx.InS.swap03

@[simp]
theorem InS.coe_vswap03 {Γ : Ctx α ε} {L} {r : InS φ (first::second::third::fourth::Γ) L}
  : (r.vswap03 : Region φ) = r.vswap03 := rfl

def InS.lwk {Γ : Ctx α ε} (ρ : L.InS K) (r : InS φ Γ L) : InS φ Γ K
  := ⟨(r : Region φ).lwk ρ, r.2.lwk ρ.prop⟩

def InS.lwk0 {Γ : Ctx α ε} {L} (r : InS φ Γ L) : InS φ Γ (head::L)
  := r.lwk LCtx.InS.wk0

def InS.lwk1 {Γ : Ctx α ε} (r : InS φ Γ (head::L)) : InS φ Γ (head::inserted::L)
  := r.lwk LCtx.InS.wk1

theorem InS.lwk_equiv {Γ : Ctx α ε} {ρ ρ' : L.InS K} (r : InS φ Γ L) (h : ρ ≈ ρ')
  : r.lwk ρ = r.lwk ρ' := by
  ext; apply Region.lwk_eqOn_fls
  apply Set.EqOn.mono r.prop.fls h

@[simp]
theorem InS.coe_lwk {Γ : Ctx α ε} {ρ : L.InS K} {r : InS φ Γ L}
  : (r.lwk ρ : Region φ) = (r : Region φ).lwk ρ := rfl

@[simp]
theorem InS.coe_lwk0 {Γ : Ctx α ε} {L} {r : InS φ Γ L}
  : (r.lwk0 (head := head) : Region φ) = (r : Region φ).lwk0 := rfl

@[simp]
theorem InS.coe_lwk1 {Γ : Ctx α ε} {L} {r : InS φ Γ (head::L)}
  : (r.lwk1 (inserted := inserted) : Region φ) = (r : Region φ).lwk1 := rfl

theorem InS.lwk_lwk {Γ : Ctx α ε} {L K J}
  {ρ : L.InS K} {σ : K.InS J}
  {r : InS φ Γ L}
  : (r.lwk ρ).lwk σ = r.lwk (σ.comp ρ) := by
  cases r; simp [lwk, Region.lwk_lwk]

theorem InS.lwk_vwk {Γ Δ : Ctx α ε} {L K} {ρ : Γ.InS Δ} {σ : L.InS K}
  {r : InS φ Δ L}
  : (r.vwk ρ).lwk σ = (r.lwk σ).vwk ρ := by
  cases r; simp [lwk, vwk, Region.lwk_vwk]

theorem InS.vwk_lwk {Γ Δ : Ctx α ε} {L K} {ρ : Γ.InS Δ} {σ : L.InS K}
  {r : InS φ Δ L}
  : (r.lwk σ).vwk ρ = (r.vwk ρ).lwk σ := by
  cases r; simp [lwk, vwk, Region.lwk_vwk]

theorem InS.lwk_vwk1 {Γ : Ctx α ε} {L K} {ρ : L.InS K} {r : InS φ (head::Γ) L}
  : (r.vwk1 (inserted := inserted)).lwk ρ = (r.lwk ρ).vwk1 := by
  rw [vwk1, lwk_vwk]; rfl

theorem InS.vwk1_lwk {Γ : Ctx α ε} {L K} {ρ : L.InS K} {r : InS φ (head::Γ) L}
  : (r.lwk ρ).vwk1 = (r.vwk1 (inserted := inserted)).lwk ρ := by rw [lwk_vwk1]

def InS.lwk_id {Γ : Ctx α ε} {L} (h : L.Wkn K id) (r : InS φ Γ L) : InS φ Γ K
  := ⟨r, r.2.lwk_id h⟩

@[simp]
theorem InS.coe_lwk_id {Γ : Ctx α ε} {L} {r : InS φ Γ L} {h : L.Wkn K id}
  : (r.lwk_id h : Region φ) = (r : Region φ) := rfl

theorem InS.lwk_id_eq_lwk {Γ : Ctx α ε} {L K} {r : InS φ Γ L} {h : L.Wkn K id}
  : r.lwk_id h = r.lwk ⟨id, h⟩ := by simp [lwk, lwk_id]

theorem InS.lwk_id_lwk {Γ : Ctx α ε} {L K J} {h : L.Wkn K id} {ρ : K.InS J}
  {r : InS φ Γ L}
  : (r.lwk_id h).lwk ρ = r.lwk ⟨ρ, (ρ.prop.comp h)⟩ := by
  cases r; simp [lwk, lwk_id, lwk_lwk]

theorem InS.lwk_lwk_id {Γ : Ctx α ε} {L K J} {ρ : L.InS K} {h : K.Wkn J id}
  {r : InS φ Γ L}
  : (r.lwk ρ).lwk_id h = r.lwk ⟨ρ, (h.comp ρ.prop)⟩ := by
  cases r; simp [lwk, lwk_id, lwk_lwk]

abbrev InS.extend {Γ : Ctx α ε} {L} (r : InS φ Γ L) : InS φ Γ (L ++ R)
  := r.lwk_id LCtx.Wkn.id_right_append

theorem InS.shf_vwk {Γ Δ : Ctx α ε} {L R : LCtx α} {Y : Ty α}
  {ρ : Ctx.InS Γ Δ}
  {d : InS φ Δ (R ++ (Y::L))}
  : (d.vwk ρ).shf = d.shf.vwk ρ := rfl

theorem InS.vwk_shf {Γ Δ : Ctx α ε} {L R : LCtx α} {Y : Ty α}
  {ρ : Ctx.InS Γ Δ}
  {d : InS φ Δ (R ++ (Y::L))}
  : d.shf.vwk ρ = (d.vwk ρ).shf := rfl

theorem InS.shf_vwk1 {Γ : Ctx α ε} {L : LCtx α} {R : LCtx α} {Y : Ty α}
  {d : InS φ (head::Γ) (R ++ (Y::L))}
  : (d.vwk1).shf = d.shf.vwk1 (inserted := inserted) := rfl

theorem InS.vwk1_shf {Γ : Ctx α ε} {L : LCtx α} {R : LCtx α} {Y : Ty α}
  {d : InS φ (head::Γ) (R ++ (Y::L))}
  : d.shf.vwk1 (inserted := inserted) = (d.vwk1).shf := rfl

theorem InS.ushf_vwk {Γ Δ : Ctx α ε} {L R : LCtx α} {Y : Ty α}
  {ρ : Ctx.InS Γ Δ}
  {d : InS φ Δ ((LCtx.shf_first R Y L)::(LCtx.shf_rest R Y L))}
  : (d.vwk ρ).ushf = d.ushf.vwk ρ := rfl

theorem InS.vwk_ushf {Γ Δ : Ctx α ε} {L R : LCtx α} {Y : Ty α}
  {ρ : Ctx.InS Γ Δ}
  {d : InS φ Δ ((LCtx.shf_first R Y L)::(LCtx.shf_rest R Y L))}
  : d.ushf.vwk ρ = (d.vwk ρ).ushf := rfl

theorem InS.ushf_vwk1 {Γ : Ctx α ε} {L : LCtx α} {R : LCtx α} {Y : Ty α}
  {d : InS φ (head::Γ) ((LCtx.shf_first R Y L)::(LCtx.shf_rest R Y L))}
  : (d.vwk1 (inserted := inserted)).ushf = d.ushf.vwk1 := rfl

theorem InS.vwk1_ushf {Γ : Ctx α ε} {L : LCtx α} {R : LCtx α} {Y : Ty α}
  {d : InS φ (head::Γ) ((LCtx.shf_first R Y L)::(LCtx.shf_rest R Y L))}
  : d.ushf.vwk1 = (d.vwk1 (inserted := inserted)).ushf := rfl

-- theorem InS.lwk1_shf {Γ : Ctx α ε} {L : LCtx α}
--   {d : InS φ Γ (head::(R ++ (Y::L)))}
--   : (d.lwk1 (inserted := inserted)).shf (R := (head::inserted::R))
--   = d.shf.lwk1 (inserted := inserted) := sorry

-- TODO: normalize Region to TRegion; type preservation

-- TODO: normalize TRegion to BBRegion; type preservation
