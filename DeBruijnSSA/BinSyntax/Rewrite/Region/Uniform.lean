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
  | uniform {e : Term φ} {r s : Region φ}
    : e.Wf (⟨A, ⊥⟩::Γ) (B, ⊥)
    → r.Wf (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ((C.coprod B)::L)
    → s.Wf (⟨A, ⊥⟩::Γ) ((C.coprod A)::L)
    → Uniform P (⟨A, ⊥⟩::Γ)
      ((C.coprod B)::L)
      (r.vsubst e.subst0)
      (s.lsubst (ret (sum Term.nil e)).lsubst0)
    → Uniform P (⟨A, ⊥⟩::Γ) (C::L) (r.fixpoint.vsubst e.subst0) s.fixpoint
  | refl : r.Wf Γ L → Uniform P Γ L r r
  -- TODO: this should be a theorem, later
  | let1_equiv {a a' : Term φ} {r : Region φ}
    : Term.Uniform Term.TStep Γ ⟨A, e⟩ a a'
    → r.Wf (⟨A, ⊥⟩::Γ) L
    → Uniform P Γ L (Region.let1 a r) (Region.let1 a' r)
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
  | uniform de dr ds => exact ⟨Wf.vsubst de.subst0 dr.fixpoint, ds.fixpoint⟩
  | refl h => exact ⟨h, h⟩
  | let1_equiv da dr => exact ⟨dr.let1 (da.left TStep.wf),
                               dr.let1 (da.right TStep.wf)⟩
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

theorem Uniform.vwk {P Q : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ Δ L r r'}
  (toVwk : ∀{Γ Δ L ρ r r'}, Γ.Wkn Δ ρ → P Δ L r r' → Q Γ L (r.vwk ρ) (r'.vwk ρ))
  (hρ : Γ.Wkn Δ ρ)
  (p : (Uniform P Δ L) r r') : Uniform Q Γ L (r.vwk ρ) (r'.vwk ρ)
  := by induction p with
  | rel h => exact rel $ toVwk hρ h
  | symm _ I => exact (I hρ).symm
  | trans _ _ Il Ir => exact (Il hρ).trans (Ir hρ)
  | refl h => exact refl (h.vwk hρ)
  | _ => sorry

theorem Uniform.lwk {P Q : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ L K r r'}
  (toLwk : ∀{Γ L K ρ r r'}, L.Wkn K ρ → P Γ L r r' → Q Γ K (r.lwk ρ) (r'.lwk ρ))
  (hρ : L.Wkn K ρ)
  (p : (Uniform P Γ L) r r') : Uniform Q Γ K (r.lwk ρ) (r'.lwk ρ)
  := by induction p with
  | rel h => exact rel $ toLwk hρ h
  | symm _ I => exact (I hρ).symm
  | trans _ _ Il Ir => exact (Il hρ).trans (Ir hρ)
  | refl h => exact refl (h.lwk hρ)
  | _ => sorry

theorem Uniform.vsubst {P Q : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ Δ L r r'}
  (toVsubst : ∀{Γ Δ L σ r r'}, σ.Wf Γ Δ → P Δ L r r' → Q Γ L (r.vsubst σ) (r'.vsubst σ))
  (hσ : σ.Wf Γ Δ)
  (p : (Uniform P Δ L) r r') : Uniform Q Γ L (r.vsubst σ) (r'.vsubst σ)
  := by induction p with
  | rel h => exact rel $ toVsubst hσ h
  | symm _ I => exact (I hσ).symm
  | trans _ _ Il Ir => exact (Il hσ).trans (Ir hσ)
  | refl h => exact refl (h.vsubst hσ)
  | _ => sorry

theorem Uniform.lsubst {P Q : Ctx α ε → LCtx α → Region φ → Region φ → Prop} {Γ L K r r'}
  (toLsubst : ∀{Γ L K σ r r'}, σ.Wf Γ L K → P Γ L r r' → Q Γ K (r.lsubst σ) (r'.lsubst σ))
  (hσ : σ.Wf Γ L K)
  (p : (Uniform P Γ L) r r') : Uniform Q Γ K (r.lsubst σ) (r'.lsubst σ)
  := by induction p with
  | rel h => exact rel $ toLsubst hσ h
  | symm _ I => exact (I hσ).symm
  | trans _ _ Il Ir => exact (Il hσ).trans (Ir hσ)
  | refl h => exact refl (h.lsubst hσ)
  | _ => sorry

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
