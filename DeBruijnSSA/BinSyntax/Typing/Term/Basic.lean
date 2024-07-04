import Discretion.Wk.List
import Discretion.Basic
import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Fv.Basic
import DeBruijnSSA.BinSyntax.Syntax.Effect.Definitions

import DeBruijnSSA.BinSyntax.Typing.Ctx

namespace BinSyntax

section Basic

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]

/-- A well-formed term -/
inductive Term.Wf : Ctx α ε → Term φ → Ty α × ε → Prop
  | var : Γ.Var n V → Wf Γ (var n) V
  | op : Φ.EFn f A B e → Wf Γ a ⟨A, e⟩ → Wf Γ (op f a) ⟨B, e⟩
  | let1 : Wf Γ a ⟨A, e⟩ → Wf (⟨A, ⊥⟩::Γ) b ⟨B, e⟩ → Wf Γ (let1 a b) ⟨B, e⟩
  | pair : Wf Γ a ⟨A, e⟩ → Wf Γ b ⟨B, e⟩ → Wf Γ (pair a b) ⟨(Ty.prod A B), e⟩
  | let2 : Wf Γ a ⟨A.prod B, e⟩ → Wf (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) c ⟨C, e⟩ → Wf Γ (let2 a c) ⟨C, e⟩
  | inl : Wf Γ a ⟨A, e⟩ → Wf Γ (inl a) ⟨(Ty.coprod A B), e⟩
  | inr : Wf Γ b ⟨B, e⟩ → Wf Γ (inr b) ⟨(Ty.coprod A B), e⟩
  | case : Wf Γ a ⟨Ty.coprod A B, e⟩
    → Wf (⟨A, ⊥⟩::Γ) l ⟨C, e⟩
    → Wf (⟨B, ⊥⟩::Γ) r ⟨C, e⟩
    → Wf Γ (case a l r) ⟨C, e⟩
  | abort : Wf Γ a ⟨Ty.empty, e⟩ → Wf Γ (abort a) ⟨A, e⟩
  | unit (e) : Wf Γ unit ⟨Ty.unit, e⟩

theorem Term.Wf.to_var {Γ : Ctx α ε} {n V} (h : Wf Γ (@Term.var φ n) V)
  : Γ.Var n V := by cases h; assumption

theorem Term.Wf.to_fn' {Γ : Ctx α ε} {a : Term φ}
  (h : Wf Γ (Term.op f a) V)
  (hA : A ≤ Φ.src f)
  (hB : V.1 ≤ B)
  (he : V.2 ≤ e)
  : Φ.EFn f A B e := by cases h with | op hf => exact ⟨⟨hA, hf.trg.trans hB⟩, hf.effect.trans he⟩

theorem Term.Wf.to_fn {Γ : Ctx α ε} {a : Term φ} (h : Wf Γ (Term.op f a) V)
  : Φ.EFn f (Φ.src f) V.1 V.2 := h.to_fn' (le_refl _) (le_refl _) (le_refl _)

theorem Term.Wf.wk_res {Γ : Ctx α ε} {a : Term φ} {V V'} (h : Wf Γ a V) (hV : V ≤ V') : Wf Γ a V'
  := by induction h generalizing V' with
  | var dv =>
    constructor
    exact ⟨dv.length, dv.getElem.trans hV⟩
  | op hf _ I =>
    cases V'
    constructor
    exact ⟨⟨hf.src, hf.trg.trans hV.left⟩, hf.effect.trans hV.right⟩
    exact I ⟨le_refl _, hV.right⟩
  | let1 => sorry
  | pair _ _ Il Ir =>
    cases V'
    cases hV.left
    constructor
    exact Il ⟨by assumption, hV.right⟩
    exact Ir ⟨by assumption, hV.right⟩
  | let2 => sorry
  | inl _ I =>
    cases V'
    cases hV.left
    constructor
    exact I ⟨by assumption, hV.right⟩
  | inr _ I =>
    cases V'
    cases hV.left
    constructor
    exact I ⟨by assumption, hV.right⟩
  | case => sorry
  | abort _ I =>
    cases V'
    constructor
    exact I ⟨le_refl _, hV.right⟩
  | unit =>
    cases V'
    cases hV.left
    constructor

theorem Term.Wf.to_op' {Γ : Ctx α ε} {a : Term φ}
  (h : Wf Γ (Term.op f a) V)
  (hV : ⟨Φ.src f, V.2⟩ ≤ V')
  : Wf Γ a V' := by cases h with | op hf ha => exact ha.wk_res ⟨hf.src.trans hV.left, hV.right⟩

theorem Term.Wf.to_op {Γ : Ctx α ε} {a : Term φ} {V} (h : Wf Γ (Term.op f a) V)
  : Wf Γ a ⟨Φ.src f, V.2⟩ := h.to_op' (le_refl _)

theorem Term.Wf.to_left {Γ : Ctx α ε} {a b : Term φ}
  (h : Wf Γ (Term.pair a b) ⟨Ty.prod A B, e⟩)
  : Wf Γ a ⟨A, e⟩ := by cases h with | pair ha _ => exact ha

theorem Term.Wf.to_right {Γ : Ctx α ε} {a b : Term φ}
  (h : Wf Γ (Term.pair a b) ⟨Ty.prod A B, e⟩)
  : Wf Γ b ⟨B, e⟩ := by cases h with | pair _ hb => exact hb

def Term.InS (φ) [EffInstSet φ (Ty α) ε] (Γ : Ctx α ε) (V : Ty α × ε) : Type _
  := {a : Term φ | a.Wf Γ V}

instance Term.inSCoe {Γ : Ctx α ε} {V} : CoeOut (Term.InS φ Γ V) (Term φ)
  := ⟨λt => t.val⟩

@[ext]
theorem Term.InS.ext {Γ : Ctx α ε} {V} {a b : Term.InS φ Γ V} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

def Term.InS.var {Γ : Ctx α ε} {V} (n) (h : Γ.Var n V) : Term.InS φ Γ V
  := ⟨Term.var n, Wf.var h⟩

@[simp]
theorem Term.InS.coe_var {Γ : Ctx α ε} {V} {n} (h : Γ.Var n V)
  : (Term.InS.var (φ := φ) n h : Term φ) = Term.var n
  := rfl

def Term.InS.op {Γ : Ctx α ε}
  (f) (hf : Φ.EFn f A B e) (a : Term.InS φ Γ ⟨A, e⟩) : Term.InS φ Γ ⟨B, e⟩
  := ⟨Term.op f a, Wf.op hf a.2⟩

@[simp]
theorem Term.InS.coe_op {Γ : Ctx α ε} {f} {hf : Φ.EFn f A B e} {a : Term.InS φ Γ ⟨A, e⟩}
  : (Term.InS.op f hf a : Term φ) = Term.op f a
  := rfl

def Term.InS.let1 {Γ : Ctx α ε}
  (a : Term.InS φ Γ ⟨A, e⟩) (b : Term.InS φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩) : Term.InS φ Γ ⟨B, e⟩
  := ⟨Term.let1 a b, Wf.let1 a.2 b.2⟩

@[simp]
theorem Term.InS.coe_let1 {Γ : Ctx α ε} {a : Term.InS φ Γ ⟨A, e⟩} {b : Term.InS φ (⟨A, ⊥⟩::Γ) ⟨B, e⟩}
  : (Term.InS.let1 a b : Term φ) = Term.let1 a b
  := rfl

def Term.InS.pair {Γ : Ctx α ε}
  (a : Term.InS φ Γ ⟨A, e⟩) (b : Term.InS φ Γ ⟨B, e⟩) : Term.InS φ Γ ⟨Ty.prod A B, e⟩
  := ⟨Term.pair a b, Wf.pair a.2 b.2⟩

@[simp]
theorem Term.InS.coe_pair {Γ : Ctx α ε} {a : Term.InS φ Γ ⟨A, e⟩} {b : Term.InS φ Γ ⟨B, e⟩}
  : (Term.InS.pair a b : Term φ) = Term.pair a b
  := rfl

def Term.InS.let2 {Γ : Ctx α ε}
  (a : Term.InS φ Γ ⟨A.prod B, e⟩) (c : Term.InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩) : Term.InS φ Γ ⟨C, e⟩
  := ⟨Term.let2 a c, Wf.let2 a.2 c.2⟩

@[simp]
theorem InS.coe_let2 {Γ : Ctx α ε} {a : Term.InS φ Γ ⟨A.prod B, e⟩}
  {c : Term.InS φ (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) ⟨C, e⟩}
  : (a.let2 c : Term φ) = Term.let2 a c
  := rfl

def Term.InS.inl {Γ : Ctx α ε}
  (a : Term.InS φ Γ ⟨left, e⟩) : Term.InS φ Γ ⟨Ty.coprod left right, e⟩
  := ⟨Term.inl a, Wf.inl a.2⟩

@[simp]
theorem Term.InS.coe_inl {Γ : Ctx α ε} {a : Term.InS φ Γ ⟨left, e⟩}
  : (a.inl (right := right) : Term φ) = Term.inl a
  := rfl

def Term.InS.inr {Γ : Ctx α ε}
  (b : Term.InS φ Γ ⟨right, e⟩) : Term.InS φ Γ ⟨Ty.coprod left right, e⟩
  := ⟨Term.inr b, Wf.inr b.2⟩

@[simp]
theorem Term.InS.coe_inr {Γ : Ctx α ε} {b : Term.InS φ Γ ⟨right, e⟩}
  : (b.inr (left := left) : Term φ) = Term.inr b
  := rfl

def Term.InS.case {Γ : Ctx α ε}
  (a : Term.InS φ Γ ⟨Ty.coprod left right, e⟩)
  (l : Term.InS φ (⟨left, ⊥⟩::Γ) ⟨C, e⟩)
  (r : Term.InS φ (⟨right, ⊥⟩::Γ) ⟨C, e⟩) : Term.InS φ Γ ⟨C, e⟩
  := ⟨Term.case a l r, Wf.case a.2 l.2 r.2⟩

@[simp]
theorem Term.InS.coe_case {Γ : Ctx α ε} {a : Term.InS φ Γ ⟨Ty.coprod left right, e⟩}
  {l : Term.InS φ (⟨left, ⊥⟩::Γ) ⟨C, e⟩} {r : Term.InS φ (⟨right, ⊥⟩::Γ) ⟨C, e⟩}
  : (a.case l r : Term φ) = Term.case a l r
  := rfl

def Term.InS.abort {Γ : Ctx α ε}
  (a : Term.InS φ Γ ⟨Ty.empty, e⟩) (tyOut) : Term.InS φ Γ ⟨tyOut, e⟩
  := ⟨Term.abort a, Wf.abort a.2⟩

@[simp]
theorem Term.InS.coe_abort {Γ : Ctx α ε} {a : Term.InS φ Γ ⟨Ty.empty, e⟩}
  : (a.abort tyOut : Term φ) = Term.abort a
  := rfl

def Term.InS.unit {Γ : Ctx α ε} (e) : Term.InS φ Γ ⟨Ty.unit, e⟩
  := ⟨Term.unit, Wf.unit e⟩

@[simp]
theorem Term.InS.coe_unit {Γ : Ctx α ε} {e}
  : (Term.InS.unit (φ := φ) (Γ := Γ) e : Term φ) = Term.unit
  := rfl

/-- A derivation that a term is well-formed -/
inductive Term.WfD : Ctx α ε → Term φ → Ty α × ε → Type _
  | var : Γ.Var n V → WfD Γ (var n) V
  | op : Φ.EFn f A B e → WfD Γ a ⟨A, e⟩ → WfD Γ (op f a) ⟨B, e⟩
  | let1 : WfD Γ a ⟨A, e⟩ → WfD (⟨A, ⊥⟩::Γ) b ⟨B, e⟩ → WfD Γ (let1 a b) ⟨B, e⟩
  | pair : WfD Γ a ⟨A, e⟩ → WfD Γ b ⟨B, e⟩ → WfD Γ (pair a b) ⟨(Ty.prod A B), e⟩
  | let2 : WfD Γ a ⟨A.prod B, e⟩ → WfD (⟨B, ⊥⟩::⟨A, ⊥⟩::Γ) c ⟨C, e⟩ → WfD Γ (let2 a c) ⟨C, e⟩
  | inl : WfD Γ a ⟨A, e⟩ → WfD Γ (inl a) ⟨(Ty.coprod A B), e⟩
  | inr : WfD Γ b ⟨B, e⟩ → WfD Γ (inr b) ⟨(Ty.coprod A B), e⟩
  | case : WfD Γ a ⟨Ty.coprod A B, e⟩
    → WfD (⟨A, ⊥⟩::Γ) l ⟨C, e⟩
    → WfD (⟨B, ⊥⟩::Γ) r ⟨C, e⟩
    → WfD Γ (case a l r) ⟨C, e⟩
  | abort : WfD Γ a ⟨Ty.empty, e⟩ → WfD Γ (abort a) ⟨A, e⟩
  | unit (e) : WfD Γ unit ⟨Ty.unit, e⟩

def Term.WfD.var0 {head} {Γ : Ctx α ε} : WfD (head::Γ) (@Term.var φ 0) head := var (by simp)

def Term.WfD.var1 {left right} {Γ : Ctx α ε} : WfD (left::right::Γ) (@Term.var φ 1) right
  := var (by simp)

def Term.WfD.cast_term {Γ : Ctx α ε} {a a' : Term φ} {V} (h : WfD Γ a V) (ha : a = a') : WfD Γ a' V
  := ha ▸ h

def Term.WfD.cast_src {Γ Γ' : Ctx α ε} {a : Term φ} {V} (h : Γ = Γ') (d : WfD Γ a V)
  : WfD Γ' a V := h ▸ d

def Term.WfD.cast_trg {Γ : Ctx α ε} {a : Term φ} {V V'} (d : WfD Γ a V) (h : V = V')
  : WfD Γ a V' := h ▸ d

theorem Term.WfD.cast_term_cast_src {Γ Γ' : Ctx α ε} {a a' : Term φ} {V}
  (h : Γ = Γ') (d : WfD Γ a V) (ha : a = a')
  : (d.cast_src h).cast_term ha = (d.cast_term ha).cast_src h
  := by cases h; cases ha; rfl

theorem Term.WfD.cast_term_cast_trg {Γ : Ctx α ε} {a a' : Term φ} {V V'}
  (d : WfD Γ a V) (ha : a = a') (h : V = V')
  : (d.cast_trg h).cast_term ha = (d.cast_term ha).cast_trg h
  := by cases ha; cases h; rfl

theorem Term.WfD.cast_src_cast_trg {Γ Γ' : Ctx α ε} {a : Term φ} {V V'}
  (h : Γ = Γ') (d : WfD Γ a V) (h' : V = V')
  : (d.cast_trg h').cast_src h = (d.cast_src h).cast_trg h'
  := by cases h; cases h'; rfl

-- TODO: weakenings should commute, too...

theorem Term.WfD.toWf {Γ : Ctx α ε} {a : Term φ} {V} (h : WfD Γ a V) : Wf Γ a V
  := match h with
  | var dv => Wf.var dv
  | op df de => Wf.op df de.toWf
  | let1 da db => Wf.let1 da.toWf db.toWf
  | pair dl dr => Wf.pair dl.toWf dr.toWf
  | let2 da dc => Wf.let2 da.toWf dc.toWf
  | inl dl => Wf.inl dl.toWf
  | inr dr => Wf.inr dr.toWf
  | case da dl dr => Wf.case da.toWf dl.toWf dr.toWf
  | abort da => Wf.abort da.toWf
  | unit e => Wf.unit e

theorem Term.Wf.nonempty {Γ : Ctx α ε} {a : Term φ} {V} (h : Wf Γ a V) : Nonempty (WfD Γ a V)
  := match h with
  | var dv => ⟨WfD.var dv⟩
  | op df de => let ⟨de⟩ := de.nonempty; ⟨de.op df⟩
  | let1 da db => let ⟨da⟩ := da.nonempty; let ⟨db⟩ := db.nonempty; ⟨da.let1 db⟩
  | pair dl dr => let ⟨dl⟩ := dl.nonempty; let ⟨dr⟩ := dr.nonempty; ⟨dl.pair dr⟩
  | let2 da dc => let ⟨da⟩ := da.nonempty; let ⟨dc⟩ := dc.nonempty; ⟨da.let2 dc⟩
  | inl dl => let ⟨dl⟩ := dl.nonempty; ⟨dl.inl⟩
  | inr dr => let ⟨dr⟩ := dr.nonempty; ⟨dr.inr⟩
  | case da dl dr =>
    let ⟨da⟩ := da.nonempty; let ⟨dl⟩ := dl.nonempty; let ⟨dr⟩ := dr.nonempty; ⟨da.case dl dr⟩
  | abort da => let ⟨da⟩ := da.nonempty; ⟨da.abort⟩
  | unit e => ⟨WfD.unit e⟩

theorem Term.Wf.nonempty_iff {Γ : Ctx α ε} {a : Term φ} {V} : Wf Γ a V ↔ Nonempty (WfD Γ a V)
  := ⟨Term.Wf.nonempty, λ⟨h⟩ => h.toWf⟩

@[simp]
theorem Term.Wf.var_iff {Γ : Ctx α ε} {n V} : Wf (φ := φ) Γ (Term.var n) V ↔ Γ.Var n V
  := ⟨λ| Wf.var dv => dv, λdv => Wf.var dv⟩

@[simp]
theorem Term.Wf.op_iff {Γ : Ctx α ε} {a : Term φ} {V}
  : Wf Γ (Term.op f a) V ↔ Φ.trg f ≤ V.1 ∧ Φ.effect f ≤ V.2 ∧ Wf Γ a ⟨Φ.src f, V.2⟩
  := ⟨λ| Wf.op df de => ⟨df.trg, df.effect, de.wk_res ⟨df.src, le_refl _⟩⟩,
      λ⟨trg, e, de⟩ => Wf.op ⟨⟨le_refl _, trg⟩, e⟩ de⟩

@[simp]
theorem Term.Wf.pair_iff {Γ : Ctx α ε} {a b : Term φ} {A B}
  : Wf Γ (Term.pair a b) ⟨Ty.prod A B, e⟩ ↔ Wf Γ a ⟨A, e⟩ ∧ Wf Γ b ⟨B, e⟩
  := ⟨λ| Wf.pair dl dr => ⟨dl, dr⟩, λ⟨dl, dr⟩ => Wf.pair dl dr⟩

@[simp]
theorem Term.Wf.inl_iff {Γ : Ctx α ε} {a : Term φ} {A B}
  : Wf Γ (Term.inl a) ⟨Ty.coprod A B, e⟩ ↔ Wf Γ a ⟨A, e⟩
  := ⟨λ| Wf.inl dl => dl, λdl => Wf.inl dl⟩

@[simp]
theorem Term.Wf.inr_iff {Γ : Ctx α ε} {b : Term φ} {A B}
  : Wf Γ (Term.inr b) ⟨Ty.coprod A B, e⟩ ↔ Wf Γ b ⟨B, e⟩
  := ⟨λ| Wf.inr dr => dr, λdr => Wf.inr dr⟩

@[simp]
theorem Term.Wf.abort_iff {Γ : Ctx α ε} {a : Term φ} {A}
  : Wf Γ (Term.abort a) ⟨A, e⟩ ↔ Wf Γ a ⟨Ty.empty, e⟩
  := ⟨λ| Wf.abort da => da, λda => Wf.abort da⟩

@[simp]
theorem Term.Wf.unit' {Γ : Ctx α ε} {e} : Wf (φ := φ) Γ Term.unit ⟨Ty.unit, e⟩
  := Wf.unit e

-- /-- Infer the type of a term; pun with infimum -/
-- def Term.infTy (Γ : Ctx α ε) : Term φ → Ty α
--   | var n => if h : n < Γ.length then (Γ.get ⟨n, h⟩).1 else Ty.unit
--   | op f _ => Φ.trg f
--   | pair a b => Ty.prod (a.infTy Γ) (b.infTy Γ)
--   | inl a => Ty.coprod (a.infTy Γ) Ty.unit
--   | inr b => Ty.coprod Ty.unit (b.infTy Γ)
--   | unit => Ty.unit

-- theorem Term.WfD.infTy_le {Γ : Ctx α ε} {a : Term φ} {A e} (h : WfD Γ a ⟨A, e⟩) : a.infTy Γ ≤ A
--   := match h with
--   | var dv => by simp [infTy, dv.length, dv.get.left]
--   | op df de => df.trg
--   | prod dl dr => Ty.LE.prod dl.infTy_le dr.infTy_le
--   | unit _ | bool _ _ => le_refl _

-- def Term.WfD.toInfTy {Γ : Ctx α ε} {a : Term φ} {A e} (h : WfD Γ a ⟨A, e⟩) : WfD Γ a ⟨a.infTy Γ, e⟩
--   := match h with
--   | var dv => var (by
--     constructor <;> simp only [infTy, dv.length, ↓reduceDIte]
--     exact ⟨le_refl _, dv.get.2⟩
--     )
--   | op df de => op ⟨df.src, le_refl _, df.effect⟩ de
--   | prod dl dr => prod (dl.toInfTy) (dr.toInfTy)
--   | unit e => unit e
--   | bool b e => bool b e

-- TODO: WfD ==> Wf

-- TODO: Wf ==> ∃WfD

-- def Term.Wf.toWfD
--   {Γ : Ctx α ε} {a : Term φ} {V} (h : Wf Γ a V) : WfD Γ a V
--   := match a, V, h with
--   | Term.var _, _, h => WfD.var h.to_var
--   | Term.op _ _, _, h => WfD.op h.to_fn h.to_op.toWfD
--   | Term.pair _ _, ⟨Ty.prod _ _, _⟩, h => WfD.pair h.to_left.toWfD h.to_right.toWfD
--   | Term.inl _, _, h => WfD.inl h.to_left.toWfD
--   | Term.inr _, _, h => WfD.inr h.to_right.toWfD
--   | Term.unit, ⟨Ty.unit, _⟩, _ => WfD.unit _

-- theorem Term.wf_iff_wfD
--   {Γ : Ctx α ε} {a : Term φ} {V} : Wf Γ a V ↔ Nonempty (WfD Γ a V)
--   := ⟨Nonempty.intro ∘ Wf.toWfD, λ⟨h⟩ => h.toWf⟩

-- TODO: for a discrete order on α, WfD unique



/-- Weaken the effect of a term derivation -/
def Term.WfD.wk_eff {Γ : Ctx α ε} {a : Term φ} {A e} (h : e ≤ e')
  : WfD Γ a ⟨A, e⟩ → WfD Γ a ⟨A, e'⟩
  | var dv => var (dv.wk_eff h)
  | op df de => op (df.wk_eff h) (de.wk_eff h)
  | let1 da db => let1 (da.wk_eff h) (db.wk_eff h)
  | pair dl dr => pair (dl.wk_eff h) (dr.wk_eff h)
  | let2 da dc => let2 (da.wk_eff h) (dc.wk_eff h)
  | inl dl => inl (dl.wk_eff h)
  | inr dr => inr (dr.wk_eff h)
  | case da dl dr => case (da.wk_eff h) (dl.wk_eff h) (dr.wk_eff h)
  | abort da => abort (da.wk_eff h)
  | unit e => unit e'

/-- Weaken the type of a term derivation -/
def Term.WfD.wk_ty {Γ : Ctx α ε} {a : Term φ} {A e} (h : A ≤ A')
  (da : WfD Γ a ⟨A, e⟩) : WfD Γ a ⟨A', e⟩
  := match da, A', h with
  | var dv, _, h => var (dv.wk_ty h)
  | op df de, _, h => op (df.wk_trg h) de
  | let1 da db, _, h => let1 da (db.wk_ty h)
  | pair dl dr, Ty.prod A B, h => pair (dl.wk_ty h.prod_left) (dr.wk_ty h.prod_right)
  | let2 da dc, _, h => let2 da (dc.wk_ty h)
  | inl dl, Ty.coprod A B, h => inl (dl.wk_ty h.coprod_left)
  | inr dr, Ty.coprod A B, h => inr (dr.wk_ty h.coprod_right)
  | case da dl dr, _, h => case da (dl.wk_ty h) (dr.wk_ty h)
  | abort da, _, h => abort da
  | unit e, Ty.unit, h => unit e

/-- Weaken the result of a term derivation -/
def Term.WfD.wk_res₂ {a : Term φ} (hA : A ≤ A') (he : e ≤ e') (da : WfD Γ a ⟨A, e⟩)
  : WfD Γ a ⟨A', e'⟩ := da.wk_eff he |>.wk_ty hA

/-- Weaken the result of a term derivation -/
def Term.WfD.wk_res {a : Term φ} (h : V ≤ V') (da : WfD Γ a V) : WfD Γ a V'
  := match V, V', h with
  | ⟨_, _⟩, ⟨_, _⟩, ⟨hA, he⟩ => da.wk_res₂ hA he

/-- Weaken a term derivation -/
def Term.WfD.wk {Γ Δ : Ctx α ε} {ρ} (h : Γ.Wkn Δ ρ) {a : Term φ}
  : WfD Δ a ⟨A, e⟩ → WfD Γ (a.wk ρ) ⟨A, e⟩
  | var dv => var (dv.wk h)
  | op df de => op df (de.wk h)
  | let1 da db => let1 (da.wk h) (db.wk h.slift)
  | pair dl dr => pair (dl.wk h) (dr.wk h)
  | let2 da db => let2 (da.wk h) (db.wk h.sliftn₂)
  | inl dl => inl (dl.wk h)
  | inr dr => inr (dr.wk h)
  | case da db dc => case (da.wk h) (db.wk h.slift) (dc.wk h.slift)
  | abort da => abort (da.wk h)
  | unit e => unit e

theorem Term.Wf.wk {a : Term φ} (h : Γ.Wkn Δ ρ) (d : Wf Δ a ⟨A, e⟩) : Wf Γ (a.wk ρ) ⟨A, e⟩
  := have ⟨d⟩ := d.nonempty; (d.wk h).toWf

def Term.InS.wk {Γ Δ : Ctx α ε} (ρ : Γ.InS Δ) (d : InS φ Δ ⟨A, e⟩) : InS φ Γ ⟨A, e⟩
  := ⟨(d : Term φ).wk ρ, d.prop.wk ρ.prop⟩

def Term.InS.wk1 {Γ : Ctx α ε} {L} (d : InS φ (head::Γ) L)
  : InS φ (head::inserted::Γ) L
  := d.wk Ctx.InS.wk1

theorem Term.InS.wk_equiv {Γ Δ : Ctx α ε} {ρ ρ' : Γ.InS Δ} (d : InS φ Δ ⟨A, e⟩) (h : ρ ≈ ρ')
  : d.wk ρ = d.wk ρ'
  := sorry

@[simp]
theorem Term.InS.wk_var {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ} {n} (h : Δ.Var n A)
  : (var (φ := φ) n h).wk ρ = var (ρ.val n) (h.wk ρ.prop)
  := rfl

@[simp]
theorem Term.InS.wk_op {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ}
  {df : Φ.EFn f A B e} {de : Term.InS φ Δ ⟨A, e⟩}
  : (op f df de).wk ρ = op f df (de.wk ρ)
  := rfl

@[simp]
theorem Term.InS.wk_pair {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ}
  {dl : Term.InS φ Δ ⟨A, e⟩} {dr : Term.InS φ Δ ⟨B, e⟩}
  : (pair dl dr).wk ρ = pair (dl.wk ρ) (dr.wk ρ)
  := rfl

@[simp]
theorem Term.InS.wk_inl {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ} {dl : Term.InS φ Δ ⟨A, e⟩}
  : (inl (right := right) dl).wk ρ = inl (dl.wk ρ)
  := rfl

@[simp]
theorem Term.InS.wk_inr {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ} {dr : Term.InS φ Δ ⟨B, e⟩}
  : (inr (left := left) dr).wk ρ = inr (dr.wk ρ)
  := rfl

@[simp]
theorem Term.InS.wk_abort {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ} {da : Term.InS φ Δ ⟨Ty.empty, e⟩}
  : (abort (tyOut := tyOut) da).wk ρ = abort (tyOut := tyOut) (da.wk ρ)
  := rfl

@[simp]
theorem Term.InS.wk_unit {Γ Δ : Ctx α ε} {ρ : Γ.InS Δ} {e}
  : (unit (φ := φ) e).wk ρ = unit e
  := rfl

/-- Reverse-weaken a term derivation, given that it is inbounds -/
def Term.WfD.wk_inv {Γ Δ : Ctx α ε} {ρ} (h : Γ.EWkn Δ ρ) {a : Term φ}
  (d : WfD Γ (a.wk ρ) ⟨A, e⟩) (ha : a.fvi ≤ Δ.length) : WfD Δ a ⟨A, e⟩
  := match a, d with
  | Term.var i, var dv => var $ h.var_inv ha dv
  | Term.op _ _, op df de => op df (de.wk_inv h ha)
  | Term.let1 _ _, let1 da db => let1 (da.wk_inv h sorry) (db.wk_inv h.lift sorry)
  | Term.pair _ _, pair dl dr
    => pair (dl.wk_inv h (fvi_pair_le_left ha)) (dr.wk_inv h (fvi_pair_le_right ha))
  | Term.let2 _ _, let2 da dc => let2 (da.wk_inv h sorry) (dc.wk_inv h.liftn₂ sorry)
  | Term.inl _, inl dl => inl (dl.wk_inv h ha)
  | Term.inr _, inr dr => inr (dr.wk_inv h ha)
  | Term.case _ _ _, case da dl dr
    => case (da.wk_inv h sorry) (dl.wk_inv h.lift sorry) (dr.wk_inv h.lift sorry)
  | Term.abort _, abort da => abort (da.wk_inv h ha)
  | Term.unit, unit e => unit e

theorem Term.Wf.wk_inv {a : Term φ}
  (h : Γ.EWkn Δ ρ) (d : Wf Γ (a.wk ρ) ⟨A, e⟩) (ha : a.fvi ≤ Δ.length) : Wf Δ a ⟨A, e⟩
  := have ⟨d⟩ := d.nonempty; (d.wk_inv h ha).toWf

theorem Term.Wf.fvs {a : Term φ} (h : Wf Γ a V) : a.fvs ⊆ Set.Iio Γ.length
  := by induction h with
  | var dv => simp [dv.length]
  | _ => simp [*] <;> sorry

def Term.WfD.wk1 {Γ : Ctx α ε} {L} {r : Term φ} (dr : WfD (A::Γ) r L) : WfD (A::B::Γ) r.wk1 L
  := dr.wk Ctx.Wkn.wk1

def Term.WfD.wk0 {Γ : Ctx α ε} {L} {r : Term φ} (dr : WfD Γ r L)
  : WfD (A::Γ) (r.wk Nat.succ) L
  := dr.wk Ctx.Wkn.succ

def Term.WfD.wk_id {Γ Δ : Ctx α ε} {a : Term φ} (h : Γ.Wkn Δ id) : WfD Δ a ⟨A, e⟩ → WfD Γ a ⟨A, e⟩
  | var dv => var (dv.wk h)
  | op df de => op df (de.wk_id h)
  | let1 da db => let1 (da.wk_id h) (db.wk_id h.slift_id)
  | pair dl dr => pair (dl.wk_id h) (dr.wk_id h)
  | let2 da db => let2 (da.wk_id h) (db.wk_id h.sliftn_id₂)
  | inl dl => inl (dl.wk_id h)
  | inr dr => inr (dr.wk_id h)
  | case da dl dr => case (da.wk_id h) (dl.wk_id h.slift_id) (dr.wk_id h.slift_id)
  | abort da => abort (da.wk_id h)
  | unit e => unit e
