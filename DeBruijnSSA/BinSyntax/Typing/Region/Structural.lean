import DeBruijnSSA.BinSyntax.Typing.Term.Structural
import DeBruijnSSA.BinSyntax.Typing.Region.LSubst
import DeBruijnSSA.BinSyntax.Typing.Region.Compose

namespace BinSyntax

namespace Term

end Term

namespace Region

variable
  [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [OrderBot ε]
  {Γ Δ : Ctx α ε} {σ : Region.Subst φ}

open Term

def Subst.pack : Region.Subst φ := λℓ => br 0 (Term.inj_n ℓ)

@[simp]
theorem Subst.Wf.pack {Γ : Ctx α ε} {R : LCtx α}
  : Subst.Wf Γ R [R.pack] (Subst.pack (φ := φ)) := λ_ => Wf.br LCtx.Trg.shead Term.Wf.inj_n

@[simp]
def Subst.InS.pack {Γ : Ctx α ε} {R : LCtx α} : Subst.InS φ Γ R [R.pack] :=
  ⟨Subst.pack, Subst.Wf.pack⟩

@[simp]
theorem Subst.InS.coe_pack {Γ : Ctx α ε} {R : LCtx α} (ℓ : ℕ)
  : (Subst.InS.pack (φ := φ) (Γ := Γ) (R := R) : Region.Subst φ) ℓ = br 0 (Term.inj_n ℓ) := rfl

@[simp]
theorem Subst.vlift_pack
  : pack.vlift = pack (φ := φ) := by funext ℓ; simp [pack, Subst.vlift, vwk1]

@[simp]
theorem Subst.InS.vlift_pack {Γ : Ctx α ε} {R : LCtx α}
  : (pack (φ := φ) (Γ := Γ) (R := R)).vlift (head := head) = pack := by ext; simp

def unpack : ℕ → Region φ
  | 0 => loop
  | r + 1 => case (var 0) nil ((unpack r).lwk0)

@[simp]
theorem vwk_lift_unpack (r : ℕ) : (unpack r).vwk (Nat.liftWk ρ) = unpack (φ := φ) r := by
  induction r generalizing ρ with
  | zero => rw [unpack, vwk_loop]
  | succ r ih =>
    rw [unpack, vwk]
    congr
    rw [lwk0, vwk_lwk, ih]

@[simp]
theorem vwk1_unpack (r : ℕ) : (unpack r).vwk1 = unpack (φ := φ) r := by
  rw [vwk1, vwk_lift_unpack]

@[simp]
theorem vsubst_lift_unpack {ρ : Term.Subst φ} (r : ℕ)
  : (unpack r).vsubst ρ.lift = unpack (φ := φ) r := by
  induction r generalizing ρ with
  | zero => rw [unpack, vsubst_loop]
  | succ r ih =>
    rw [unpack, vsubst]
    congr
    rw [lwk0, vsubst_lwk, ih]

@[simp]
theorem Wf.unpack' {Γ : Ctx α ε} {R L : LCtx α}
  : Wf ((R.pack, ⊥)::Γ) (unpack (φ := φ) R.length) (R ++ L) :=
  by induction R generalizing Γ with
  | nil => exact Wf.loop
  | cons _ _ I => exact Wf.case (Term.Wf.var Ctx.Var.shead) Wf.nil I.lwk0

@[simp]
theorem Wf.unpack {Γ : Ctx α ε} {R : LCtx α}
  : Wf ((R.pack, ⊥)::Γ) (unpack (φ := φ) R.length) R :=
  by induction R generalizing Γ with
  | nil => exact Wf.loop
  | cons _ _ I => exact Wf.case (Term.Wf.var Ctx.Var.shead) Wf.nil I.lwk0

@[simp]
def InS.unpack {Γ : Ctx α ε} {R : LCtx α} : InS φ ((R.pack, ⊥)::Γ) R :=
  ⟨Region.unpack R.length, Wf.unpack⟩

@[simp]
theorem InS.coe_unpack {Γ : Ctx α ε} {R : LCtx α}
  : (InS.unpack (φ := φ) (Γ := Γ) (R := R) : Region φ) = Region.unpack R.length :=
  rfl

@[simp]
theorem InS.vwk_lift_unpack {Γ : Ctx α ε} {R : LCtx α} {ρ : Γ.InS Δ}
  : (InS.unpack (φ := φ) (R := R)).vwk (ρ.lift (le_refl _)) = unpack := by ext; simp

@[simp]
theorem InS.vwk1_unpack {Γ : Ctx α ε} {R : LCtx α}
  : (InS.unpack (φ := φ) (Γ := Γ) (R := R)).vwk1 (inserted := inserted) = unpack := by ext; simp

def Subst.InS.unpack {Γ : Ctx α ε} {R : LCtx α} : Subst.InS φ Γ [R.pack] R :=
  Region.InS.unpack.csubst

@[simp]
theorem Subst.InS.coe_unpack {Γ : Ctx α ε} {R : LCtx α}
  : (Subst.InS.unpack (φ := φ) (Γ := Γ) (R := R) : Region.Subst φ)
  = Region.csubst (Region.unpack R.length) :=
  rfl

@[simp]
theorem Subst.InS.vlift_unpack {Γ : Ctx α ε} {R : LCtx α}
  : (Subst.InS.unpack (φ := φ) (Γ := Γ) (R := R)).vlift (head := head) = unpack := by
  ext; simp [Subst.vlift]

open Term

end Region
