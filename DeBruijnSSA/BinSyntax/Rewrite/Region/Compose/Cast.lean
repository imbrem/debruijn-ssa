import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Sum
import DeBruijnSSA.BinSyntax.Rewrite.Region.Compose.Product

namespace BinSyntax

variable [Φ: EffInstSet φ (Ty α) ε] [PartialOrder α] [SemilatticeSup ε] [OrderBot ε]

namespace Region

def Eqv.acast {Γ : Ctx α ε} {L : LCtx α} {X Y : Ty α} (h : X = Y)
  : Eqv φ ((X, ⊥)::Γ) (Y::L) := (Eqv.nil (targets := L)).cast rfl (by rw [h])

@[simp]
theorem Eqv.acast_rfl {Γ : Ctx α ε} {L : LCtx α} {X : Ty α}
  : Eqv.acast (φ := φ) (Γ := Γ) (L := L) (X := X) rfl = Eqv.nil := rfl

theorem Eqv.acast_acast {Γ : Ctx α ε} {L : LCtx α} {X Y Z : Ty α} {h : X = Y} {h' : Y = Z}
  : (Eqv.acast (φ := φ) (Γ := Γ) (L := L) h) ;; acast h' = Eqv.acast (by rw [h, h'])
  := by cases h; cases h'; simp

theorem Eqv.rtimes_acast {Γ : Ctx α ε} {L : LCtx α} {X Y : Ty α} {h : X = Y}
  : Z ⋊ (acast (φ := φ) (Γ := Γ) (L := L) h) = acast (by rw [h])
  := by cases h; simp [rtimes_nil]

theorem Eqv.ltimes_acast {Γ : Ctx α ε} {L : LCtx α} {X Y : Ty α} {h : X = Y}
  : (acast (φ := φ) (Γ := Γ) (L := L) h) ⋉ Z = acast (by rw [h])
  := by cases h; simp [ltimes_nil]

theorem Eqv.sum_acast {Γ : Ctx α ε} {L : LCtx α}
  {X Y X' Y' : Ty α} {h : X = Y} {h' : X' = Y'}
  : sum (acast (φ := φ) (Γ := Γ) (L := L) h) (acast h') = acast (by rw [h, h'])
  := by cases h; cases h'; simp [sum_nil]

theorem Eqv.sum_acast_nil {Γ : Ctx α ε} {L : LCtx α}
  {X Y : Ty α} {h : X = Y}
  : sum (acast (φ := φ) (Γ := Γ) (L := L) h) (nil (ty := X')) = acast (by rw [h])
  := by cases h; simp [sum_nil]

theorem Eqv.sum_nil_acast {Γ : Ctx α ε} {L : LCtx α}
  {X Y : Ty α} {h : X = Y}
  : sum (nil (ty := X')) (acast (φ := φ) (Γ := Γ) (L := L) h) = acast (by rw [h])
  := by cases h; simp [sum_nil]

theorem Eqv.sum_acast_inv {Γ : Ctx α ε} {L : LCtx α}
  {X Y X' Y' : Ty α} {h : X.coprod Y = X'.coprod Y'}
  : (acast (φ := φ) (Γ := Γ) (L := L) h) = sum (acast (by cases h; rfl)) (acast (by cases h; rfl))
  := by cases h; simp [sum_nil]

end Region

end BinSyntax
