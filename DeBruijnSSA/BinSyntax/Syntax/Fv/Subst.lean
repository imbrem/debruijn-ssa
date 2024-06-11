import Discretion.Wk.Nat
import Discretion.Wk.Fin
import Discretion.Wk.Multiset
import Discretion.Wk.Multiset

import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Fv.Basic

namespace BinSyntax

/-! ### Lemmas about substitution -/
section Subst

@[simp]
theorem Terminator.fl_vsubst (σ : Term.Subst φ) (r : Terminator φ) : (r.vsubst σ).fl = r.fl := by
  induction r generalizing σ <;> simp [*]

@[simp]
theorem TRegion.fl_vsubst (σ : Term.Subst φ) (r : TRegion φ) : (r.vsubst σ).fl = r.fl := by
  induction r generalizing σ <;> simp [*]

@[simp]
theorem Block.fl_vsubst (σ : Term.Subst φ) (r : Block φ) : (r.vsubst σ).fl = r.fl := by simp

@[simp]
theorem BBRegion.fl_vsubst (σ : Term.Subst φ) (r : BBRegion φ) : (r.vsubst σ).fl = r.fl := by
  induction r generalizing σ; simp [*]

@[simp]
theorem Region.fl_vsubst (σ : Term.Subst φ) (r : Region φ) : (r.vsubst σ).fl = r.fl := by
  induction r generalizing σ <;> simp [*]

-- TODO: Term.Subst.fv

-- TODO: {Terminator, Region}.Subst.{fv, fl}

-- TODO: fv_subst, fv_vsubst

-- TODO: fl_lsubst

end Subst
