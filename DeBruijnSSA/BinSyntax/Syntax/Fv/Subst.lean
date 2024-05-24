import Discretion.Wk.Fun
import Discretion.Wk.Multiset
import Discretion.Wk.Multiset

import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Fv.Basic

namespace BinSyntax

/-! ### Lemmas about substitution -/
section Subst

theorem Terminator.fl_vsubst (σ : Term.Subst φ) (r : Terminator φ) : (r.vsubst σ).fl = r.fl := by
  induction r generalizing σ <;> simp [*]

end Subst
