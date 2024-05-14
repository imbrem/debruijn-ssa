import DeBruijnSSA.SingleApp.Typing

namespace SingleApp

section Body

variable
  [Φ: InstSet φ (Ty α) ε] [PartialOrder α] [PartialOrder ε] [Bot ε]
  {Γ Δ : Ctx α ε}

def Body.WfD.append {Γ Δ Ξ : Ctx α ε} {b b' : Body φ}
  (db : b.WfD Γ Δ) (db' : b'.WfD (Δ.reverse ++ Γ) Ξ) : (b.append b').WfD Γ (Δ ++ Ξ)
  := match Δ, Ξ, db with
  | [], _, nil => db'
  | ⟨A, ⊥⟩::Δ, Ξ, let1 da db => let1 da (db.append
    (db'.cast_src (by rw [Ctx.reverse, List.reverse_cons, <-List.append_cons]; rfl)))
  | ⟨A, ⊥⟩::⟨B, ⊥⟩::Δ, Ξ, let2 da db => let2 da (db.append
    (db'.cast_src (by
      rw [Ctx.reverse, List.reverse_cons, List.reverse_cons, <-List.append_cons, <-List.append_cons]
      rfl)))

-- TODO: append_assoc w/ cast_trg

def Body.WfD.ltimes {Γ Δ Ξ : Ctx α ε} {b b' : Body φ}
  (db : b.WfD Γ Δ) (db' : b'.WfD Γ Ξ) : (b.ltimes b').WfD Γ (Δ ++ Ξ)
  := db.append (db'.wk ((Ctx.Wkn.id _).stepn_append'
    (by rw [db.num_defs_eq_length, Ctx.reverse, List.length_reverse])))

-- TODO: ltimes_assoc w/ cast_trg

end Body
