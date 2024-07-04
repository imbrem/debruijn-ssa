-- import DeBruijnSSA.BinSyntax.Syntax.Rewrite.Definitions
-- import DeBruijnSSA.BinSyntax.Syntax.Rewrite.Cong
-- import DeBruijnSSA.BinSyntax.Syntax.Rewrite.Directed

-- namespace BinSyntax

-- variable {φ : Type u} {ε : Type v} [Φ: EffectSet φ ε] [SemilatticeSup ε] [OrderBot ε]

-- namespace Region

-- inductive CongD.SubstCong (P : Region φ → Region φ → Type _) : Subst φ → Subst φ → Type _
--   | step (n) : CongD P r r' → SubstCong P (Function.update σ n r) (Function.update σ' n r')

-- inductive BCongD.SubstCong (P : (ℕ → ε) → Region φ → Region φ → Type _)
--   : (ℕ → ε) → Subst φ → Subst φ → Type _
--   | step (n) : BCongD P Γ r r' → SubstCong P Γ (Function.update σ n r) (Function.update σ' n r')

-- def RWD.Subst (P : (ℕ → ε) →  Region φ → Region φ → Type _) (Γ : ℕ → ε) (σ σ' : Subst φ)
--   := ∀n, RWD P Γ (σ n) (σ' n)

-- -- TODO: RwD.Subst is effect monotone/antitone iff underlying is
-- -- ==> RwD.Subst is effect preserving iff underlying is

-- def RWD.Subst.refl {P} {Γ : ℕ → ε} (σ : Region.Subst φ) : RWD.Subst P Γ σ σ := λ_ => RWD.refl _

-- def RWD.Subst.comp {P} {Γ : ℕ → ε} {σ σ' σ'' : Region.Subst φ}
--   (h : RWD.Subst P Γ σ σ') (h' : RWD.Subst P Γ σ' σ'')
--   : RWD.Subst P Γ σ σ''
--   := λn => (h n).comp (h' n)

-- -- TODO: lift, liftn, lwk, vwk lore

-- -- TODO: Path SubstCong ==> RWD, RWD ∩ FiniteDiff ==> Path SubstCong, "adjunction"

-- end Region

-- end BinSyntax
