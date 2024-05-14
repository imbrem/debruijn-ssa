import Discretion
import Discretion.Wk.Multiset
import Mathlib.Algebra.BigOperators.Basic
import DeBruijnSSA.BinPair.Syntax.Definitions
import DeBruijnSSA.BinPair.Syntax.Fv
import DeBruijnSSA.BinPair.Syntax.Subst

-- TODO: use abstract higher-ERT type formalism, add to discretion?

-- TODO: splat file?

namespace BinPair

-- TODO: stepnwk and friends

/-- Append two bodies, letting the second use the variables defined in the first -/
def Body.append (b b' : Body φ) : Body φ := match b with
  | nil => b'
  | let1 a t => let1 a (t.append b')
  | let2 a t => let2 a (t.append b')

theorem Body.fv_append (b b' : Body φ) : (b.append b').fv = b.fv + b'.fv.liftnFv b.num_defs := by
  induction b generalizing b'
  <;> simp [append, fv, <-Multiset.liftnFv_add, add_assoc, Nat.add_comm, *]

theorem Body.append_num_defs (b b' : Body φ)
  : (b.append b').num_defs = b.num_defs + b'.num_defs := by
  induction b generalizing b' <;> simp_arith [append, num_defs, *]

@[simp]
theorem Body.nil_append (b : Body φ) : nil.append b = b := rfl

@[simp]
theorem Body.append_nil (b : Body φ) : b.append nil = b := by
  induction b <;> simp [append, *]

theorem Body.append_assoc (b b' b'' : Body φ)
  : (b.append b').append b'' = b.append (b'.append b'') := by
  induction b generalizing b' b'' <;> simp [append, *]

theorem Body.wk_append (ρ : ℕ → ℕ) (b b' : Body φ)
  : (b.append b').wk ρ = (b.wk ρ).append (b'.wk (Nat.liftnWk b.num_defs ρ)) := by
  induction b generalizing ρ b' with
  | nil => rfl
  | _ => simp only [wk, *, append, num_defs, let1.injEq, true_and, Nat.liftnWk_succ]; congr

/-- Append two bodies, weakening the second so that it shares the same inputs as the first -/
def Body.ltimes (b b' : Body φ) : Body φ := b.append (b'.wk (· + b.num_defs))

theorem Body.fv_ltimes (b b' : Body φ) : (b.ltimes b').fv = b.fv + b'.fv := by
  rw [ltimes, fv_append, fv_wk]
  congr
  -- TODO: factor out as theorem in `Discretion`
  generalize b'.fv = s
  generalize b.num_defs = n
  open Multiset in
  ext i
  simp only [liftnFv, ge_iff_le, count_map, filter_filter, <-countP_eq_card_filter, countP_map]
  congr
  ext a
  simp

theorem Body.ltimes_num_defs (b b' : Body φ) : (b.ltimes b').num_defs = b.num_defs + b'.num_defs
  := by simp [ltimes, append_num_defs, Body.num_defs_wk]

theorem Body.wk_ltimes (ρ : ℕ → ℕ) (b b' : Body φ)
  : (b.ltimes b').wk ρ = (b.wk ρ).ltimes (b'.wk ρ) := by
  simp only [ltimes, wk_append, <-wk_comp]
  congr
  funext n
  simp [Function.comp_apply, Nat.liftnWk, num_defs_wk]

@[simp]
theorem Body.ltimes_nil (b : Body φ) : b.ltimes nil = b := by simp [ltimes]

@[simp]
theorem Body.nil_ltimes (b : Body φ) : nil.ltimes b = b :=
  by simp only [ltimes, num_defs, add_zero, nil_append]; exact b.wk_id

theorem Body.let1_ltimes (a : Term φ) (b b' : Body φ)
  : (let1 a b).ltimes b' = let1 a (b.ltimes (b'.wk Nat.succ)) := by
  simp only [ltimes, append, wk_append, <-wk_comp]
  congr
  funext n
  simp_arith

theorem Body.let2_ltimes (a : Term φ) (b b' : Body φ)
  : (let2 a b).ltimes b' = let2 a (b.ltimes (b'.wk (λn => n + 2))) := by
  simp only [ltimes, append, wk_append, <-wk_comp]
  congr
  funext n
  simp_arith

theorem Body.ltimes_assoc (b b' b'' : Body φ)
  : (b.ltimes b').ltimes b'' = b.ltimes (b'.ltimes b'') := by
  induction b generalizing b' b'' <;> simp [let1_ltimes, let2_ltimes, wk_ltimes, *]

-- TODO: make Body into a monoid this way

-- TODO: relationship between append and comp

-- TODO: define comp as append instead? removes the need for compn...

-- TODO: another issue: now there are _two_ monoid structures on Body

-- TODO: variant with a body followed by a weakening (WBody?). This is also a monoid, of course.

-- TODO: in fact, _this_ variant supports an _rtimes_ operation. Wow!

/-- Substitute the variables in this basic block -/

theorem Block.fv_lwk (ρ : ℕ → ℕ) (β : Block φ) : (β.lwk ρ).fv = β.fv := by
  simp [Terminator.fv_lwk]

theorem Block.fl_lwk (ρ : ℕ → ℕ) (β : Block φ) : (β.lwk ρ).fl = β.fl.map ρ := by
  simp [Terminator.fl_lwk]

/-- Prepend a let-binding to this basic block -/
@[match_pattern]
def Block.let1 (a : Term φ) (β : Block φ) : Block φ where
  body := Body.let1 a β.body
  terminator := β.terminator

/-- Prepend a destructuring let-binding to this basic block -/
@[match_pattern]
def Block.let2 (a : Term φ) (β : Block φ) : Block φ where
  body := Body.let2 a β.body
  terminator := β.terminator

/-- Prepend a body of instructions to this basic block -/
def Block.prepend (b : Body φ) (β : Block φ) : Block φ where
  body := b.append β.body
  terminator := β.terminator

@[simp]
theorem Block.prepend_nil (β : Block φ) : β.prepend Body.nil = β := rfl

@[simp]
theorem Block.prepend_let1 (a : Term φ) (b : Body φ) (β : Block φ)
  : β.prepend (Body.let1 a b) = (β.prepend b).let1 a := rfl

@[simp]
theorem Block.prepend_let2 (a : Term φ) (b : Body φ) (β : Block φ)
  : β.prepend (Body.let2 a b) = (β.prepend b).let2 a := rfl

theorem Block.prepend_append (b b' : Body φ) (β : Block φ)
  : β.prepend (b.append b') = (β.prepend b').prepend b := by
  simp only [Block.prepend, Body.append_assoc]

@[simp]
theorem Block.prepend_body_terminator (β : Block φ)
  : (β.terminator : Block φ).prepend β.body = β := by cases β; simp [prepend, Terminator.toBlock]

-- TODO: prepend_nil, pretty trivial

-- TODO: prepend_vwk

-- TODO: prepend_lwk

-- TODO: rename to rtimes?

/-- Precompose a body of instructions to this basic block, while weakening the block so that
they share the same inputs -/
def Block.ltimes (b : Body φ) (β : Block φ) : Block φ
  := (β.vwk (· + b.num_defs)).prepend b
  -- body := b.ltimes β.body
  -- terminator := β.terminator.vwk (β.body.num_defs.liftnWk (· + b.num_defs))

theorem Block.ltimes_nil : (β : Block φ) → β.ltimes Body.nil = β
  | ⟨body, terminator⟩ => by
    simp only [ltimes, prepend, vwk, Body.num_defs, add_zero, Body.nil_append, mk.injEq]
    exact ⟨Body.wk_id _, Nat.liftnWk_id body.num_defs ▸ Terminator.vwk_id _⟩

-- TODO: version with better defeqs?

/-- Prepend a let-binding to this region -/
@[simp]
def BBRegion.let1 (a : Term φ) : BBRegion φ → BBRegion φ
  | cfg β n G => cfg (β.let1 a) n G

/-- Prepend a destructuring let-binding to this region -/
@[simp]
def BBRegion.let2 (a : Term φ) : BBRegion φ → BBRegion φ
  | cfg β n G => cfg (β.let2 a) n G

/-- Prepend a body of instructions to this region -/
def BBRegion.prepend (b : Body φ) : BBRegion φ → BBRegion φ
  | cfg β n G => cfg (β.prepend b) n G

theorem BBRegion.prepend_nil (r : BBRegion φ) : r.prepend Body.nil = r := by
  cases r; rfl

theorem BBRegion.prepend_let1 (a : Term φ) (b : Body φ) (r : BBRegion φ)
  : r.prepend (Body.let1 a b) = (r.prepend b).let1 a := by cases r; rfl

theorem BBRegion.prepend_let2 (a : Term φ) (b : Body φ) (r : BBRegion φ)
  : r.prepend (Body.let2 a b) = (r.prepend b).let2 a := by cases r; rfl

/-- Precompose a body of instructions to this region -/
@[simp]
def TRegion.prepend (b : Body φ) (r : TRegion φ) : TRegion φ := match b with
  | Body.nil => r
  | Body.let1 a b => (r.prepend b).let1 a
  | Body.let2 a b => (r.prepend b).let2 a

theorem TRegion.prepend_nil (r : TRegion φ) : r.prepend Body.nil = r := rfl

theorem TRegion.prepend_let1 (a : Term φ) (b : Body φ) (r : TRegion φ)
  : r.prepend (Body.let1 a b) = (r.prepend b).let1 a := rfl

theorem TRegion.prepend_let2 (a : Term φ) (b : Body φ) (r : TRegion φ)
  : r.prepend (Body.let2 a b) = (r.prepend b).let2 a := rfl

/-- Convert this region to the terminator based format -/
def BBRegion.toTRegion : BBRegion φ → TRegion φ
  | cfg ⟨b, t⟩ n G => (TRegion.cfg t n (λi => (G i).toTRegion)).prepend b

theorem BBRegion.let1_toTRegion (a : Term φ) (r : BBRegion φ)
  : (r.let1 a).toTRegion = r.toTRegion.let1 a := by cases r; rfl

theorem BBRegion.let2_toTRegion (a : Term φ) (r : BBRegion φ)
  : (r.let2 a).toTRegion = r.toTRegion.let2 a := by cases r; rfl

theorem BBRegion.prepend_toTRegion (b : Body φ) (r : BBRegion φ)
  : (r.prepend b).toTRegion = r.toTRegion.prepend b := by
    induction b
      <;> simp only [prepend_let1, prepend_let2, prepend_nil, let1_toTRegion, let2_toTRegion, *]
      <;> rfl

/-- Convert this region to the standard basic-block based format -/
def TRegion.toBBRegion : TRegion φ → BBRegion φ
  | TRegion.let1 a t => BBRegion.let1 a t.toBBRegion
  | TRegion.let2 a t => BBRegion.let2 a t.toBBRegion
  | TRegion.cfg β n G => BBRegion.cfg β n (λi => (G i).toBBRegion)

theorem TRegion.let1_toBBRegion (a : Term φ) (r : TRegion φ)
  : (r.let1 a).toBBRegion = r.toBBRegion.let1 a := rfl

theorem TRegion.let2_toBBRegion (a : Term φ) (r : TRegion φ)
  : (r.let2 a).toBBRegion = r.toBBRegion.let2 a := rfl

theorem TRegion.prepend_toBBRegion (b : Body φ) (r : TRegion φ)
  : (r.prepend b).toBBRegion = r.toBBRegion.prepend b := by
  induction b <;> simp only [
    prepend_let1, let1_toBBRegion, prepend_let2, let2_toBBRegion, prepend_nil,
    BBRegion.prepend_let1, BBRegion.prepend_let2, BBRegion.prepend_nil, *]

theorem TRegion.toTRegion_toBBRegion (r : TRegion φ) : r.toBBRegion.toTRegion = r := by
  induction r with
  | let1 _ _ I => rw [toBBRegion, BBRegion.let1_toTRegion, I]
  | let2 _ _ I => rw [toBBRegion, BBRegion.let2_toTRegion, I]
  | cfg => simp [toBBRegion, BBRegion.toTRegion, *]

theorem BBRegion.toBBRegion_toTRegion (r : BBRegion φ) : r.toTRegion.toBBRegion = r := by
  induction r with
  | cfg β n G I => simp [toTRegion, TRegion.prepend_toBBRegion, TRegion.toBBRegion, prepend, I]

/-- Construct a region in terminator format from one in basic-block format -/
def TRegion.ofBBRegion : BBRegion φ ≃ TRegion φ where
  toFun := BBRegion.toTRegion
  invFun := TRegion.toBBRegion
  left_inv := BBRegion.toBBRegion_toTRegion
  right_inv := TRegion.toTRegion_toBBRegion

/-- Construct a region in basic-block format from one in terminator format -/
def BBRegion.ofTRegion : TRegion φ ≃ BBRegion φ where
  toFun := TRegion.toBBRegion
  invFun := BBRegion.toTRegion
  left_inv := TRegion.toTRegion_toBBRegion
  right_inv := BBRegion.toBBRegion_toTRegion

theorem TRegion.symm_ofBBRegion : (@TRegion.ofBBRegion φ).symm = BBRegion.ofTRegion := rfl

theorem BBRegion.symm_ofTRegion : (@BBRegion.ofTRegion φ).symm = TRegion.ofBBRegion := rfl

-- TODO: intercoercions?

-- TODO: toBBRegion_toTRegion ==> equivalence, yay

-- theorem Block.ltimes_ltimes (b b' : Body φ) (β : Block φ)
--   : β.ltimes (b.ltimes b') = (β.ltimes b').ltimes b := by
--   simp only [ltimes_eq_append_wk, Body.ltimes]
--   rw [prepend_append]
--   sorry -- TODO: by prepend_vwk

-- TODO: make Body have a monoid action on Block

-- TODO: ltimes_vwk

-- TODO: ltimes_lwk

/-- Convert this terminator to a basic block with no instructions -/

theorem Terminator.toBlock_vsubst (σ : Term.Subst φ) (t : Terminator φ)
  : (t.vsubst σ).toBlock = t.toBlock.vsubst σ
  := by simp [toBlock, Block.vsubst, Body.subst, Body.num_defs, Term.Subst.liftn_zero]

-- TODO: toBlock_lsubst

theorem Terminator.coe_toBlock_vsubst (σ : Term.Subst φ) (t : Terminator φ)
  : (t.vsubst σ : Block φ) = (t : Block φ).vsubst σ := toBlock_vsubst σ t

-- TODO: coe_lsubst

-- TODO: BBRegion.prepend

-- TODO: BBRegion.ltimes
-- TODO: TRegion.prepend

-- TODO: TRegion.ltimes

-- TODO: TRegion.body

-- TODO: TRegion.tail

-- TODO: tail.prepend body = id
-- TODO: TRegion.tail'

-- TODO: TRegion.terminator

-- TODO: TRegion.cfg

-- TODO: normalize TRegion to BBRegion; commutes with label-substitution

-- TODO: normalize BBRegion to TRegion; commutes with label-substitution

-- TODO: lsubst_id, lsubst_comp

theorem Terminator.toRegion_vsubst (σ : Term.Subst φ) (t : Terminator φ)
  : (t.vsubst σ).toRegion = t.toRegion.vsubst σ := by induction t <;> simp [*]

theorem Terminator.coe_toRegion_vsubst (σ : Term.Subst φ) (t : Terminator φ)
  : (t.vsubst σ : Region φ) = (t : Region φ).vsubst σ := toRegion_vsubst σ t

/-- Convert a terminator substitution to a region substitution pointwise -/
def Terminator.Subst.toRegion (σ : Terminator.Subst φ) : Region.Subst φ := λn => σ n

theorem Terminator.Subst.toRegion_lift (σ : Terminator.Subst φ) : σ.lift.toRegion = σ.toRegion.lift := by
  funext n; simp only [Region.Subst.lift, toRegion, lift]; split <;> simp [Terminator.toRegion_lwk]

theorem Terminator.Subst.toRegion_liftn (n : ℕ) (σ : Terminator.Subst φ) : (σ.liftn n).toRegion = σ.toRegion.liftn n :=
  by funext m; simp only [Region.Subst.liftn, toRegion, liftn]; split <;> simp [Terminator.toRegion_lwk]

theorem Terminator.Subst.toRegion_vlift (σ : Terminator.Subst φ) : σ.vlift.toRegion = σ.toRegion.vlift := by
  funext n; simp [Region.Subst.vlift, toRegion, vlift, Terminator.toRegion_vwk]

theorem Terminator.Subst.toRegion_vliftn (n : ℕ) (σ : Terminator.Subst φ)
  : (σ.vliftn n).toRegion = σ.toRegion.vliftn n :=
  by funext m; simp [Region.Subst.vliftn, toRegion, vliftn, Terminator.toRegion_vwk]

instance : Coe (Terminator.Subst φ) (Region.Subst φ) := ⟨Terminator.Subst.toRegion⟩

theorem Terminator.Subst.coe_lift (σ : Terminator.Subst φ)
  : (σ.lift : Region.Subst φ) = (σ : Region.Subst φ).lift
  := σ.toRegion_lift

theorem Terminator.Subst.coe_liftn (n : ℕ) (σ : Terminator.Subst φ) : (σ.liftn n : Region.Subst φ) = (σ : Region.Subst φ).liftn n
  := σ.toRegion_liftn n

theorem Terminator.Subst.coe_vlift (σ : Terminator.Subst φ) : (σ.vlift : Region.Subst φ) = (σ : Region.Subst φ).vlift
  := σ.toRegion_vlift

theorem Terminator.Subst.coe_vliftn (n : ℕ) (σ : Terminator.Subst φ) : (σ.vliftn n : Region.Subst φ) = (σ : Region.Subst φ).vliftn n
  := σ.toRegion_vliftn n

-- TODO: Region.prepend

-- TODO: Region.ltimes

-- TODO: Block.toRegion == terminator.toRegion.prepend body

-- TODO: Block.toRegion_{vwk, vsubst, lwk}

-- TODO: BBRegion.toRegion

-- TODO: BBRegion.toRegion_{vwk, vsubst, lwk}
theorem TRegion.toRegion_vsubst (σ : Term.Subst φ) (t : TRegion φ)
  : (t.vsubst σ).toRegion = t.toRegion.vsubst σ
  := by induction t generalizing σ <;> simp [Terminator.toRegion_vsubst, *]

theorem TRegion.coe_toRegion_vsubst (σ : Term.Subst φ) (t : TRegion φ)
  : (t.vsubst σ : Region φ) = (t : Region φ).vsubst σ := toRegion_vsubst σ t

-- TODO: Region.body

-- TODO: Region.tail

-- TODO: tail.ltimes body = id

-- TODO: CFG.vcomp (say Monoid...)

-- TODO: vcomp_assoc, vcomp_nil, nil_vcomp

-- TODO: CFG.{vwk, vsubst, lwk}_vcomp

-- TODO: CFG.hcomp (say AddMonoid...)

-- TODO: hcomp_nil, nil_hcomp, hcomp_assoc

-- TODO: CFG.{vwk, vsubst, lwk}_hcomp

-- TODO: BBCFG.toCFG

/-- Conver a basic block CFG to a terminator CFG -/
def BBCFG.toTCFG : BBCFG φ ≃ TCFG φ where
  toFun := λG => ⟨G.length, TRegion.ofBBRegion ∘ G.targets⟩
  invFun := λG => ⟨G.length, TRegion.ofBBRegion.symm ∘ G.targets⟩
  left_inv := λ⟨_, _⟩ => by simp [<-Function.comp.assoc]
  right_inv := λ⟨_, _⟩ => by simp [<-Function.comp.assoc]

/-- Convert a terminator CFG to a basic block CFG -/
def TCFG.toBBCFG : TCFG φ ≃ BBCFG φ := BBCFG.toTCFG.symm

-- TODO: intercoercions?

/-- Convert a terminator CFG to a plain CFG -/
def TCFG.toCFG (G : TCFG φ) : CFG φ where
  length := G.length
  targets := λ i => (G.targets i).toRegion

instance : Coe (TCFG φ) (CFG φ) := ⟨TCFG.toCFG⟩

-- TODO: Region.tail'

-- TODO: Region.terminator_region

-- TODO: Region.cfg

-- TODO: normalize Region to TRegion; commutes with label-substitution

-- TODO: transitively, normalize Region to BBRegion; commutes with label-substitution

-- TODO: normalize TRegion to Region; commutes with label-substiution

-- /-- A single-entry multiple-exit region, applying a substitution on jumps -/
-- inductive SRegion (φ : Type) : Type
--   | br : Nat → Term.Subst φ → SRegion φ
--   | ite : Term φ → SRegion φ → SRegion φ → SRegion φ
--   | let1 : Term φ → SRegion φ → SRegion φ
--   | let2 : Term φ → SRegion φ → SRegion φ
--   | cfg (β : SRegion φ) (n : Nat) : (Fin n → SRegion φ) → SRegion φ

-- /-- A control-flow graph with `length` entry-point regions -/
-- structure SCFG (φ : Type) : Type where
--   /-- The number of entry points to this CFG -/
--   length : Nat
--   /-- The number of exits for this CFG -/
--   targets : Fin length → SRegion φ

end BinPair
