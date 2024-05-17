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
  : (t.vsubst σ).toRegion = t.toRegion.vsubst σ := by induction t generalizing σ <;> simp [*]

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

/-- Precompose a body of instructions to this region -/
@[simp]
def Region.prepend (b : Body φ) (r : Region φ) : Region φ := match b with
  | Body.nil => r
  | Body.let1 a b => (r.prepend b).let1 a
  | Body.let2 a b => (r.prepend b).let2 a

theorem Region.prepend_nil (r : TRegion φ) : r.prepend Body.nil = r := rfl

theorem Region.prepend_let1 (a : Term φ) (b : Body φ) (r : Region φ)
  : r.prepend (Body.let1 a b) = (r.prepend b).let1 a := rfl

theorem Region.prepend_let2 (a : Term φ) (b : Body φ) (r : Region φ)
  : r.prepend (Body.let2 a b) = (r.prepend b).let2 a := rfl

/-- Convert a BBRegion to a generalized region -/
def BBRegion.toRegion : BBRegion φ → Region φ
  | cfg ⟨b, t⟩ n G => (Region.cfg t n (λi => (G i).toRegion)).prepend b

/-- Construct a case split of two BBRegions in the most trivial way possible -/
def BBRegion.cfg_case (e : Term φ) (s t : BBRegion φ) : BBRegion φ
  := cfg
    ⟨Body.nil, Terminator.case e (Terminator.br 0 (Term.var 0)) (Terminator.br 1 (Term.var 0))⟩
    2 (λ| 0 => s.lwk (· + 2) | 1 => t.lwk (· + 2))

/-- Construct an case split of two BBRegions such that the images of terminators sum to the image
  of a terminator -/
def BBRegion.case (e : Term φ) (s t : BBRegion φ) : BBRegion φ :=
  match s, t with
  | cfg ⟨Body.nil, s⟩ sn sG, cfg ⟨Body.nil, t⟩ tn tG
    => cfg ⟨Body.nil,
      (s.lwk (sn.liftnWk (· + tn))).case e (t.lwk (· + sn))⟩ (sn + tn) (Fin.addCases
      (BBRegion.lwk (sn.liftnWk (· + tn)) ∘ sG)
      (BBRegion.lwk (· + sn) ∘ tG))
  | s, t => s.cfg_case e t

instance appendBBCFG : Append (BBCFG φ) := ⟨λG G' => {
  length := G.length + G'.length,
  targets := Fin.addCases G.targets G'.targets
}⟩

/-- Take the left-sum of two control-flow graphs: the left graph can call into the right, but not
  vice-versa -/
def BBCFG.lsum (G G' : BBCFG φ) : BBCFG φ := G ++ (G'.lwk (· + G.length))

/-- Take the right-sum of two control-flow graphs: the right graph can call into the left, but not
  vice-versa -/
def BBCFG.rsum (G G' : BBCFG φ) : BBCFG φ := (G.lwk (G.length.liftnWk (· + G'.length))) ++ G'

/-- Take the disjoint sum of two control-flow graphs: neither graph is allowed to call into the
  other -/
def BBCFG.sum (G G' : BBCFG φ) : BBCFG φ
  := (G.lwk (G.length.liftnWk (· + G'.length))) ++ (G'.lwk (· + G.length))

theorem BBCFG.rsum_lwk_eq_sum (G G' : BBCFG φ) : G.rsum (G'.lwk (· + G.length)) = G.sum G' := rfl

theorem BBCFG.lsum_lwk_eq_sum (G G' : BBCFG φ)
  : (G.lwk (G.length.liftnWk (· + G'.length))).lsum G' = G.sum G' := rfl

instance addBBCFG : Add (BBCFG φ) := ⟨BBCFG.sum⟩

/-- Attach a CFG to some of the outputs of a BBRegion, processing them recursively -/
def BBRegion.append_cfg (r : BBRegion φ) (G' : BBCFG φ) : BBRegion φ := match r with
  | cfg β n G => cfg β (n + G'.length) (Fin.addCases G (BBRegion.lwk (· + n) ∘ G'.targets))

def BBRegion.num_defs : BBRegion φ → ℕ
  | cfg β _ _ => β.body.num_defs

def BBRegion.ltimes_cfg (r : BBRegion φ) (G' : BBCFG φ) : BBRegion φ
  := r.append_cfg (G'.lwk (· + r.num_defs))

-- NOTE: rsum does not really make semantic sense

/-- Attach a CFG to a BBRegion which is totally disjoint.

Semantically, this is a no-op, and so is useful to define dead-code elimination
-/
def BBRegion.sum_cfg (r : BBRegion φ) (G' : BBCFG φ) : BBRegion φ := match r with
  | cfg β n G => cfg (β.lwk (n.liftnWk (· + G'.length))) (n + G'.length) (Fin.addCases
    (BBRegion.lwk (n.liftnWk (· + G'.length)) ∘ G)
    (BBRegion.lwk (· + n) ∘ G'.targets))

/-- Normalize a region to a BBRegion -/
def Region.toBBRegion : Region φ → BBRegion φ
  | br ℓ e => BBRegion.cfg ⟨Body.nil, Terminator.br ℓ e⟩ 0 Fin.elim0
  | let1 a r => BBRegion.let1 a r.toBBRegion
  | let2 a r => BBRegion.let2 a r.toBBRegion
  | case e s t => BBRegion.case e s.toBBRegion t.toBBRegion
  | cfg r n G => r.toBBRegion.ltimes_cfg ⟨n, λi => (G i).toBBRegion⟩

@[simp]
def Body.isNil : Body φ → Bool
  | nil => true
  | _ => false

def Block.isTerminator (b : Block φ) : Bool := b.body.isNil

def Block.IsTerminator (b : Block φ) : Prop := b.body = Body.nil

@[simp]
def BBRegion.isTerminator : BBRegion φ → Bool
  | cfg β n _ => β.isTerminator ∧ n = 0

inductive BBRegion.IsTerminator : BBRegion φ → Prop
  | br ℓ e : IsTerminator (BBRegion.cfg ⟨Body.nil, Terminator.br ℓ e⟩ 0 Fin.elim0)

@[simp]
def Terminator.toBlock_is_terminator
  (t : Terminator φ) : t.toBlock.IsTerminator := by constructor

def TRegion.isTerminator : TRegion φ → Bool
  | cfg _ n _ => n = 0
  | _ => false

inductive TRegion.IsTerminator : TRegion φ → Prop
  | cfg t G : IsTerminator (TRegion.cfg t 0 G)

def Region.isTerminator : Region φ → Bool
  | br _ _ => true
  | case _ s t => s.isTerminator ∧ t.isTerminator
  | _ => false

inductive Region.IsTerminator : Region φ → Prop
  | br ℓ e : IsTerminator (br ℓ e)
  | case e s t : IsTerminator s → IsTerminator t → IsTerminator (case e s t)

@[simp]
def Terminator.toRegion_is_terminator
  (t : Terminator φ) : t.toRegion.IsTerminator := by induction t <;> constructor <;> assumption

def Region.toTerminator (k : ℕ) : Region φ → Terminator φ
  | br ℓ e => Terminator.br ℓ e
  | case e s t => Terminator.case e (s.toTerminator k) (t.toTerminator k)
  | let1 _ r => (r.toTerminator k).lwk (· - 1)
  | let2 _ r => (r.toTerminator k).lwk (· - 2)
  | cfg r n G =>
    let r' := r.toTerminator n;
    let σG := λi => if h : i < n
      then (G ⟨i, h⟩).toTerminator k
      else Terminator.br (i - n) (Term.var 0);
    Terminator.lwk (· - n) (Nat.rec r' (λ_ r => r.lsubst σG) k)

def TRegion.toTerminator (k : ℕ) : TRegion φ → Terminator φ
  | let1 _ r => (r.toTerminator k).lwk (· - 1)
  | let2 _ r => (r.toTerminator k).lwk (· - 2)
  | cfg r n G =>
    let σG := λi => if h : i < n
      then (G ⟨i, h⟩).toTerminator k
      else Terminator.br (i - n) (Term.var 0);
    Terminator.lwk (· - n) (Nat.rec r (λ_ r => r.lsubst σG) k)

theorem Region.IsTerminator.eq_coe (k : ℕ) {r : Region φ} (h : r.IsTerminator)
  : r = r.toTerminator k := by induction h with
  | br _ _ => rfl
  | case _ _ _ _ _ Is It => rw [toTerminator, Terminator.toRegion, <-Is, <-It]

theorem Terminator.toTerminator_toRegion (k : ℕ) (r : Terminator φ)
  : r.toRegion.toTerminator k = r := by induction r with
  | br _ _ => rfl
  | case _ _ _ => simp [Region.toTerminator, toRegion, *]

theorem TRegion.IsTerminator.eq_cfg (k : ℕ) {r : TRegion φ} (h : r.IsTerminator)
  : r = TRegion.cfg (r.toTerminator k) 0 Fin.elim0 := by cases h with
  | cfg r _ =>
    simp only [toTerminator, tsub_zero, not_lt_zero', ↓reduceDite, Terminator.lwk_id',
    cfg.injEq, heq_eq_eq, true_and]
    constructor
    . simp only [Terminator.lsubst_id']
      induction k with
      | zero => rfl
      | succ k I => rw [<-I]
    . funext i; exact i.elim0

def Region.isBlock : Region φ → Bool
  | br _ _ => true
  | case _ s t => s.isTerminator ∧ t.isTerminator
  | let1 _ r => r.isBlock
  | let2 _ r => r.isBlock
  | cfg _ _ _ => false

inductive Region.IsBlock : Region φ → Prop
  | br ℓ e : IsBlock (br ℓ e)
  | ite e s t : IsBlock s → IsBlock t → IsBlock (case e s t)
  | let1 a r : IsBlock r → IsBlock (let1 a r)
  | let2 a r : IsBlock r → IsBlock (let2 a r)

theorem Region.IsTerminator.is_block {r : Region φ} (h : r.IsTerminator) : r.IsBlock := by
  induction h <;> constructor <;> assumption

def Region.isTRegion : Region φ → Bool
  | let1 _ r => r.isTRegion
  | let2 _ r => r.isTRegion
  | cfg r _ G => r.isTerminator ∧ ∀i, (G i).isTRegion
  | _ => false

inductive Region.IsTRegion : Region φ → Prop
  | let1 a r : IsTRegion r → IsTRegion (let1 a r)
  | let2 a r : IsTRegion r → IsTRegion (let2 a r)
  | cfg r n G : IsTerminator r → (∀i : Fin n, IsTRegion (G i)) → IsTRegion (cfg r n G)

def TRegion.cfg_case (e : Term φ) (s t : TRegion φ) : TRegion φ
  := TRegion.cfg (Terminator.case e (Terminator.br 0 (Term.var 0)) (Terminator.br 1 (Term.var 0))) 2
    (λ| 0 => s.lwk (· + 2) | 1 => t.lwk (· + 2))

def TRegion.case (e : Term φ) (s t : TRegion φ) : TRegion φ :=
  match s, t with
  | cfg s sn sG, cfg t tn tG => cfg ((s.lwk (sn.liftnWk (· + tn))).case e (t.lwk (· + sn)))
    (sn + tn) (Fin.addCases
      (TRegion.lwk (sn.liftnWk (· + tn)) ∘ sG)
      (TRegion.lwk (· + sn) ∘ tG))
  | s, t => s.cfg_case e t

/-- Attach a CFG to some of the outputs of a `TRegion`, processing them recursively -/
def TRegion.append_cfg (r : TRegion φ) (G' : TCFG φ) : TRegion φ := match r with
  | let1 a r => (r.append_cfg G').let1 a
  | let2 a r => (r.append_cfg G').let2 a
  | cfg t n G => cfg t (n + G'.length) (Fin.addCases G (TRegion.lwk (· + n) ∘ G'.targets))

@[simp]
def TRegion.num_defs : TRegion φ → ℕ
  | let1 _ r => r.num_defs + 1
  | let2 _ r => r.num_defs + 2
  | cfg _ _ _ => 0

def TRegion.ltimes_cfg (r : TRegion φ) (G' : TCFG φ) : TRegion φ
  := r.append_cfg (G'.lwk (· + r.num_defs))

def Region.toTRegion : Region φ → TRegion φ
  | br ℓ e => TRegion.cfg (Terminator.br ℓ e) 0 Fin.elim0
  | case e s t => TRegion.case e s.toTRegion t.toTRegion
  | let1 a r => r.toTRegion.let1 a
  | let2 a r => r.toTRegion.let2 a
  | cfg r n G => r.toTRegion.ltimes_cfg ⟨n, λi => (G i).toTRegion⟩

def Region.append_cfg (r : Region φ) (G' : CFG φ) : Region φ := match r with
  | let1 a r => (r.append_cfg G').let1 a
  | let2 a r => (r.append_cfg G').let2 a
  | cfg r n G => cfg r (n + G'.length) (Fin.addCases G (Region.lwk (· + n) ∘ G'.targets))
  | r => cfg r G'.length G'.targets

def Region.append_cfg' (r : Region φ) (G' : CFG φ) : Region φ := match r with
  | let1 a r => (r.append_cfg' G').let1 a
  | let2 a r => (r.append_cfg' G').let2 a
  | r => cfg r G'.length G'.targets

theorem TRegion.coe_toRegion_append_cfg (r : TRegion φ) (G' : TCFG φ)
  : (r : Region φ).append_cfg G' = r.append_cfg G' := by
  induction r with
  | cfg =>
    simp only [toRegion, Region.append_cfg, TCFG.toCFG, Region.cfg.injEq, heq_eq_eq, true_and]
    funext i
    simp only [Fin.addCases]
    split
    . rfl
    . simp only [Function.comp_apply, eq_rec_constant, TRegion.toRegion_lwk]
  | _ => simp [Region.append_cfg, *]

@[simp]
def Region.num_defs : Region φ → ℕ
  | let1 _ r => r.num_defs + 1
  | let2 _ r => r.num_defs + 2
  | _ => 0

@[simp]
theorem TRegion.num_defs_coe_toRegion (r : TRegion φ) : (r : Region φ).num_defs = r.num_defs := by
  induction r <;> simp [*]

def Region.ltimes_cfg (r : Region φ) (G' : CFG φ) : Region φ
  := r.append_cfg (G'.lwk (· + r.num_defs))

def Region.ltimes_cfg' (r : Region φ) (G' : CFG φ) : Region φ
  := r.append_cfg' (G'.lwk (· + r.num_defs))

theorem TRegion.coe_toRegion_ltimes_cfg (r : TRegion φ) (G' : TCFG φ)
  : (r : Region φ).ltimes_cfg G' = r.ltimes_cfg G' := by
  rw [ltimes_cfg, <-coe_toRegion_append_cfg, Region.ltimes_cfg]
  simp [TRegion.toRegion_lwk] -- TODO: this should probably be a simp lemma?

theorem Region.IsTerminator.append_eq_cfg {r : Region φ} (h : r.IsTerminator) (G : CFG φ)
  : r.append_cfg G = cfg r G.length G.targets := by cases h <;> rfl

theorem Region.IsTerminator.num_defs_eq_zero {r : Region φ} (h : r.IsTerminator)
  : r.num_defs = 0 := by cases h <;> rfl

theorem Region.IsTerminator.ltimes_eq_cfg {r : Region φ} (h : r.IsTerminator) (G : CFG φ)
    : r.ltimes_cfg G = cfg r G.length G.targets := by
  rw [ltimes_cfg, h.append_eq_cfg, h.num_defs_eq_zero]
  simp

theorem TRegion.IsTerminator.case {s t : TRegion φ}
  (e : Term φ) (h1 : s.IsTerminator) (h2 : t.IsTerminator)
  : (TRegion.case e s t).IsTerminator := by
  cases h1; cases h2
  constructor

theorem Region.IsTerminator.toTRegion {r : Region φ} (h : r.IsTerminator)
  : r.toTRegion.IsTerminator := by
  induction h with
  | br _ _ => constructor
  | case _ s t _ _ I1 I2 => rw [Region.toTRegion]; apply TRegion.IsTerminator.case <;> assumption

theorem Region.cfg_cast_eq (r : Region φ) (n n' : ℕ) (G : Fin n → Region φ) (h : n' = n)
  : cfg r n G = cfg r n' (G ∘ Fin.cast h) := by cases h; rfl

theorem Terminator.toRegion_lsubst (σ : Subst φ) (t : Terminator φ)
  : (t.lsubst σ).toRegion = t.toRegion.lsubst σ := by
  induction t generalizing σ with
  | br => simp only [lsubst, Region.lsubst]; rw [toRegion_vsubst]; rfl
  | _ => stop simp [toRegion, Terminator.lsubst, toRegion, Subst.liftn, *]

theorem TRegion.toRegion_toTerminator (r : TRegion φ) (k : ℕ)
  : r.toRegion.toTerminator k = r.toTerminator k := by
  induction r with
  | let1 _ r I => simp [toTerminator, Region.toTerminator, I]
  | let2 _ r I => simp [toTerminator, Region.toTerminator, I]
  | cfg r n G I =>
    simp only [Region.toTerminator, toTerminator]
    congr
    rw [r.toTerminator_toRegion]
    funext _ r
    congr
    funext i
    split
    . rw [I]
    . rfl

theorem Region.IsTerminator.toTRegion_eq_cfg (k : ℕ) {r : Region φ} (h : r.IsTerminator)
  : r.toTRegion = TRegion.cfg (r.toTerminator k) 0 Fin.elim0 := by
  induction h with
  | br _ _ => rfl
  | case _ _ _ _ _ Is It =>
    simp only [Region.toTRegion, TRegion.case, Is, It]
    congr
    simp
    simp
    funext i; exact i.elim0

theorem Region.IsTRegion.eq_toTRegion {r : Region φ} (h : r.IsTRegion) : r = r.toTRegion := by
  induction h with
  | let1 a r _ I => rw [toTRegion, TRegion.toRegion, <-I]
  | let2 a r _ I => rw [toTRegion, TRegion.toRegion, <-I]
  | cfg r n G hr _ I =>
    rw [toTRegion, <-TRegion.coe_toRegion_ltimes_cfg, <-hr.ltimes_eq_cfg ⟨n, G⟩]
    simp only
    rw [hr.toTRegion_eq_cfg 0]
    simp [TRegion.toRegion, ltimes_cfg, append_cfg]
    -- TODO: factor this out, flip eq_coe, etc...
    induction hr with
    | br =>
      simp only [num_defs, append_cfg, add_zero, Nat.liftnWk_id', lwk_id, Terminator.toRegion,
        Fin.addCases, not_lt_zero', ↓reduceDite, Nat.add_zero, Function.comp_apply, lwk_id',
        eq_rec_constant]
      rw [Region.cfg_cast_eq _ (0 + n) n _ (by simp)]
      congr
      funext i
      simp [Fin.subNat, <-I]
    | case _ _ _ hs ht =>
      simp only [append_cfg, num_defs, Nat.add_zero, add_zero, Nat.liftnWk_id', lwk_id,
        Terminator.toRegion, <- hs.eq_coe, <- ht.eq_coe, Fin.addCases, not_lt_zero', ↓reduceDite,
        Function.comp_apply, lwk_id', eq_rec_constant, zero_add, true_and]
      rw [Region.cfg_cast_eq _ (0 + n) n _ (by simp)]
      congr
      funext i
      simp [Fin.subNat, <-I]

-- TODO: change TRegion.case, etc to something else since it's not _really_ case under coe...

@[simp]
theorem TRegion.toRegion_is_tRegion (r : TRegion φ) : r.toRegion.IsTRegion := by
  induction r <;> constructor <;> simp [*]

theorem Region.IsBlock.not_tRegion {r : Region φ} (h : r.IsBlock) : ¬r.IsTRegion := by
  induction h <;> intro h' <;> cases h' <;> contradiction

theorem Region.IsTerminator.not_tRegion {r : Region φ} (h : r.IsTerminator) : ¬r.IsTRegion
  := h.is_block.not_tRegion

theorem Region.IsBlock.prepend {r : Region φ} (b : Body φ) (h : r.IsBlock) : (r.prepend b).IsBlock
  := by induction b <;> repeat first | assumption | constructor

-- TODO: this is an iff
theorem Region.IsTRegion.prepend {r : Region φ} (b : Body φ) (h : r.IsTRegion)
  : (r.prepend b).IsTRegion := by induction b <;> repeat first | assumption | constructor

@[simp]
theorem BBRegion.toRegion_is_tRegion (r : BBRegion φ) : r.toRegion.IsTRegion := by
  induction r with
  | cfg β n G I =>
    rw [toRegion]
    apply Region.IsTRegion.prepend
    constructor <;> simp [I]

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
