import Discretion
import DeBruijnSSA.BinSyntax.Syntax.Definitions

namespace BinSyntax

/-- Append two bodies, letting the second use the variables defined in the first -/
def Body.append (b b' : Body φ) : Body φ := match b with
  | nil => b'
  | let1 a t => let1 a (t.append b')
  | let2 a t => let2 a (t.append b')

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


-- TODO: make Body into a monoid this way

-- TODO: relationship between append and comp

-- TODO: define comp as append instead? removes the need for compn...

-- TODO: another issue: now there are _two_ monoid structures on Body

-- TODO: variant with a body followed by a weakening (WBody?). This is also a monoid, of course.

-- TODO: in fact, _this_ variant supports an _rtimes_ operation. Wow!

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

def Region.append_cfg (r : Region φ) (G' : CFG φ) : Region φ := match r with
  | let1 a r => (r.append_cfg G').let1 a
  | let2 a r => (r.append_cfg G').let2 a
  | cfg r n G => cfg r (n + G'.length) (Fin.addCases G (Region.lwk (· + n) ∘ G'.targets))
  | r => cfg r G'.length G'.targets

def Region.append_cfg' (r : Region φ) (G' : CFG φ) : Region φ := match r with
  | let1 a r => (r.append_cfg' G').let1 a
  | let2 a r => (r.append_cfg' G').let2 a
  | r => cfg r G'.length G'.targets
