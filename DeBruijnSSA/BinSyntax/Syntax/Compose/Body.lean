import DeBruijnSSA.BinSyntax.Syntax.Definitions
import DeBruijnSSA.BinSyntax.Syntax.Fv.Basic

namespace BinSyntax

/-- Append two bodies, letting the second use the variables defined in the first -/
def Body.append (b b' : Body φ) : Body φ := match b with
  | nil => b'
  | let1 a t => let1 a (t.append b')
  | let2 a t => let2 a (t.append b')

theorem Body.append_num_defs (b b' : Body φ)
  : (b.append b').num_defs = b.num_defs + b'.num_defs := by
  induction b generalizing b' <;> simp_arith [append, num_defs, *]

theorem Body.fv_append (b b' : Body φ) : (b.append b').fv = b.fv + b'.fv.liftnFv b.num_defs := by
  induction b generalizing b'
  <;> simp [append, fv, <-Multiset.liftnFv_add, add_assoc, Nat.add_comm, *]

theorem Body.wk_append (ρ : ℕ → ℕ) (b b' : Body φ)
  : (b.append b').wk ρ = (b.wk ρ).append (b'.wk (Nat.liftnWk b.num_defs ρ)) := by
  induction b generalizing ρ b' with
  | nil => rfl
  | _ => simp only [wk, *, append, num_defs, let1.injEq, true_and, Nat.liftnWk_succ]; congr

@[simp]
theorem Body.nil_append (b : Body φ) : nil.append b = b := rfl

@[simp]
theorem Body.append_nil (b : Body φ) : b.append nil = b := by
  induction b <;> simp [append, *]

theorem Body.append_assoc (b b' b'' : Body φ)
  : (b.append b').append b'' = b.append (b'.append b'') := by
  induction b generalizing b' b'' <;> simp [append, *]

theorem Body.let1_append (a : Term φ) (b b' : Body φ)
  : (let1 a b).append b' = let1 a (b.append b') := by
  simp only [append, let1.injEq, *]

theorem Body.let2_append (a : Term φ) (b b' : Body φ)
  : (let2 a b).append b' = let2 a (b.append b') := by
  simp only [append, let2.injEq, *]

/-- Append two bodies, weakening the second so that it shares the same inputs as the first -/
def Body.ltimes (b b' : Body φ) : Body φ := b.append (b'.wk (· + b.num_defs))

theorem Body.ltimes_num_defs (b b' : Body φ) : (b.ltimes b').num_defs = b.num_defs + b'.num_defs
  := by simp [ltimes, append_num_defs, Body.num_defs_wk]

theorem Body.wk_ltimes (ρ : ℕ → ℕ) (b b' : Body φ)
  : (b.ltimes b').wk ρ = (b.wk ρ).ltimes (b'.wk ρ) := by
  simp only [ltimes, wk_append, wk_wk]
  congr
  funext n
  simp [Function.comp_apply, Nat.liftnWk, num_defs_wk]

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

@[simp]
theorem Body.ltimes_nil (b : Body φ) : b.ltimes nil = b := by simp [ltimes]

@[simp]
theorem Body.nil_ltimes (b : Body φ) : nil.ltimes b = b :=
  by simp only [ltimes, num_defs, add_zero, nil_append]; exact b.wk_id

theorem Body.let1_ltimes (a : Term φ) (b b' : Body φ)
  : (let1 a b).ltimes b' = let1 a (b.ltimes (b'.wk Nat.succ)) := by
  simp only [ltimes, append, wk_append, wk_wk]
  congr
  funext n
  simp_arith

theorem Body.let2_ltimes (a : Term φ) (b b' : Body φ)
  : (let2 a b).ltimes b' = let2 a (b.ltimes (b'.wk (λn => n + 2))) := by
  simp only [ltimes, append, wk_append, wk_wk]
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
