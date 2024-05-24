import DeBruijnSSA.BinSyntax.Syntax.Definitions

namespace BinSyntax

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
