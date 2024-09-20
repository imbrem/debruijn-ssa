# debruijn-ssa

This repository contains a formalization of SSA in Lean 4, along with it's equational semantics and a proof of completeness w.r.t an (otherwise unformalized) categorical semantics.

Unlike the related [`freyd-ssa`](github.com/imbrem/freyd-ssa), this version uses deBruijn indices rather than variable names, hence the repository name.
