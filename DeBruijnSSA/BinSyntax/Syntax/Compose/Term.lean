import DeBruijnSSA.BinSyntax.Syntax.Subst
import DeBruijnSSA.BinSyntax.Syntax.Rewrite
import DeBruijnSSA.InstSet

namespace BinSyntax

namespace Term

def nil {φ} : Term φ := var 0

def seq {φ} (r s : Term φ) : Term φ := let1 r s.wk1

def pseq {φ} (r s : Term φ) : Term φ := s.wk1.subst r.subst0

def pi_l {φ} : Term φ := let2 nil (var 1)

def pi_r {φ} : Term φ := let2 nil (var 0)

def prod {φ} (l r : Term φ) : Term φ := let1 nil (pair l.wk1 r.wk1)

def tensor {φ} (l r : Term φ) : Term φ := let2 nil (pair l.wk1.wk0 r.wk1.wk1)

def split {φ} : Term φ := prod nil nil

def assoc {φ} : Term φ := let2 nil (let2 (var 1) (pair (var 1) (pair (var 0) (var 2))))

def assoc_inv {φ} : Term φ := let2 nil (let2 (var 0) (pair (pair (var 3) (var 1)) (var 0)))

def swap {φ} : Term φ := let2 nil (pair (var 0) (var 1))

def zero {φ} : Term φ := abort nil

def inj_l {φ} : Term φ := inl nil

def inj_r {φ} : Term φ := inr nil

def coprod {φ} (r s : Term φ) : Term φ := case nil r.wk1 s.wk1

def sum {φ} (l r : Term φ) : Term φ := coprod (l.seq inj_l) (r.seq inj_r)

def join {φ} : Term φ := coprod nil nil

def aassoc {φ} : Term φ := sorry

def aassoc_inv {φ} : Term φ := sorry

def aswap {φ} : Term φ := sorry
