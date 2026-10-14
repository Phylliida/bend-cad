# Semiring laws of Base's unary Nat (Nat.add, Nat.mul), by Peano induction.
# These feed the Nat normalizer (lib/natring.bend), which then discharges the
# arithmetic in the binary-number proofs.
#
# A rewrite %e : P with e : {a == b : T} needs the goal to be P with b at each
# _, and continues with a there. So lemmas are stated {target == source}: a
# rewrite turns the source form into the target form.

import Base

# Addition
# --------

def add_zero(a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      add_zero(b)
    case 1n+p:
      %add_succ(b, p) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

# a + (b + c) = b + (a + c)
def add_swap(a: Nat, +b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(b, Nat.add(p, c)) : {1n+Nat.add(p, Nat.add(b, c)) == _ : Nat}
      %add_swap(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

# Multiplication
# --------------

def mul_zero(a: Nat) -> {0n == Nat.mul(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      mul_zero(p)

def mul_one(a: Nat) -> {a == Nat.mul(a, 1n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %mul_one(p) : {1n+p == 1n+_ : Nat}
      {==}

# a + a * b = a * (1 + b)
def mul_succ(+a: Nat, +b: Nat) -> {Nat.add(a, Nat.mul(a, b)) == Nat.mul(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %mul_succ(p, b) : {1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) == 1n+Nat.add(b, _) : Nat}
      %add_swap(p, b, Nat.mul(p, b)) : {1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) == 1n+_ : Nat}
      {==}

def mul_comm(+a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n:
      mul_zero(b)
    case 1n++p:
      %mul_succ(b, p) : {Nat.add(b, Nat.mul(p, b)) == _ : Nat}
      %mul_comm(p, b) : {Nat.add(b, Nat.mul(p, b)) == Nat.add(b, _) : Nat}
      {==}

# a * c + b * c = (a + b) * c
def mul_add_r(a: Nat, -b: Nat, +c: Nat) -> {Nat.add(Nat.mul(a, c), Nat.mul(b, c)) == Nat.mul(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %mul_add_r(p, b, c) : {Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)) == Nat.add(c, _) : Nat}
      %add_assoc(c, Nat.mul(p, c), Nat.mul(b, c)) : {_ == Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))) : Nat}
      {==}

# a * b + a * c = a * (b + c)
def mul_add_l(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.mul(a, b), Nat.mul(a, c)) == Nat.mul(a, Nat.add(b, c)) : Nat}:
  %mul_comm(Nat.add(b, c), a) : {Nat.add(Nat.mul(a, b), Nat.mul(a, c)) == _ : Nat}
  %mul_add_r(b, c, a) : {Nat.add(Nat.mul(a, b), Nat.mul(a, c)) == _ : Nat}
  %mul_comm(a, b) : {Nat.add(Nat.mul(a, b), Nat.mul(a, c)) == Nat.add(_, Nat.mul(c, a)) : Nat}
  %mul_comm(a, c) : {Nat.add(Nat.mul(a, b), Nat.mul(a, c)) == Nat.add(Nat.mul(a, b), _) : Nat}
  {==}

def mul_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(Nat.mul(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %mul_add_r(b, Nat.mul(p, b), c) : {Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))) == _ : Nat}
      %mul_assoc(p, b, c) : {Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))) == Nat.add(Nat.mul(b, c), _) : Nat}
      {==}

# a * (b * c) = b * (a * c)
def mul_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(b, Nat.mul(a, c)) : Nat}:
  %mul_comm(Nat.mul(b, c), a) : {_ == Nat.mul(b, Nat.mul(a, c)) : Nat}
  %mul_assoc(b, c, a) : {_ == Nat.mul(b, Nat.mul(a, c)) : Nat}
  %mul_comm(c, a) : {Nat.mul(b, Nat.mul(c, a)) == Nat.mul(b, _) : Nat}
  {==}
