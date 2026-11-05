import Base

# A function `f` that is a bijection between two subsets, together with
# its inverse.
#
# `A` and `B` are the surrounding types.  `in_domain` selects the subset
# of `A` on which `f` is defined, and `in_codomain` selects the subset of
# `B` that `f` maps onto.  `f` takes an `a` with a proof that
# `in_domain(a)` holds, and `inverse` takes a `b` with a proof that
# `in_codomain(b)` holds.

# `inverse` is a left inverse of `f`: applying `f` and then `inverse`
# returns the original value.

def LeftInverse(-A: Type, -B: Type,
  -in_domain: @a: A -> Bool, -in_codomain: @b: B -> Bool,
  -f: @a: A -> @-valid: {in_domain(a) == True{} : Bool} -> B,
  -inverse: @b: B -> @-valid: {in_codomain(b) == True{} : Bool} -> A) -> Type:
  @a: A -> @+valid: {in_domain(a) == True{} : Bool} ->
    Exists({in_codomain(f(a, valid)) == True{} : Bool}, valid_result =>
      {inverse(f(a, valid), valid_result) == a : A})

# `inverse` is a right inverse of `f`: applying `inverse` and then `f`
# returns the original value.

def RightInverse(-A: Type, -B: Type,
  -in_domain: @a: A -> Bool, -in_codomain: @b: B -> Bool,
  -f: @a: A -> @-valid: {in_domain(a) == True{} : Bool} -> B,
  -inverse: @b: B -> @-valid: {in_codomain(b) == True{} : Bool} -> A) -> Type:
  @b: B -> @+valid: {in_codomain(b) == True{} : Bool} ->
    Exists({in_domain(inverse(b, valid)) == True{} : Bool}, valid_result =>
      {f(inverse(b, valid), valid_result) == b : B})

# With both, `f` is a bijection from the domain onto the codomain, and
# `inverse` is its unique inverse.

def Bijection(-A: Type, -B: Type,
  -in_domain: @a: A -> Bool, -in_codomain: @b: B -> Bool,
  -f: @a: A -> @-valid: {in_domain(a) == True{} : Bool} -> B,
  -inverse: @b: B -> @-valid: {in_codomain(b) == True{} : Bool} -> A) -> Type:
  LeftInverse(A, B, in_domain, in_codomain, f, inverse) &
  RightInverse(A, B, in_domain, in_codomain, f, inverse)
