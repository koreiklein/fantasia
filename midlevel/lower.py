# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import itertools

from calculus.enriched import factor, endofunctor, formula

# NOTE: All the details of cached imports go in this module.
#  The current implementation does not concern itself with caching, or with
#  importing claims at the "highest" spot in a formula.  Later implementations will
#  want to dramatically increase performance by caching formulas as aggressively as
#  possible (With a clever extraction engine, caching causes essentially no performance
#  drain on the generated code.  With a clever factorization layer, caching causes
#  essentially no performance drain on interactive proof.).  To perform
#  this caching, the absorb function in this module will need to repeatedly factor
#  its endofunctors and bifunctors into one piece for each caching site.  Appropriate
#  instantiations can be performed at each site, and the final claim brought to its final
#  place at the "bottom" of the endofunctor.  The interface exposed by this module
#  is designed to allow the performance conscious implementer to make those changes to
#  this module exclusively.  The only impact on the rest of fantasia is that
#  more elaborate endofunctors G (with several caching sites) are returned by absorb.

# f, g: endofunctors
# x: a formula
# return: ('full',
#           ( G (very similar to g)
#           , i  (an integer measuring the "amount" of f that was absorbed
#           , an enriched arrow g.onObject(f.onObject(x)) -> G.onObject(x)))
#         OR
#         ('partial', (a, G, e, i)) if some of f can be absorbed
#             where a is an arrow: g.onObject(f.onObject(x)) -> G.onObject(e.onObject(x))
#                   and i is an integer measuring the "amount" of f that was absorbed.
#         OR
#         ('none', None) if nothing can be absorbed.
def absorb(x, f, g):
  A, F, i = _simplify(x, f, g)
  if i == 0:
    return 'none', None
  elif F.is_identity():
    return 'full', (g, i, A)
  else:
    return 'partial', (A, g, F, i)

# Note: The current specification of simplify is not amenable for adaptation of
# cached import.  A better specification would be for simplify to take 4 arguments:
# def simplify(x, As, f, Bs):
# simplify would return not only the arrow and simplified f', but also new variants of
# each As[i] and Bs[i] according to what has been imported.  This choice of specification
# may prove to be particularly nice for the kind of recursion needed to implement
# a correct cached import.

# return: _simplify(x, f, g) if f is atomic else return None
def _simplify_atomic(x, f, g):
  no_simplify = g.onObject(f.onObject(x)).identity(), f, 0
  if f.is_identity():
    return g.onObject(x).identity(), f, 0
  elif f.is_always():
    if g.covariant():
      return g.onArrow(f.onObject(x).forwardUnalways()), endofunctor.identity_functor, 1
    else:
      return g.onObject(f.onObject(x)).identity(), f, 0
  elif f.is_not():
    return no_simplify
  elif isinstance(f, endofunctor.Conjunction) and len(f.values) == 0:
    # f is already equal to the identity functor.
    return g.onObject(x).identity(), endofunctor.identity_functor, 1
  elif f.__class__ == endofunctor.And and len(f.values) == 1:
    if g.covariant():
      return g.onArrow(f.forwardForget()(x)), endofunctor.identity_functor, 1
    else:
      # Try to export the claim
      y = f.values[0]
      gen0 = factor.ef_match(endofunctor = g,
          ef_constraint = factor.apply_right(
            formula_constraint = factor.formula_replace(
              formula_constraint = factor.apply(
                formula_constraint = factor.exact(y),
                ef_constraint = factor.variance(True),
                f = lambda formula, a, b: b),
              covariant = True,
              allowed_variables = g.allQuantified(),
              f = lambda original, arrow, substitutions, y: (arrow, substitutions, y)),
            bi_constraint = factor.no_negations_right,
            f = lambda endofunctor, a, b: (b, a)))
      for B, (arrow, substitutions, ef) in gen0:
        # The constraints insure the following:
        #   B.onRight(arrow.src) == g
        #   arrow.tgt == ef.onObject(y)
        y_ = y
        for a, b in substitutions:
          y_ = y_.substituteVariable(a, b)
        ef_ = ef.do_substitutions()
        A, F, i = _simplify(
            x = y_,
            f = ef_,
            g = endofunctor.And(values = [formula.Not(f.onObject(x))], index = 0).compose(
              endofunctor.not_functor).compose(
                g))
        if F.is_identity():
          t = formula.And([y_, formula.Not(f.onObject(x))])
          AA = B.precomposeLeft(endofunctor.not_functor).transport_other_duplicating(arrow.src)(
              formula.Not(f.onObject(x))).forwardCompose(
                endofunctor.And(values = [formula.Not(f.onObject(x))], index = 0).compose(endofunctor.not_functor.compose(g)).onArrow(arrow).forwardCompose(
                A)).forwardCompose(
                  endofunctor.not_functor.compose(g).onArrow(
                    t.forwardApply() if f.index == 1 else t.forwardApplyOther())).forwardCompose(
                        g.onArrow(x.forwardDoubleDual()))
          AAA = g.onArrow(f.onObject(x).backwardUndoubleDual()).forwardCompose(AA)
          return (AAA,
                  endofunctor.identity_functor, i + 1)
      if y.__class__ == formula.And:
        return None
      else:
        return no_simplify
  elif f.__class__ == endofunctor.Or and len(f.values) == 1:
    if not g.covariant():
      return g.onArrow(f.backwardAdmit()(x)), endofunctor.identity_functor, 1
    else:
      # Try to contradict the claim
      raise Exception("Not yet implemented.")
  elif f.__class__ == endofunctor.Exists and len(f.bindings) == 0:
    if g.covariant():
      return (g.onArrow(formula.Arrow(
        src = f.onObject(x), tgt = x, basicArrow = x.translate().identity()))
        , endofunctor.identity_functor, 1)
    else:
      return (g.onArrow(formula.Arrow(
        tgt = f.onObject(x), src = x, basicArrow = x.translate().identity()))
        , endofunctor.identity_functor, 1)
  elif f.__class__ == endofunctor.Exists and len(f.bindings) == 1:
    binding = f.bindings[0]
    if binding.variable not in x.freeVariables():
      if g.covariant():
        return (g.onArrow(f.onObject(x).forwardRemoveSingleExists())
            , endofunctor.identity_functor, 1)
      else:
        if binding.is_ordinary():
          return (g.onArrow(f.onObject(x).backwardInstantiateIthOrdinary(0, binding.variable))
              , endofunctor.identity_functor, 1)
        else:
          # Strange case.  We need export only that binding.variable is in some domain?
          #  It's as if any variable in that domain is valid.
          return no_simplify
    else:
      # TODO: Consider ways of absorbing endofunctors f that quantify over variables
      #       that occur in f, but not in x.
      #  Note: Such considerations necessarily are at a broader scope than just this function.
      return no_simplify
  else:
    # f is not "atomic" (_split_non_atomic_endofunctor(f) should work)
    return None


# WARNING: The mutual recursion between the following 4 functions is quite intimate.

# x: a formula
# f, g: endofunctors
# return: (A, F, i) such that
#   A an arrow : g.onObject(f.onObject(x)) --> g.onObject(F.onObject(x))
#   F an endofunctor simpler than f, ideally F = ID
#   i an integer that measures the extent to which F is simpler than f.
#   i == 0 iff f == F
def _simplify(x, f, g):
  s = _simplify_atomic(x, f, g)
  if s is not None:
    return s
  else:
    a, b, f_to_ab, ab_to_f = _split_non_atomic_endofunctor(f)
    if g.covariant():
      split_arrow = g.onArrow(f_to_ab(x))
    else:
      split_arrow = g.onArrow(ab_to_f(x))
    arrow, simple_a, i = _simplify(x, a, b.compose(g))
    A, F, j = _simplify_a_simple(x, simple_a, b, g)
    return split_arrow.forwardCompose(arrow).forwardCompose(A), F, i + j

# x: a formula
# a, b, g: endofunctors
# _simplify(x, a, b.compose(g)) must return an i == 0
# return: _simplify(x, a.compose(b), g)
def _simplify_a_simple(x, a, b, g):
  arrow, simple_b, i = _simplify(a.onObject(x), b, g)
  if i == 0:
    return _simplify_a_simple_b_simple(x, a, b, g)
  else:
    # b was simplified, now maybe a can be simplified.
    A, F, j = _simplify_b_simple(x, a, simple_b, g)
    return arrow.forwardCompose(A), F, j + i

# x: a formula
# a, b, g: endofunctors
# _simplify(a.onObject(x), b, g) must return an i == 0
# return: _simplify(x, a.compose(b), g)
def _simplify_b_simple(x, a, b, g):
  arrow, simple_a, i = _simplify(x, a, b.compose(g))
  if i == 0:
    return _simplify_a_simple_b_simple(x, a, b, g)
  else:
    # a was simplified, now maybe b can be simplified.
    A, F, j = _simplify_a_simple(x, simple_a, b, g)
    return arrow.forwardCompose(A), F, j + i

# x: a formula
# a, b, g: endofunctors
# _simplify(a.onObject(x), b, g) must return an i == 0
# _simplify(x, a, b.compose(g)) must return an i == 0
# return: _simplify(x, a.compose(b), g)
# Note: The only opportunity for further simplification comes from
#       natural transforms on a.compose(b)
def _simplify_a_simple_b_simple(x, a, b, g):
  if a.is_identity():
    return _simplify(x, b, g)
  elif b.is_identity():
    return _simplify(x, a, g)
  else:
    a0, a1 = a.factor_right()
    b0, b1 = b.factor_left()
    if a1.is_not() and b0.is_not():
      # With two adjancent Not endofunctors, we can simplify.
      A, F, i = _simplify(x, a0.compose(b1), g)
      if b1.compose(g).covariant():
        return (b1.compose(g).onArrow(
            b0.onObject(a.onObject(x)).forwardUndoubleDual()).forwardCompose(A)
            , F
            , i + 1)
      else:
        return (b1.compose(g).onArrow(
          b0.onObject(a.onObject(x)).backwardDoubleDual()).forwardCompose(A)
          , F
          , i + 1)
    elif a1.is_always() and b0.is_always() and not b1.compose(g).covariant():
      A, F, i = _simplify(x, a.compose(b1), g)
      return (b1.compose(g).onArrow(
        b0.onObject(a.onObject(x)).backwardCojoin()).forwardCompose(A)
        , F
        , i + 1)
    else:
      # We implement no simplifications for other adjacent endofunctors.
      return g.onObject(b.onObject(a.onObject(x))).identity(), a.compose(b), 0

# f: an endofunctor that is not atomic (it can be split)
# return: a, b, f_to_ab, ab_to_f such that:
#   a and b are both endofunctors "simpler" than f.
#   f_to_ab is a natural transform : f --> a.compose(b)
#   ab_to_f is a natural transform : a.compose(b) --> f
def _split_non_atomic_endofunctor(f):
  if f.__class__ == endofunctor.Composite:
    a, b = f.factor_right()
    return a, b, lambda x: f.onObject(x).identity(), lambda x: f.onObject(x).identity()
  elif (isinstance(f, endofunctor.Conjunction)
      and len(f.values) == 1
      and f.values[0].__class__ == f.multiOp()):
    # Note: the implementation of this case is extraordinarily long.  Some clever
    # redesign could certainly avoid having to write such messy code.
    if f.index == 0:
      a = f.__class__(index = 0, values = f.values[0].values)
      b = endofunctor.identity_functor
      f_to_ab = (lambda x: formula.Arrow(
        src = f.onObject(x),
        tgt = b.onObject(a.onObject(x)),
        basicArrow = f.onObject(x).identity()))
      ab_to_f = (lambda x: formula.Arrow(
        src = b.onObject(a.onObject(x)),
        tgt = f.onObject(x),
        basicArrow = f.onObject(x).identity()))
      return a, b, f_to_ab, ab_to_f
    else:
      assert(f.index == 1)
      a = f.__class__(index = len(f.values[0].values), values = f.values[0].values)
      b = endofunctor.identity_functor
      def _prepend(x):
        result = [x]
        result.extend(f.values[0].values)
        return result
      def _append(x):
        result = list(f.values[0].values)
        result.append(x)
        return result
      n = len(f.values[0].values)
      f_to_ab = (lambda x: formula.Arrow(
        src = f.onObject(x),
        tgt = b.onObject(a.onObject(x)),
        basicArrow = f.onObject(x).translate().forwardCommute().forwardCompose(
          f.multiOp()(_prepend(x))._forwardMoveForward(0, n).translate())))
      ab_to_f = (lambda x: formula.Arrow(
        src = b.onObject(a.onObject(x)),
        tgt = f.onObject(x),
        basicArrow = f.multiOp()(_append(x)).forwardMoveBack(n, n).translate().forwardFollow(lambda t:
          t.forwardCommute())))
      return a, b, f_to_ab, ab_to_f
  elif isinstance(f, endofunctor.Conjunction) and len(f.values) > 1:
    if f.index == 0:
      a = f.__class__(values = f.values[0:1], index = 0)
      b = f.__class__(values = f.values[1], index = 0)
      f_to_ab = (lambda x: formula.Arrow(
        src = f.onObject(x),
        tgt = b.onObject(a.onObject(x)),
        basicArrow = f.onObject(x).translate().forwardAssociate()))
      ab_to_f = (lambda x: formula.Arrow(
        src = b.onObject(a.onObject(x)),
        tgt = f.onObject(x),
        basicArrow = f.onObject(x).translate().backwardAssociateOther()))
      return a, b, f_to_ab, ab_to_f
    else:
      a = f.__class__(values = f.values[1:], index = f.index - 1)
      b = f.__class__(values = f.values[0:1], index = 1)
      f_to_ab = (lambda x: formula.Arrow(
        src = f.onObject(x),
        tgt = b.onObject(a.onObject(x)),
        basicArrow = f.onObject(x).identity().translate()))
      ab_to_f = (lambda x: formula.Arrow(
        src = b.onObject(a.onObject(x)),
        tgt = f.onObject(x),
        basicArrow = f.onObject(x).identity().translate()))
      return a, b, f_to_ab, ab_to_f
  else:
    raise Exception("Endofunctor of class %s could not be split."%(f.__class__,))

