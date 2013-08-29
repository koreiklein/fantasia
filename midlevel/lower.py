# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import factor, endofunctor

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
  # TODO(koreiklein): This function has become a MONSTER!
  # The only way I was able to write it was by drawing a series of elaborate diagrams
  # showing exactly what parts of the chain of formula -- ef -- ef -- ef ... -- ef
  # had been detected as amenable to absorb, and drawing the decision tree for
  # which part of the chain to test for absorbability next.
  # Coding this function this way wasn't pretty, but I was able to do it.
  # I would not want anyone else (including a future version of myself) to have to
  # suffer through those diagrams again if it can be avoided.

  # Figure out whether it is possible to get the same or reasonably similar behavior
  # without all this mess.
  if f.is_identity():
    return ('full', (g, 0, g.onObject(x).identity()))
  else:
    a, b = f.factor_right()
    small_absorb = _absorb_small(a.onObject(x), b, g)
    if small_absorb is not None:
      G, A = small_absorb
      tag, p = absorb(x, a, G)
      if tag == 'full':
        GG, i, AA = p
        return 'full', (GG, i + 1, A.forwardCompose(AA))
      elif tag == 'partial':
        AA, GG, e, i = p
        return 'partial', (A.forwardCompose(AA), GG, e, i + 1)
      elif tag == 'none':
        return 'partial', (A, G, a, 1)
      else:
        raise Exception("Unrecognized tag %s"%(tag,))
    else:
      tag, p = absorb(x, a, b.compose(g))
      if tag == 'full':
        G, i, A = p
        B, GG = G.factor_left()
        pp = _absorb_small(x, B, GG)
        if pp is None:
          return 'partial', (A, GG, B, i)
        else:
          GGG, AA = pp
          return 'full', (GGG, i + 1, A.forwardCompose(AA))
      elif tag == 'partial':
        A, G, e, i = p
        B, GG = G.factor_left()
        pp = _absorb_small(e.onObject(x), B, GG)
        if pp is None:
          return 'partial', (A, GG, e.compose(B), i)
        else:
          GGG, AA = pp
          ppp = _absorb_small(x, e, GGG)
          if ppp is None:
            return 'partial', (A.forwardCompose(AA), GGG, e, i + 1)
          else:
            GGGG, AAA = ppp
            return 'full', (GGGG, i + 2, A.forwardCompose(AA).forwardCompose(AAA))
      elif tag == 'none':
        return 'none', None
      else:
        raise Exception("Unrecognized tag %s"%(tag,))

# g: an endofunctor
# b: a "small" endofunctor
# x: a formula
# return: (G, an enriched arrow g.onObject(b.onObject(x)) --> G.onObject(x))
#         or None if no such arrow can be "easily" constructed.
def _absorb_small(x, b, g):
  if b.__class__ == endofunctor.And:
    for bi, y in factor.all_endofunctor_factorizations_of_small_endofunctor(b):
      f = bi.left_onObject(x)
      p = export(y, f)
      if p is None:
        return None
      else:
        F, A = p
  elif b.__class__ == endofunctor.Or:
    raise Exception("Not yet implemented.")
  elif b.__class__ == endofunctor.Exists:
    raise Exception("Not yet implemented.")
  elif b.__class__ == endofunctor.BoundedVariableBinding:
    raise Exception("Not yet implemented.")
  elif b.__class__ == endofunctor.OrdinaryVariableBinding:
    raise Exception("Not yet implemented.")
  elif b.__class__ == endofunctor.Hidden:
    raise Exception("Not yet implemented.")
  elif b.__class__ == endofunctor.AppendIffRight:
    raise Exception("Not yet implemented.")
  elif b.__class__ == endofunctor.AppendIffLeft:
    raise Exception("Not yet implemented.")
  elif b.__class__ == endofunctor.DirectTranslate:
    raise Exception("Not yet implemented.")
  else:
    raise Exception("A supposedly small endofunctor was of an inappropriate class %s"%(b.__class__,))

# f: an endofunctor
# x: a formula
# return: (F, an arrow : f.onObject(x) -> F.onObject(Or([]) if f.covariant() else And([])))
#         or None if such an arrow can not be constructed.
def export(x, f):
  raise Exception("Not yet implemented.")
