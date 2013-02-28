# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic, enriched
from lib import common_vars


# Stating that a variable is a natural number.
class IsNatural(enriched.Logic):
  def __init__(self, n):
    self._n = n
    self.initMarkable([])

  def n(self):
    return self._n

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.n() == other.n()

  def __ne__(self, other):
    return not (self == other)

  def substituteVar(self, a, b):
    if self.n() == a:
      return IsNatural(b)
    else:
      return self

  def translate(self):
    return basic.Holds(natural = self.n().translate())

  def transpose(self):
    return enriched.Not(self)

# Stating some inequality (=, >=, <=) between two variables.
class Compare(enriched.Logic):
  # strict: a boolean indicating whether the inequality is strict.
  def __init__(self, lesser, greater, strict):
    self._lesser = lesser
    self._greater = greater
    self._strict = strict
    self.initMarkable([])

  def lesser(self):
    return self._lesser
  def greater(self):
    return self._greater
  def strict(self):
    return self._strict

  def __eq__(self, other):
    return self.__class__ == other.__class__ and (
        self.lesser() == other.lesser() and
        self.greater() == other.greater() and
        self.strict() == other.strict())

  def __ne__(self, other):
    return not (self == other)

  def substituteVar(self, a, b):
    lesser = self.lesser()
    greater = self.greater()
    if lesser == a:
      lesser = b
    if greater == a:
      greater = b
    return Compare(lesser = lesser, greater = greater, strict = self.strict())

  def translate(self):
    return basic.Holds(lesser = self.lesser().translate(), greater = self.greater().translate(),
        strict = self.strict())

  def transpose(self):
    return enriched.Not(self)

# Stating that the successor of the natural number a is b.
class Successor(enriched.Logic):
  def __init__(self, a, b):
    self._a = a
    self._b = b
    self.initMarkable([])

  def a(self):
    return self._a
  def b(self):
    return self._b

  def __eq__(self, other):
    return self.__class__ == other.__class__ and (
        self.a() == other.a() and
        self.b() == other.b())

  def __ne__(self, other):
    return not (self == other)

  def substituteVar(self, a, b):
    smaller = self.a()
    larger = self.b()
    if smaller == a:
      smaller = b
    if larger == a:
      larger = b
    return Successor(a = smaller, b = larger)

  def translate(self):
    return basic.Holds(succeeded = self.a().translate(),
        succeeding = self.b().translate())

  def transpose(self):
    return enriched.Not(self)

zero = enriched.Var('zero')

five = enriched.Var('5')

zero_natural = IsNatural(zero)

exists_five = enriched.Exists([five], IsNatural(five))

t = common_vars.t()
r = common_vars.r()
increasing = enriched.Forall([t, r],
    enriched.Implies(predicate = Successor(t, r),
      consequent = Compare(lesser = t, greater = r, strict = True)))

n = common_vars.n()
reflexivity = enriched.Forall([n],
    enriched.Implies(predicate = IsNatural(n),
      consequent = Compare(lesser = n, greater = n, strict = False)))

s = common_vars.s()
l = common_vars.l()
weakening = enriched.Forall([s, l],
    enriched.Implies(predicate = Compare(s, l, strict = True),
      consequent = Compare(s, l, strict = False)))

n = common_vars.n()
m = common_vars.m()
successorExists = enriched.Forall([n],
    enriched.Implies(predicate = IsNatural(n),
      consequent = enriched.Exists([m],
        enriched.And([IsNatural(m), Successor(n, m), Successor(n, m)]))))

a = common_vars.a()
b = common_vars.b()
c = common_vars.c()
transitivity = enriched.Forall([a, b, c],
    enriched.Implies(predicate = enriched.And([ Compare(a, b, False)
                                              , Compare(b, c, True)]),
                     consequent = Compare(a, c, True)))


# This definition of induction should by no means be considered final.
# As the combinators in calculus.enriched become more sophisticated, we may
# wish to give more elaborate definitions of induction.
# For example, all claims about numbers being natural might be hidden.
# For another example, we may use m = n + 1 instead of natural.Successor(n, m).

n = common_vars.n()
m = common_vars.m()
k = common_vars.k()
# claim: a function from a variable to a formula saying the claim holds of
# that variable.
def byInduction(claim):
  return enriched.Implies(
      predicate = enriched.And([ claim(zero)
                               , enriched.Forall([n]
                               , enriched.Implies(
                                  predicate = enriched.And([ IsNatural(n)
                                                           , claim(n)]),
                                  consequent =
                                    enriched.Exists([m],
                                      enriched.And([ IsNatural(m)
                                                   , Successor(n, m)
                                                   , claim(m)]))))]),
      consequent = enriched.Forall([k],
        enriched.Implies(
          predicate = IsNatural(k),
          consequent = claim(k))))

