# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic, enriched
from lib import common_vars

from sets import Set

class Natural(enriched.Logic):
  # n: a python natural number
  def __init__(self, n):
    self._n = n
    self.initMarkable([])

  def __repr__(self):
    return "%s : N"%(self.n(),)

  def n(self):
    return self._n

  def freeVariables(self):
    return Set([self.n()])

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.n() == other.n()

  def __ne__(self, other):
    return not (self == other)

  def substituteVar(self, a, b):
    if self.n() == a:
      return IsNatural(b)
    else:
      return self

  def transposeIsNot(self):
    return True

  def translate(self):
    return basic.Holds(natural = self.n().translate())

class Equal(enriched.Logic):
  def __init__(self, a, b):
    self._a = a
    self._b = b
    self.initMarkable([])

  def a(self):
    return self.a()
  def b(self):
    return self.b()

  def freeVariables(self):
    return Set([self.a(), self.b()])

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.a() == other.a() and self.b() == other.b()

  def __ne__(self, other):
    return not (self == other)

  def substituteVar(self, x, y):
    a = self.a()
    b = self.b()
    if a == x:
      a = y
    if b == x:
      b = y
    return Successor(a = a, b = b)

  def transposeIsNot(self):
    return True

  def translate(self):
    return basic.Holds(naturalEqualLeft = self.a().translate,
        naturalEqualRight = self.b().translate())

class Successor(enriched.Logic):
  def __init__(self, a, b):
    self._a = a
    self._b = b
    self.initMarkable([])

  def __repr__(self):
    return "%s + 1 == %s"%(self.a(), self.b())

  def a(self):
    return self._a
  def b(self):
    return self._b

  def freeVariables(self):
    return Set([self.a(), self.b()])

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.a() == other.a() and self.b() == other.b()

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

  def transposeIsNot(self):
    return True

n = common_vars.n()
eqIdentitiy = enriched.Forall([n],
    enriched.Implies(
      predicate = Natural(n),
      consequent = Equal(n, n)))

n = common_vars.n()
m = common_vars.m()
eqSymmetric = enriched.Forall([n, m],
    enriched.Implies(
      predicate = Equal(n, m),
      consequent = Equal(m, n)))

a = common_vars.a()
b = common_vars.b()
c = common_vars.c()
eqSymmetric = enriched.Forall([a, b, c],
    enriched.Implies(
      predicate = enriched.And([Equal(a, b), Equal(b, c)]),
      consequent = Equal(a, c)))

zero = enriched.Var('zero')

zeroIsNatural = Natural(zero)

n = common_vars.n()
m = common_vars.m()
successorExists = enriched.Forall([n],
    enriched.Implies(
      predicate = Natural(n),
      consequent = enriched.Exists([m],
        enriched.And([Natural(m), Successor(n, m)]))))

a = common_vars.a()
n = common_vars.n()
m = common_vars.m()
successorUnique = enriched.Forall([a, n, m],
    enriched.Implies(
      predicate = enriched.And([ Successor(a, n), Successor(a, m) ]),
      consequent = Equal(n, m)))

b = common_vars.b()
n = common_vars.n()
m = common_vars.m()
successorInjective = enriched.Forall([b, n, m],
    enriched.Implies(
      predicate = enriched.And([ Successor(n, b), Successor(m, b) ]),
      consequent = Equal(n, m)))

n = common_vars.n()
successorNotZero = enriched.Forall([n],
    enriched.Not(Successor(n, zero)))

def byInduction(claim):
  n = common_vars.n()
  m = common_vars.m()
  k = common_vars.k()
  return enriched.Implies(
      predicate = enriched.And([ claim(zero)
                               , enriched.Forall([n]
                               , enriched.Implies(
                                  predicate = enriched.And([ Natural(n)
                                                           , claim(n)]),
                                  consequent =
                                    enriched.Exists([m],
                                      enriched.And([ Natural(m)
                                                   , Successor(n, m)
                                                   , claim(m)]))))]),
      consequent = enriched.Forall([k],
        enriched.Implies(
          predicate = Natural(k),
          consequent = claim(k))))

R = common_vars.R()
allInduction = enriched.Forall([R],
    byInduction(lambda v: enriched.Holds(holding = R, held = v)))

n = common_vars.n()
m = common_vars.m()
t = common_vars.t()
lessVar = common_vars.less()
defLessStart = enriched.Forall([n, m],
    enriched.Implies(
      predicate = enriched.And([Natural(n), Natural(m)]),
      consequent = enriched.true))
defLessArrow = defLessStart.forwardOnBodyFollow(lambda x:
    x.forwardOnIthFollow(2, lambda one:
      one.forwardAppendDefinition(
        relation = enriched.Holds(holding = lessVar, less = n, more = m),
        definition = enriched.Or([ Successor(n, m)
                                 , enriched.Exists([t],
                                     enriched.And(
                                       [ Successor(n, t)
                                       , enriched.Holds(holding = lessVar,
                                         less = t, more = m)]))]))))

defLessArrow.translate()
defLess = defLessArrow.tgt()
