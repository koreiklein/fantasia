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
      return Natural(b)
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
    return self._a
  def b(self):
    return self._b

  def __repr__(self):
    return "%s == %s"%(self.a(), self.b())

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
    return Equal(a = a, b = b)

  def transposeIsNot(self):
    return True

  def translate(self):
    return basic.Holds(naturalEqualLeft = self.a().translate(),
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
eqTransitive = enriched.Forall([a, b, c],
    enriched.Implies(
      predicate = enriched.And([Equal(a, b), Equal(b, c)]),
      consequent = Equal(a, c)))

n = common_vars.n()
m = common_vars.m()
eqDiscrete = enriched.Forall([n, m],
    enriched.Implies(
      predicate = enriched.And([Natural(n), Natural(m)]),
      consequent = enriched.Or([Equal(n,m), Equal(n, m).transpose()])))

eqClaims = [eqIdentitiy, eqSymmetric, eqTransitive, eqDiscrete]

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

successorClaims = [successorExists, successorUnique, successorInjective, successorNotZero]

R = common_vars.R()
allInduction = enriched.Forall([R],
    byInduction(lambda v: enriched.Holds(holding = R, held = v)))

startingFormula = enriched.And([ zeroIsNatural
                               , enriched.And(eqClaims)
                               , enriched.And(successorClaims)
                               , allInduction])


n = common_vars.n()
m = common_vars.m()
t = common_vars.t()
lessVar = common_vars.less()

defLessArrow = enriched.true.forwardIntroduceQuantifier(type = basic.forallType,
        variables = [n, m]).forwardFollow(lambda x:
            x.forwardOnBodyFollow(lambda x:
              x.forwardSingleton(enriched.parType).forwardFollow(lambda x:
                x.forwardAdmit(0, Natural(m)).forwardFollow(lambda x:
                  x.forwardAdmit(0, Natural(n))))))
defLessArrow = defLessArrow.forwardFollow(lambda x:
    x.forwardOnBodyFollow(lambda x:
      x.forwardOnIthFollow(2, lambda one:
        one.forwardAppendDefinition(
          relation = enriched.Holds(holding = lessVar, less = n, more = m),
          definition = enriched.Or([ Successor(n, m)
                                   , enriched.Exists([t],
                                       enriched.And(
                                         [ Successor(n, t)
                                         , enriched.Holds(holding = lessVar,
                                           less = t, more = m)]))])))))

defLessArrow.translate()
defLess = defLessArrow.tgt()

# This is the formula for which extraction engines must give an implementation.
startingFormula = enriched.And([ zeroIsNatural
                               , enriched.And(eqClaims)
                               , enriched.And(successorClaims)
                               , allInduction])

# This library wishes to provide as simple as possible a formula for extraction
# engines to implement and as useful a formula for users to start with.
# Therefore, it defines the following preludeArrow for converting the startingFormula
# into a formula more useful for clients of the library.  Proofs using this library should
# simply append their proofs to this preludeArrow.
preludeArrow = startingFormula.forwardAssociateOut(0, 0).forwardFollow(lambda x:
    x.forwardOnIth(0, defLessArrow))

preludeArrow.translate()

# This is the formula which users of this library should start with.
preludeFormula = preludeArrow.tgt()
