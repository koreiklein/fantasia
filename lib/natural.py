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

class Equal:
  def __init__(self, a, b):
    self._a = a
    self._b = b

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

zero = enriched.Var('zero')

n = common_vars.n()
m = common_vars.m()
successorExists = enriched.Forall([n],
    enriched.Implies(
      predicate = Natural(n),
      consequent = enriched.Exists([m],
        enriched.And([Natural(m), Successor(n, m)]))))

