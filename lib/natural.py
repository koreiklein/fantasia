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

