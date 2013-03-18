# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic, enriched
from lib import common_vars

from sets import Set

class Natural(enriched.Logic):
  # n: a python natural number
  # holds: a boolean indicating whether this formula asserts that n is natural
  #        or that n is not natural.
  def __init__(self, n, holds = True):
    self._n = n
    self._holds = holds
    self.initMarkable([])

  def __repr__(self):
    if self.holds():
      return "%s : N"%(self.n(),)
    else:
      return "%s ~: N"%(self.n(),)

  def n(self):
    return self._n
  def holds(self):
    return self._holds

  def freeVariables(self):
    return Set([self.n()])

  def __eq__(self, other):
    return (self.__class__ == other.__class__
        and self.n() == other.n()
        and self.holds() == other.holds())

  def __ne__(self, other):
    return not (self == other)

  def substituteVar(self, a, b):
    if self.n() == a:
      return IsNatural(b)
    else:
      return self

  def translate(self):
    if self.holds():
      return basic.Holds(natural = self.n().translate())
    else:
      return basic.Holds(notNatural = self.n().translate())

  def transpose(self):
    return Natural(n = self.n(), holds = not self.holds())

class Successor(enriched.Logic):
  def __init__(self, a, b, holds = True):
    self._a = a
    self._b = b
    self._holds = holds
    self.initMarkable([])

  def __repr__(self):
    if self.holds():
      return "%s + 1 == %s"%(self.a(), self.b())
    else:
      return "%s + 1 != %s"%(self.a(), self.b())

  def a(self):
    return self._a
  def b(self):
    return self._b

  def holds(self):
    return self._holds

  def freeVariables(self):
    return Set([self.a(), self.b()])

  def __eq__(self, other):
    return self.__class__ == other.__class__ and (
        self.a() == other.a() and
        self.b() == other.b() and
        self.holds() == other.holds())

  def __ne__(self, other):
    return not (self == other)

  def substituteVar(self, a, b):
    smaller = self.a()
    larger = self.b()
    if smaller == a:
      smaller = b
    if larger == a:
      larger = b
    return Successor(a = smaller, b = larger, holds = self.holds())

  def translate(self):
    if self.holds():
      return basic.Holds(succeeded = self.a().translate(),
          succeeding = self.b().translate())
    else:
      return basic.Holds(notSucceeded = self.a().translate(),
          notSucceeding = self.b().translate())

  def transpose(self):
    return Successor(a = self.a(), b = self.b(), holds = not self.holds())

  def notToTranspose(

zero = enriched.Var('zero')

n = common_vars.n()
m = common_vars.m()
successorExists = enriched.Forall([n],
    enriched.Implies(predicate = Natural(
