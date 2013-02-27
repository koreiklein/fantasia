# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from logic import linearui, linear
from logic.lib import common_vars


# Stating that a variable is a natural number.
class IsNatural(linearui.Logic):
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
    return linear.Holds(natural = self.n().translate())

  def transpose(self):
    return linearui.Not(self)

# Stating some inequality (=, >=, <=) between two variables.
class Compare(linearui.Logic):
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
    return linear.Holds(lesser = self.lesser().translate(), greater = self.greater().translate(),
        strict = self.strict())

  def transpose(self):
    return linearui.Not(self)

# Stating that the successor of the natural number a is b.
class Successor(linearui.Logic):
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
    return linear.Holds(succeeded = self.a().translate(),
        succeeding = self.b().translate())

  def transpose(self):
    return linearui.Not(self)

zero = linearui.Var('zero')

zero_natural = IsNatural(zero)

t = common_vars.t()
r = common_vars.r()
increasing = linearui.Forall([t, r],
    linearui.Implies(predicate = Successor(t, r),
      consequent = Compare(lesser = t, greater = r, strict = True)))

n = common_vars.n()
reflexivity = linearui.Forall([n],
    linearui.Implies(predicate = IsNatural(n),
      consequent = Compare(lesser = n, greater = n, strict = False)))

s = common_vars.s()
l = common_vars.l()
weakening = linearui.Forall([s, l],
    linearui.Implies(predicate = Compare(s, l, strict = True),
      consequent = Compare(s, l, strict = False)))

n = common_vars.n()
m = common_vars.m()
successorExists = linearui.Forall([n],
    linearui.Implies(predicate = IsNatural(n),
      consequent = linearui.Exists([m],
        linearui.And([IsNatural(m), Successor(n, m), Successor(n, m)]))))

a = common_vars.a()
b = common_vars.b()
c = common_vars.c()
transitivity = linearui.Forall([a, b, c],
    linearui.Implies(predicate = linearui.And([ Compare(a, b, False)
                                              , Compare(b, c, True)]),
                     consequent = Compare(a, c, True)))

