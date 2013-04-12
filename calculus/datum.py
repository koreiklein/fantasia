# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol, variable

class Datum:
  def project(self, symbol):
    return Projection(value = self, symbol = symbol)
  def coinject(self, symbol):
    return Coinjection(value = self, symbol = symbol)

  def inject(self, symbol):
    return Case(value = self, symbol = symbol)

  def canSimplify(self):
    raise Exception("Abstract Superclass")

class Variable(Datum):
  # v: a variable.Variable
  def __init__(self, v):
    self._variable = v

  def variable(self):
    return self._variable

  def canSimplify(self):
    return False

class ConstructiveDatum(Datum):
  pass

class Record(ConstructiveDatum):
  # pairs: a list of (symbol, datum) pairs.
  def __init__(self, pairs):
    self._pairs = pairs

  def pairs(self):
    return self._pairs

  def canSimplify(self):
    return False

class Case(ConstructiveDatum):
  # value: a datum
  # symbol: a symbol
  def __init__(self, value, symbol):
    self._value = value
    self._symbol = symbol

  def value(self):
    return self._value
  def symbol(self):
    return self._symbol

  def canSimplify(self):
    return False

class DestructiveDatum(Datum):
  def value(self):
    raise Exception("Abstract Superclass")
  def symbol(self):
    raise Exception("Abstract Superclass")

class Projection(DestructiveDatum):
  def __init__(self, value, symbol):
    if value.__class__ == Record:
      assert(symbol in [s for (s, v) in value.pairs()])
    assert(value.__class__ != Case)
    self._value = value
    self._symbol = symbol

  def value(self):
    return self._value
  def symbol(self):
    return self._symbol

  def canSimplify(self):
    return self.value().__class__ == Record

  def simplify(self):
    assert(self.canSimplify())
    for (symbol, value) in self.value().pairs():
      if symbol == self.symbol():
        return value
    raise Exception("Impossible: a simplifyable Projection's value must be defined on its symbol.")

class Coinjection(DestructiveDatum):
  def __init__(self, value, symbol):
    if value.__class__ == Case:
      assert(symbol == value.symbol())
    assert(value.__class__ != Record)
    self._value = value
    self._symbol = symbol

  def value(self):
    return self._value
  def symbol(self):
    return self._symbol

  def canSimplify(self):
    return self.value().__class__ == Case

  def simplify(self):
    assert(self.canSimplify())
    assert(symbol == value.symbol())
    return self.value().value()

