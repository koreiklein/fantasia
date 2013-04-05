# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol
from calculus import variable

from sets import Set

limitType = 'limitType'
colimitType = 'colimitType'

types = [limitType, colimitType]

def newLimit(pairs):
  return Limit(type = limitType, pairs = pairs)

def newColimit(pairs):
  return Limit(type = colimitType, pairs = pairs)

def isLimitOrVariable(x):
  return isinstance(x, variable.Variable) or isinstance(x, Limit)

class Limit:
  # type in types
  # pairs: a list of pairs (symbol, value) where symbol is a symbol.Symbol and isLimitOrVariable(value)
  def __init__(self, type, pairs, asAType = False):
    assert(type in types)
    self._type = type
    self._pairs = pairs
    self._asAType = asAType

  def type(self):
    return self._type
  def pairs(self):
    return self._pairs
  def usedAsAType(self):
    return self._asAType

  def updateVars(self):
    return Limit(type = self.type(), asAType = self.usedAsAType(),
        pairs = [(symbol, value.updateVars()) for (symbol, value) in self.pairs()])

  def __eq__(self, other):
    if self.__class__ != other.__class__:
      return False
    elif self.type() != other.type():
      return False
    elif len(self.pairs()) != len(other.pairs()):
      return False
    else:
      for i in range(len(self.pairs())):
        if self.pairs()[i] != other.pairs()[i]:
          return False
      return True

  def __ne__(self, other):
    return not(self == other)

  def freeVariables(self):
    result = Set()
    for (symbol, value) in self.pairs():
      result.union_update(value.freeVariables())
    return result

  def substituteVariable(self, a, b):
    return Limit(type = self.type(), asAType = self.usedAsAType(),
        pairs = [ (symbol, value.substituteVariable(a, b)) for (symbol, value) in self.pairs()])

