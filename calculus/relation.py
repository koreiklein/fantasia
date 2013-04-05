# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol
from calculus import variable
from calculus import limit
from calculus import enriched, basic

class Holds(enriched.Logic):
  # holding: a variable.Variable
  # held: a variable.Variable or a limit.Limit
  def __init__(self, holding, held):
    assert(isinstance(holding, variable.Variable))
    assert(limit.isLimitOrVariable(held))
    self._holding = holding
    self._held = held
    self.initMarkable([]) # TODO: Consider allowing the user to navigate limits.

  def assertEqual(self, other):
    # TODO: Consider using a more detailed assert.
    print self
    print other
    assert(self == other)

  def __eq__(self, other):
    return (self.__class__ == other.__class__ and self.holding() == other.holding() and
        self.held() == other.held())
  def __ne__(self, other):
    return not(self == other)

  def updateVariables(self):
    return Holds(holding = self.holding().updateVariables(),
        held = self.held().updateVariables())

  def holding(self):
    return self._holding
  def held(self):
    return self._held

  def translate(self):
    # basic holds and enriched holds currently share the same implementation.
    return BasicHolds(holding = self.holding(), held = self.held())

  def transposeIsNot(self):
    return True

  def substituteVariable(self, a, b):
    return Holds(holding = self.holding().substituteVariable(a, b),
        held = self.held().substituteVariable(a, b))

  def freeVariables(self):
    return self.holding().freeVariables().union(self.held().freeVariables())

# These are the standard symbols to be used for functions.
inputSymbol = symbol.StringSymbol('input')
outputSymbol = symbol.StringSymbol('output')

# Special "function" holds objects can be constructed with this function.
def FunctionHolds(functionVariable, input, output):
  assert(isLimitOrVariable(input))
  assert(isLimitOrVariable(output))
  return Holds(holding = functionVariable,
      held = limit.newLimit([ (inputSymbol, input)
                            , (outputSymbol, output)]))

class BasicHolds(basic.PrimitiveObject, Holds):
  def assertEqual(self, other):
    # TODO Make a more detailed assert.
    assert(self == other)

  def substituteVariable(self, a, b):
    return BasicHolds(holding = self.holding().substituteVariable(a, b),
        held = self.held().substituteVariable(a, b))

  def updateVariables(self):
    return Holds(holding = self.holding().updateVariables(),
        held = self.held().updateVariables())

