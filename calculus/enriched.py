# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import constructors, basic
from lib.equivalence import relationSymbol, domainSymbol, leftSymbol, rightSymbol
from lib import common_vars

from sets import Set

class VariableBinidng:
  # variable: a basic.Variable
  # equivalence: an Object whose representation is an equivalence in the sense of lib.equivalence
  # uinque: a boolean indicating whether or not this variable is quantified uniquely.
  def __init__(self, variable, equivalence, unique):
    self.variable = variable
    self.equivalence = equivalence
    self.unique = unique

  def relation(self):
    return constructors.Project(value = self.equivalence, symbol = relationSymbol)
  def domain(self):
    return constructors.Project(value = self.equivalence, symbol = domainSymbol)

  def updateVariables(self):
    return VariableBinidng(variable = self.variable.updateVariables(),
        equivalence = self.equivalence.updateVariables(),
        unique = self.unique)

  def substituteVariable(self, a, b):
    return VariableBinidng(variable = self.variable.substituteVariable(a, b),
        equivalence = self.equivalence.substituteVariable(a, b),
        unique = self.unique)

  def freeVariables(self):
    return equivalence.freeVariables().difference(Set([self.variable]))

  def __repr__(self):
    if self.unique:
      c = '!'
    else:
      c = ':'
    return "%s c %s"%(self.variable, self.equivalence)

# For enriched Objects.
class Enriched(basic.Object):
  pass

class Exists(Enriched):
  # bindings: a list of VariableBinidng
  # value: an Object
  def __init__(self, bindings, value):
    self.bindings = bindings
    self.value = value

  # Always returns a "basic" object.
  def translate(self):
    result = self.value.translate()
    for binding in self.bindings:
      claims = []
      claims.append(constructors.Intersect(binding.variable, binding.domain()))
      claims.append(result)
      if binding.unique:
        x = common_vars.x()
        claims.append(constructors.Forall([x],
          constructors.Implies(
            predicate = constructors.And(
              [ constructors.Intersect(x, binding.domain()),
              , result.substituteVariable(binding.variable, x) ]),
            consequent = constructors.Intersect(
              left = constructors.SymbolAnd(
                [ (leftSymbol, x)
                , (rightSymbol, binding.variable) ]),
              right = binding.relation()))))
      result = constructors.And(claims)
    return constructors.Exists([binding.variable for binding in self.bindings],
        result)

  def updateVariables(self):
    return Exists(bindings = [binding.updateVariables() for binding in self.bindings],
        value = self.value.updateVariables())

  def substituteVariable(self, a, b):
    return Exists(bindings = [binding.substituteVariable(a, b) for binding in self.bindings],
        value = self.value.substituteVariable(a, b))

  def freeVariables(self):
    result = self.value.freeVariables()
    for binding in self.bindings:
      result = result.union(binding.freeVariables()).difference(Set([binding.variable]))
    return result

