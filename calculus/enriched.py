# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic, basicConstructors as constructors
from lib.equivalence import relationSymbol, domainSymbol, leftSymbol, rightSymbol
from lib import common_vars

from sets import Set

class VariableBinding:
  # variable: a basic.Variable
  # equivalence: an Object whose representation is an equivalence in the sense of lib.equivalence
  # uinque: a boolean indicating whether or not this variable is quantified uniquely.
  def __init__(self, variable, equivalence, unique, alternate_variable = None):
    if alternate_variable is None:
      self.alternate_variable = common_vars.x()
    else:
      self.alternate_variable = alternate_variable
    self.variable = variable
    self.equivalence = equivalence
    self.unique = unique

  def __eq__(self, other):
    return (self.__class__ == other.__class__ and self.variable == other.variable
        and self.equivalence == other.equivalence and self.unique == other.unique
        and self.alternate_variable == other.alternate_variable)

  def __ne__(self, other):
    return not(self == other)

  def relation(self):
    return constructors.Project(value = self.equivalence, symbol = relationSymbol)
  def domain(self):
    return constructors.Project(value = self.equivalence, symbol = domainSymbol)

  def updateVariables(self):
    return VariableBinding(variable = self.variable.updateVariables(),
        equivalence = self.equivalence.updateVariables(),
        alternate_variable = self.alternate_variable.updateVariables(),
        unique = self.unique)

  def substituteVariable(self, a, b):
    return VariableBinding(variable = self.variable.substituteVariable(a, b),
        equivalence = self.equivalence.substituteVariable(a, b),
        alternate_variable = self.alternate_variable.substituteVariable(a, b),
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

def Forall(bindings, value):
  return Quantifier(bindings = bindings, value = value, underlying = BoundedForall)

def Exists(bindings, value):
  return Quantifier(bindings = bindings, value = value, underlying = BoundedExists)

class Quantifier(Enriched):
  # bindings: a list of VariableBinding
  # value: an Object
  # underlying: BoundedExists or BoundedForall
  def  __init__(self, bindings, value, underlying):
    self.bindings = bindings
    self.value = value
    self.underlying = underlying

  def __eq__(self, other):
    return (self.__class__ == other.__class__
        and self.bindings == other.bindings
        and self.value == other.value
        and self.underlying == other.underlying)

  def __ne__(self, other):
    return not(self == other)

  def uniquenessCombinator(self):
    if self.underlying == BoundedExists:
      return constructors.Uniquely
    else:
      assert(self.underlying == BoundedForall)
      return constructors.Welldefinedly

  # Always returns a "basic" object.
  def translate(self):
    value = self.value
    for binding in self.bindings:
      if binding.unique:
        value = self.uniquenessCombinator()(
            variable = binding.variable,
            value = value,
            domain = binding.domain(),
            x = binding.alternate_variable)
    return self.underlying(
        variables = [binding.variable for binding in self.bindings],
        domains = [binding.domain() for binding in self.bindings],
        value = value).translate()

  def isForall(self):
    return self.underlying == BoundedForall

  def isExists(self):
    return self.underlying == BoundedExists

  def updateVariables(self):
    return Quantifier(
        bindings = [binding.updateVariables() for binding in self.bindings],
        value = self.value.updateVariables(),
        underlying = self.underlying)

  def substituteVariable(self, a, b):
    return Quantifier(
        bindings = [binding.substituteVariable(a, b) for binding in self.bindings],
        value = self.value.substituteVariable(a, b),
        underlying = self.underlying)

  def freeVariables(self):
    result = self.value.freeVariables()
    for binding in self.bindings:
      result = result.union(binding.domain().freeVariables()).difference(Set([binding.variable]))
    return result

def BoundedForall(variables, domains, value):
  return constructors.Not(BoundedExists(
    variables = variables,
    domains = domains,
    value = constructors.Not(value)))

class BoundedExists(Enriched):
  def __init__(self, variables, domains, value):
    assert(len(variables ) == len(domains))
    self.variables = variables
    self.domains = domains
    self.value = value

  # Always returns a "basic" object.
  def translate(self):
    result = self.value.translate()
    for i in range(len(self.variables)):
      result = constructors.And([ constructors.Intersect(self.variables[i], self.domains[i])
                                , result])
    return constructors.Exists(self.variables, result)

  def updateVariables(self):
    return BoundedExists(
        variables = [variable.updateVariables() for variable in self.variables],
        domains = [domain.updateVariables() for domain in self.domains],
        value = self.value.updateVariables())

  def substituteVariable(self, a, b):
    return BoundedExists(
        variables = [variable.substituteVariable(a, b) for variable in self.variables],
        domains = [domain.substituteVariable(a, b) for domain in self.domains],
        value = self.value.substituteVariable(a, b))

  def freeVariables(self):
    result = self.value.freeVariables()
    for i in range(len(self.variables)):
      result = result.union(self.domains[i].freeVariables()).difference(Set([self.variables[i]]))
    return result

def Function(domain_variable, domain, codomain_variable, codomain, unique, value):
  return Forall(
      bindings = [VariableBinding(variable = domain_variable,
                                  equivalence = domain,
                                  unique = True)],
      value = Exists(
          bindings = [VariableBinding(variable = codomain_variable,
                                      equivalence = codomain,
                                      unique = True)],
          value = value))

outputSymbol = constructors.StringVariable('output')
inputSymbol = constructors.StringVariable('input')

class Call(Enriched):
  def __init__(self, left, right, intermediate_variable = None):
    self.left = left
    self.right = right
    if intermediate_variable is None:
      self.intermediate_variable = common_vars.x()
    else:
      self.intermediate_variable = intermediate_variable

  def translate(self):
    return constructors.Exists([self.intermediate_variable],
        constructors.Project(symbol = outputSymbol,
          value = constructors.Intersect(
            left = constructors.SymbolAnd([ (inputSymbol, self.left)
                                          , (outputSymbol, self.intermediate_variable) ]),
            right = self.right)))

  def updateVariables(self):
    return Call(left = self.left.updateVariables(),
        right = self.right.updateVariables(),
        intermediate_variable = self.intermediate_variable.updateVariables())

  def substituteVariable(self, a, b):
    return Call(left = self.left.substituteVariable(a, b),
        right = self.right.substituteVariable(a, b),
        intermediate_variable = self.intermediate_variable.substituteVariable(a, b))

  def freeVariables(self):
    return Set([self.intermediate_variable]).union(self.left.freeVariables()).union(
        self.right.freeVariables())

  def __eq__(self, other):
    return (self.__class__ == other.__class__
        and self.left == other.left
        and self.right == other.right
        and self.intermediate_variable == other.intermediate_variable)

  def __ne__(self, other):
    return not(self == other)


