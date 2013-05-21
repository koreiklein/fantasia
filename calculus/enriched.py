# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic, symbol, basicConstructors as constructors
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
    return constructors.ProjectionVariable(self.equivalence, relationSymbol)
  def domain(self):
    return constructors.ProjectionVariable(self.equivalence, domainSymbol)

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
            relation = binding.relation(),
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
      result = constructors.And([ constructors.Holds(self.variables[i], self.domains[i])
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

outputSymbol = symbol.StringSymbol('output')
inputSymbol = symbol.StringSymbol('input')

class Apply:
  # x: a variable on an Apply object
  # f: a variable (the "function") or an Apply object
  # tmp: the temporary variable to use for the output (or None if a new one should be generated)
  def __init__(self, x, f, tmp = None):
    self.x = x
    self.f = f
    if tmp is None:
      self.tmp = common_vars.tmp()
    else:
      self.tmp = tmp

  def __eq__(self, other):
    return (other.__class__ == Apply
        and self.x == other.x and self.f == other.f and self.tmp == other.tmp)

  def __ne__(self, other):
    return not(self == other)

  def __repr__(self, other):
    return "< " + repr(self.x) + " |> " + repr(self.f) + " >"

  def updateVariables(self):
    return Apply(x = self.x.updateVariables(),
        f = self.f.updateVariables(),
        tmp = self.tmp.updateVariables())
  def substituteVariable(self, a, b):
    return Apply(x = self.x.substituteVariable(a, b),
        f = self.f.substituteVariable(a, b),
        tmp = self.tmp.substituteVariable(a, b))
  def freeVariables(self):
    result = Set()
    result.union_with(self.x.freeVariables())
    result.union_with(self.f.freeVariables())
    result.union_with(self.tmp.freeVariables())

# v: either a variable or an Apply object
# return: a function f taking (a function g taking a new "output" variable to a basic object)
#                          to (a larger object that put the output variable in scope and
#                              assumes the appropriate things about it)
def _translate(v):
  if isinstance(v, basic.Variable):
    f = lambda g: g(v)
  else:
    assert(v.__class__ == Apply)
    f = lambda g: _translate(v.x, lambda x: _translate(v.f, lambda f:
      basic.Exists(variables = [v.tmp],
        value = basic.And( basic.Relation(holding = f, held = [x, v.tmp])
                         , g(v.tmp)))))
  return f

class FunctionallyEnrichedHolds(Enriched):
  # enrichedHolding: a variable, or an Apply object
  # enrichedHeld: a list of variables, or Apply objects
  def __init__(self, enrichedHolding, enrichedHeld):
    self.enrichedHolding = enrichedHolding
    self.enrichedHeld = enrichedHeld

  def __eq__(self, other):
    return (other.__class__ == FunctionallyEnrichedHolds
        and self.enrichedHolding == other.enrichedHolding
        and self.enrichedHeld == other.enrichedHeld)
  def __ne__(self, other):
    return not(self == other)

  def __repr__(self, other):
    return (repr(self.enrichedHolding)
        + "(" + ", ".join([repr(v) for v in self.enrichedHeld]) + ")")

  def updateVariables(self):
    return FunctionallyEnrichedHolds(enrichedHolding = self.enrichedHolding.updateVariables(),
        enrichedHeld = [v.updateVariables() for v in self.enrichedHeld])
  def substituteVariable(self, a, b):
    return FunctionallyEnrichedHolds(enrichedHolding = self.enrichedHolding.substituteVariable(a, b),
        enrichedHeld = [v.substituteVariable(a, b) for v in self.enrichedHeld])
  def freeVariables(self):
    result = Set()
    result.union_with(self.enrichedHolding.freeVariables())
    for v in self.enrichedHeld:
      result.union_with(v.freeVariables())
    return self

  def translate(self):
    def _s(vs, f):
      if len(vs) == 0:
        return f([])
      else:
        x = vs[0]
        rest = vs[1:]
        return _translate(x, lambda realX:
            _s(rest, lambda realRest:
              f(_listCons(realX, realRest))))
    return _s(self.enrichedHeld, lambda held:
        _translate(self.enrichedHolding, lambda holding:
          basic.Relation(holding = holding, held = held)))


def _listCons(x, xs):
  result = [x]
  result.extend(xs)
  return result

class Iff(Enriched):
  def __init__(self, left, right):
    self.left = left
    self.right = right
  def translate(self):
    return constructors.Iff(self.left, self.right)
  def updateVariables(self):
    return Iff(left = self.left.updateVariables(),
        right = self.right.updateVariables())
  def substituteVariable(self, a, b):
    return Iff(left = self.left.substituteVariable(a, b),
        right = self.right.substituteVariable(a, b))
  def freeVariables(self):
    return self.left.freeVariables().union(self.right.freeVariables())
