# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic, symbol, basicConstructors as constructors
from lib.common_symbols import relationSymbol, domainSymbol, leftSymbol, rightSymbol
from lib import common_vars

from sets import Set

# Multiple conjunction will be represented (a | (b | (c | 1)))
def multiple_conjunction(conjunction, values):
  result = basic.unit_for_conjunction(conjunction)
  for value in values[::-1]:
    result = conjunction(left = value, right = result)
  return basic.Always(result)

def And(values):
  return multiple_conjunction(basic.And, values)
def Or(values):
  return multiple_conjunction(basic.Or, values)

# There are two reasonable ways to implement this function.
def Implies(predicate, consequent):
  return basic.Always(basic.Not(
    value = basic.And(left = predicate,
                      right = basic.Not(consequent))))
  #return basic.Always(basic.Not(
  #  value = basic.And(left = basic.Not(basic.Not(value = predicate, rendered = True)),
  #                    right = basic.Not(consequent))))

def ExpandIff(left, right):
  return And([Implies(left, right), Implies(right, left)])

def Not(a):
  return basic.Always(basic.Not(value = a, rendered = True))

def unaryHolds(r):
  return lambda x: basic.Always(basic.unaryHolds(r)(x))

def Holds(x, r):
  return basic.Always(basic.Holds(x, r))

def VariableProject(v, s):
  return basic.ProjectionVariable(variable = v, symbol = s)

def VariableProduct(symbol_variable_pairs):
  return basic.ProductVariable(symbol_variable_pairs)

StringVariable = basic.StringVariable

true = basic.Always(basic.true)
false = basic.Always(basic.false)

def EnrichedExists(bindings, value):
  return basic.Always(Exists(bindings = bindings, value = value))

def EnrichedForall(bindings, value):
  return basic.Always(Forall(bindings = bindings, value = value))

def SimpleEnrichedForall(variableEquivalencePairs, value):
  return EnrichedForall(
      bindings = [VariableBinding(variable = v, equivalence = e, unique = False)
                  for (v,e) in variableEquivalencePairs],
      value = value)

def SimpleEnrichedExists(variableEquivalencePairs, value):
  return EnrichedExists(
      bindings = [VariableBinding(variable = v, equivalence = e, unique = False)
                  for (v,e) in variableEquivalencePairs],
      value = value)

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
    return basic.ProjectionVariable(self.equivalence, relationSymbol)
  def domain(self):
    return basic.ProjectionVariable(self.equivalence, domainSymbol)

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
  return basic.Always(Quantifier(bindings = bindings, value = value,
    underlying = BoundedForall))

def Exists(bindings, value):
  return basic.Always(Quantifier(bindings = bindings, value = value,
    underlying = BoundedExists))

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
      return Uniquely
    else:
      assert(self.underlying == BoundedForall)
      return Welldefinedly

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
  return basic.Not(BoundedExists(
    variables = variables,
    domains = domains,
    value = basic.Not(value)))

def BasicForall(variables, value):
  return basic.Not(basic.Exists(variables = variables, value = basic.Not(value)))

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
      result = And([ constructors.Holds(self.variables[i], self.domains[i])
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

#class Apply:
#  # x: a variable on an Apply object
#  # f: a variable (the "function") or an Apply object
#  # tmp: the temporary variable to use for the output (or None if a new one should be generated)
#  def __init__(self, x, f, tmp = None):
#    self.x = x
#    self.f = f
#    if tmp is None:
#      self.tmp = common_vars.tmp()
#    else:
#      self.tmp = tmp
#
#  def __eq__(self, other):
#    return (other.__class__ == Apply
#        and self.x == other.x and self.f == other.f and self.tmp == other.tmp)
#
#  def __ne__(self, other):
#    return not(self == other)
#
#  def __repr__(self, other):
#    return "< " + repr(self.x) + " |> " + repr(self.f) + " >"
#
#  def updateVariables(self):
#    return Apply(x = self.x.updateVariables(),
#        f = self.f.updateVariables(),
#        tmp = self.tmp.updateVariables())
#  def substituteVariable(self, a, b):
#    return Apply(x = self.x.substituteVariable(a, b),
#        f = self.f.substituteVariable(a, b),
#        tmp = self.tmp.substituteVariable(a, b))
#  def freeVariables(self):
#    result = Set()
#    result.union_with(self.x.freeVariables())
#    result.union_with(self.f.freeVariables())
#    result.union_with(self.tmp.freeVariables())
#
## v: either a variable or an Apply object
## return: a function f taking (a function g taking a new "output" variable to a basic object)
##                          to (a larger object that put the output variable in scope and
##                              assumes the appropriate things about it)
#def _translate(v):
#  if isinstance(v, basic.Variable):
#    f = lambda g: g(v)
#  else:
#    assert(v.__class__ == Apply)
#    f = lambda g: _translate(v.x, lambda x: _translate(v.f, lambda f:
#      basic.Exists(variables = [v.tmp],
#        value = basic.And( basic.Relation(holding = f, held = [x, v.tmp])
#                         , g(v.tmp)))))
#  return f
#
#class FunctionallyEnrichedHolds(Enriched):
#  # enrichedHolding: a variable, or an Apply object
#  # enrichedHeld: a list of variables, or Apply objects
#  def __init__(self, enrichedHolding, enrichedHeld):
#    self.enrichedHolding = enrichedHolding
#    self.enrichedHeld = enrichedHeld
#
#  def __eq__(self, other):
#    return (other.__class__ == FunctionallyEnrichedHolds
#        and self.enrichedHolding == other.enrichedHolding
#        and self.enrichedHeld == other.enrichedHeld)
#  def __ne__(self, other):
#    return not(self == other)
#
#  def __repr__(self, other):
#    return (repr(self.enrichedHolding)
#        + "(" + ", ".join([repr(v) for v in self.enrichedHeld]) + ")")
#
#  def updateVariables(self):
#    return FunctionallyEnrichedHolds(enrichedHolding = self.enrichedHolding.updateVariables(),
#        enrichedHeld = [v.updateVariables() for v in self.enrichedHeld])
#  def substituteVariable(self, a, b):
#    return FunctionallyEnrichedHolds(enrichedHolding = self.enrichedHolding.substituteVariable(a, b),
#        enrichedHeld = [v.substituteVariable(a, b) for v in self.enrichedHeld])
#  def freeVariables(self):
#    result = Set()
#    result.union_with(self.enrichedHolding.freeVariables())
#    for v in self.enrichedHeld:
#      result.union_with(v.freeVariables())
#    return self
#
#  def translate(self):
#    def _s(vs, f):
#      if len(vs) == 0:
#        return f([])
#      else:
#        x = vs[0]
#        rest = vs[1:]
#        return _translate(x, lambda realX:
#            _s(rest, lambda realRest:
#              f(_listCons(realX, realRest))))
#    return _s(self.enrichedHeld, lambda held:
#        _translate(self.enrichedHolding, lambda holding:
#          basic.Relation(holding = holding, held = held)))
#
#
#def _listCons(x, xs):
#  result = [x]
#  result.extend(xs)
#  return result

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

class Hidden(Enriched):
  def __init__(self, base, name):
    self.base = base
    self.name = name
  def translate(self):
    return self.base.translate()
  def updateVariables(self):
    return Hidden(base = self.base.updateVariables(), name = self.name)
  def substituteVariable(self, a, b):
    return Hidden(base = self.base.substituteVariable(a, b), name = self.name)
  def freeVariables(self):
    return self.base.freeVariables()

def Uniquely(variable, value, domain, relation, x):
  return And([value, BasicForall([x], Implies(
    predicate = And([Holds(x, domain), value.substituteVariable(variable, x)]),
    consequent = Holds(VariableProduct([(leftSymbol, x), (rightSymbol, variable)]), relation)))])

def Welldefinedly(variable, value, domain, x):
  return And([value, BasicForall([x], Implies(
    predicate = And([ Holds(x, domain)
                    , Holds( VariableProduct([(leftSymbol, x), (rightSymbol, variable)])
                           , relation) ]),
    consequent = value.substituteVariable(variable, x)))])

