# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic, symbol
from lib.common_symbols import relationSymbol, domainSymbol, leftSymbol, rightSymbol, inputSymbol, outputSymbol, functionPairsSymbol, tgtSymbol
from lib import common_vars

from sets import Set

class SimpleEnrichedArrow(basic.Arrow):
  def __init__(self, src, tgt, basicArrow):
    self.src = src
    self.tgt = tgt
    self.basicArrow = basicArrow

  def translate(self):
    return self.basicArrow

def Always(value):
  return basic.Always(value)

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

def Holds(x, r):
  return basic.Always(basic.Holds(x, r))

def ProjectionVariable(v, s):
  return basic.ProjectionVariable(variable = v, symbol = s)

def ProductVariable(symbol_variable_pairs):
  return basic.ProductVariable(symbol_variable_pairs)

StringVariable = basic.StringVariable

true = basic.Always(basic.true)
false = basic.Always(basic.false)

# For enriched Objects.
class Enriched(basic.Object):
  pass

def Forall(variableEquivalencePairs, value):
  return basic.Always(BoundedForall(variables = [v for (v,e) in variableEquivalencePairs],
      domains = [basic.ProjectionVariable(e, domainSymbol) for (v,e) in variableEquivalencePairs],
      value = value))

def Exists(variableEquivalencePairs, value):
  return basic.Always(BoundedExists(variables = [v for (v,e) in variableEquivalencePairs],
      domains = [basic.ProjectionVariable(e, domainSymbol) for (v,e) in variableEquivalencePairs],
      value = value))

def BasicForall(variables, value):
  return basic.Not(basic.Exists(variables = variables, value = basic.Not(value)))

def BasicExists(variables, value):
  return basic.Exists(variables = variables, value = value)

def BoundedForall(variables, domains, value):
  return basic.Not(BoundedExists(
    variables = variables,
    domains = domains,
    value = basic.Not(value)))

class BoundedExists(Enriched):
  def __init__(self, variables, domains, value):
    assert(len(variables ) == len(domains))
    self.variables = variables
    self.domains = domains
    self.value = value
    self.pairs = [(self.variables[i], self.domains[i]) for i in range(len(self.variables))]

  def __repr__(self):
    s = []
    for (v,d) in self.pairs:
      s.append("%s : %s"%(v,d))
    return "( BoundedExists " + ",".join(s) + " . %s )"%(self.value)

  def produceFiltered(self, f):
    return [SimpleEnrichedArrow(src = self, tgt = basic.And(a.tgt.left, self),
      basicArrow = a) for a in self._translate(self.value).produceFiltered(f)]

  # Always returns a "basic" object.
  def translate(self):
    return self._translate(self.value.translate())

  def _translate(self, value):
    for i in range(len(self.variables)):
      value = basic.And( basic.Holds(self.variables[i], self.domains[i])
                       , value)
    return basic.Exists(self.variables, value)

  def updateVariables(self):
    return BoundedExists(
        variables = [variable.updateVariables() for variable in self.variables],
        domains = self.domains,
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

# Instances of this class may only be used within an EnrichedHolds.
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

  def __repr__(self):
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
def _translate(v, g):
  if isinstance(v, basic.Variable):
    return g(v)
  elif v.__class__  == basic.ProductVariable:
    def _s(pairs, f):
      if len(pairs) == 0:
        return f([])
      else:
        (firstS, firstV) = pairs[0]
        rest = pairs[1:]
        return _translate(firstV, lambda basicFirstV:
            _s(rest, lambda basicRest:
              f(_listCons((firstS, basicFirstV), basicRest))))
    return _s(v.symbol_variable_pairs, lambda basic_symbol_variable_pairs:
        g(basic.ProductVariable(basic_symbol_variable_pairs)))
  elif v.__class__ == basic.ProjectionVariable:
    return _translate(v.variable, lambda variable:
        g(basic.ProjectionVariable(variable = variable, symbol = v.symbol)))
  elif v.__class__ == basic.InjectionVariable:
    return _translate(v.variable, lambda variable:
        g(basic.InjectionVariable(variable = variable, symbol = v.symbol)))
  else:
    assert(v.__class__ == Apply)
    return _translate(v.x, lambda x: _translate(v.f, lambda f:
      basic.Exists(variables = [v.tmp],
        value = basic.And(basic.And(basic.Holds( v.tmp,
            basic.ProjectionVariable(basic.ProjectionVariable(f, tgtSymbol), domainSymbol).simplify()),
          basic.Holds(
            held = basic.ProductVariable([ (inputSymbol, x)
                                         , (outputSymbol, v.tmp)]),
            holding = basic.ProjectionVariable(f, functionPairsSymbol).simplify())),
          g(v.tmp)))))

def _listCons(x, xs):
  result = [x]
  result.extend(xs)
  return result

# This class differs from Holds in that you may use Apply objects for the contained variables.
class EnrichedHolds(Enriched):
  def __init__(self, held, holding):
    self.held = held
    self.holding = holding

  def __eq__(self, other):
    return (other.__class__ == EnrichedHolds
        and self.held == other.held
        and self.holding == other.holding)
  def __ne__(self, other):
    return not(self == other)

  def __repr__(self):
    return repr(self.held) + " : " + repr(self.holding)

  def updateVariables(self):
    return EnrichedHolds(held = self.held.updateVariables(),
        holding = self.holding.updateVariables())
  def substituteVariable(self, a, b):
    return EnrichedHolds(held = self.held.substituteVariable(a, b),
        holding = self.holding.substituteVariable(a, b))
  def freeVariables(self):
    return self.held.freeVariables().union(self.holding.freeVariables())

  def translate(self):
    return _translate(self.held, lambda held:
        _translate(self.holding, lambda holding:
          basic.Holds(held = held, holding = holding)))

class Iff(Enriched):
  def __init__(self, left, right):
    self.left = left
    self.right = right
  def translate(self):
    return ExpandIff(self.left, self.right)
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
  def produceFiltered(self, f):
    return self.base.produceFiltered(f)
  def translate(self):
    return self.base.translate()
  def updateVariables(self):
    return Hidden(base = self.base.updateVariables(), name = self.name)
  def substituteVariable(self, a, b):
    return Hidden(base = self.base.substituteVariable(a, b), name = self.name)
  def freeVariables(self):
    return self.base.freeVariables()

