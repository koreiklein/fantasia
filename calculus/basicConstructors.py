# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic
from lib.common_symbols import domainSymbol, relationSymbol, leftSymbol, rightSymbol

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

def Iff(left, right):
  return And([Implies(left, right), Implies(right, left)])

def Exists(variables, value):
  return basic.Always(basic.Exists(variables = variables, value = value))
def Forall(variables, value):
  return basic.Always(basic.Not(basic.Exists(variables = variables, value = basic.Not(value))))

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

def Uniquely(variable, value, domain, x):
  # FIXME
  assert(False)

def Welldefinedly(variable, value, domain, x):
  # FIXME
  assert(False)

