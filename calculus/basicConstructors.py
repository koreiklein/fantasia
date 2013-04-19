# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic
from lib.common_symbols import domainSymbol, relationSymbol, leftSymbol, rightSymbol

# Multiple conjunction will be represented (a | (b | (c | 1)))
def multiple_conjunction(conjunction, symbol_value_pairs):
  result = basic.unit_for_conjunction(conjunction)
  for (symbol, value) in symbol_value_pairs[::-1]:
    result = conjunction(left_symbol = symbol, left = value, right = result)
  return basic.Always(result)

def SymbolAnd(symbol_value_pairs):
  return multiple_conjunction(basic.And, symbol_value_pairs)
def SymbolOr(symbol_value_pairs):
  return multiple_conjunction(basic.Or, symbol_value_pairs)

def And(values):
  if len(values) == 1:
    return values[0]
  else:
    return SymbolAnd([(basic.empty_symbol, value) for value in values])
def Or(values):
  if len(values) == 1:
    return values[0]
  else:
    return SymbolOr([(basic.empty_symbol, value) for value in values])

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

def Intersect(left, right):
  return basic.Always(basic.Intersect(left = left, right = right))

def Not(a):
  return basic.Always(basic.Not(value = a, rendered = True))

def Project(value, symbol):
  return basic.Always(basic.Project(value = value, symbol = symbol))

def Inject(value, symbol):
  return basic.Always(basic.Inject(value = value, symbol = symbol))

def Coinject(value, symbol):
  return basic.Always(basic.Coinject(value = value, symbol = symbol))

StringVariable = basic.StringVariable

true = basic.Always(basic.true)
false = basic.Always(basic.false)

def Uniquely(variable, value, domain, x):
  return And(
      [ value
      , Forall([x],
        Implies(
          predicate = And([ Intersect(x, Project(domain, domainSymbol))
                          , value.substituteVariable(variable, x) ]),
          consequent = Intersect(SymbolAnd([ (leftSymbol, x)
                                           , (rightSymbol, variable) ]),
                                 Project(domain, relationSymbol))))])

def Welldefinedly(variable, value, domain, x):
  return And(
      [ value
      , Forall([x],
        Implies(
          predicate = And([ Intersect(x, Project(domain, domainSymbol))
                          , Intersect(SymbolAnd([ (leftSymbol, x)
                                                , (rightSymbol, variable) ]),
                                      Project(domain, relationSymbol))]),
          consequent = value.substituteVariable(variable, x)))])

