# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol, constructors
from lib import library, common_vars

natural = constructors.StringVariable('N')

natural_less = constructors.StringVariable('<')
smaller = constructors.StringVariable('smaller')
greater = constructors.StringVariable('greater')

natural_successor = constructors.StringVariable('S')
before = constructors.StringVariable('before')
after = constructors.StringVariable('after')

natural_equal = constructors.StringVariable('=')
leftSymbol = symbol.StringSymbol('left')
rightSymbol = symbol.StringSymbol('right')

def Natural(n):
  return constructors.Intersect(left = n, right = natural)

def Equal(a, b):
  return constructors.Intersect(
      left = constructors.SymbolAnd([(leftSymbol, a), (rightSymbol, b)]),
      right = natural_equal)

def Successor(a, b):
  return constructors.Intersect(
      left = constructors.SymbolAnd([(before, a), (after, b)]),
      right = natural_successor)

def Less(a, b):
  return constructors.Intersect(
      left = constructors.SymbolAnd([(smaller, a), (greater, b)]),
      right = natural_less)

n = common_vars.n()
eqIdentity = constructors.Forall([n],
    constructors.Implies(
      predicate = Natural(n),
      consequent = Equal(n, n)))

lib = library.Library([eqIdentity])
