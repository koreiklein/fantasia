# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol, basic
from lib import library, common_vars

natural = basic.StringVariable('N')

natural_less = basic.StringVariable('<')
smaller = basic.StringVariable('smaller')
greater = basic.StringVariable('greater')

natural_successor = basic.StringVariable('S')
before = basic.StringVariable('before')
after = basic.StringVariable('after')

natural_equal = basic.StringVariable('=')
leftSymbol = symbol.StringSymbol('left')
rightSymbol = symbol.StringSymbol('right')

def Natural(n):
  return basic.Intersect(left = n, right = natural)

def Equal(a, b):
  return basic.Intersect(
      left = basic.MultiAnd([(leftSymbol, a), (rightSymbol, b)]),
      right = natural_equal)

def Successor(a, b):
  return basic.Intersect(
      left = basic.MultiAnd([(before, a), (after, b)]),
      right = natural_successor)

def Less(a, b):
  return basic.Intersect(
      left = basic.MultiAnd([(smaller, a), (greater, b)]),
      right = natural_less)

n = common_vars.n()
eqIdentity = basic.Forall([n],
    basic.Implies(
      predicate = Natural(n),
      consequent = Equal(n, n)))

lib = library.Library([eqIdentity])
