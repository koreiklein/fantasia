# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol, esmerelda
from lib import common_vars

natural = esmerelda.StringVariable('N')

natural_less = esmerelda.StringVariable('<')
smaller = esmerelda.StringVariable('smaller')
greater = esmerelda.StringVariable('greater')

natural_successor = esmerelda.StringVariable('S')
before = esmerelda.StringVariable('before')
after = esmerelda.StringVariable('after')

natural_equal = esmerelda.StringVariable('=')
leftSymbol = symbol.StringSymbol('left')
rightSymbol = symbol.StringSymbol('right')

def Natural(n):
  return esmerelda.Intersect(left = n, right = natural)

def Equal(a, b):
  return esmerelda.Intersect(
      left = esmerelda.MultiAnd([(leftSymbol, a), (rightSymbol, b)]),
      right = natural_equal)

def Successor(a, b):
  return esmerelda.Intersect(
      left = esmerelda.MultiAnd([(before, a), (after, b)]),
      right = natural_successor)

def Less(a, b):
  return esmerelda.Intersect(
      left = esmerelda.MultiAnd([(smaller, a), (greater, b)]),
      right = natural_less)

n = common_vars.n()
eqIdentity = esmerelda.Forall([n],
    esmerelda.Implies(
      predicate = Natural(n),
      consequent = Equal(n, n)))

