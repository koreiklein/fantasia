# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol, constructors, enriched
from lib import equivalence, library, common_vars

natural = constructors.StringVariable('N')

natural_less = constructors.StringVariable('<')
smaller = symbol.StringSymbol('smaller')
greater = symbol.StringSymbol('greater')

natural_successor = constructors.StringVariable('S')
before = symbol.StringSymbol('before')
after = symbol.StringSymbol('after')

leftSymbol = symbol.StringSymbol('left')
rightSymbol = symbol.StringSymbol('right')

def Natural(n):
  return constructors.Intersect(left = n,
      right = constructors.Project(natural, equivalence.domainSymbol))

def Successor(a, b):
  return constructors.Intersect(
      left = constructors.SymbolAnd([(before, a), (after, b)]),
      right = natural_successor)

def Less(a, b):
  return constructors.Intersect(
      left = constructors.SymbolAnd([(smaller, a), (greater, b)]),
      right = natural_less)

isEquivalence = constructors.Intersect(
    left = natural,
    right = equivalence.equivalence)

a = common_vars.a()
b = common_vars.b()
existsUniqueSuccessor = enriched.Function(
    domain_variable = a, domain = natural,
    codomain_variable = b, codomain = natural, unique = True,
    value = Successor(a, b))

lib = library.Library(claims = [isEquivalence, existsUniqueSuccessor],
    variables = [natural, natural_less, natural_successor])
