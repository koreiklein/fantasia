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

def Natural(n):
  return constructors.Intersect(left = n,
      right = constructors.Project(natural, equivalence.domainSymbol))

def Successor(a, b):
  return constructors.Intersect(
      left = constructors.SymbolAnd([(before, a), (after, b)]),
      right = natural_successor)

def Equal(a, b):
  return constructors.Intersect(
      left = constructors.SymbolAnd([ (equivalence.leftSymbol, a)
                                    , (equivalence.rightSymbol, b)]),
      right = constructors.Project(natural, equivalence.relationSymbol))

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
    value = Equal(enriched.Call(a, natural_successor), b))
    #value = Successor(a, b))

zero = constructors.StringVariable('zero')
zeroNatural = constructors.Intersect(zero, constructors.Project(natural, equivalence.domainSymbol))

n = common_vars.n()
m = common_vars.m()
zeroFirst = constructors.Forall([n, m],
    constructors.Implies(
      predicate = constructors.And(
        [ constructors.Intersect(n, constructors.Project(natural, equivalence.domainSymbol))
        , constructors.Intersect(m, constructors.Project(natural, equivalence.domainSymbol))
        , Successor(n, m) ]),
      consequent = constructors.Not(Equal(n, zero))))

lib = library.Library(claims = [isEquivalence, zeroNatural, zeroFirst, existsUniqueSuccessor],
    variables = [natural, zero, natural_less, natural_successor])
