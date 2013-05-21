# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol, enriched
from lib import equivalence, library, common_vars, function

natural = enriched.StringVariable('N')

natural_less = enriched.StringVariable('<')
smaller = symbol.StringSymbol('smaller')
greater = symbol.StringSymbol('greater')

natural_successor = enriched.StringVariable('S')
before = symbol.StringSymbol('before')
after = symbol.StringSymbol('after')

def Natural(n):
  return equivalence.InDomain(n, natural)

def Successor(a, b):
  return enriched.Holds(enriched.ProductVariable([(before, a), (after, b)]), natural_successor)

def Equal(a, b):
  return equivalence.EqualUnder(a, b, natural)

def Less(a, b):
  return enriched.Holds(enriched.ProductVariable([(smaller, a), (greater, b)]), natural_less)

successorIsFunction = function.IsFunction(natural_successor)

#a = common_vars.a()
#successorIsGreater = enriched.EnrichedForall(
#    [enriched.VariableBinding(variable = a, equivalence = natural, unique = True)],
#    Less(a, enriched.Call(a, natural_successor)))
#
#zero = enriched.StringVariable('zero')
#zeroNatural = enriched.Intersect(zero, enriched.Project(natural, equivalence.domainSymbol))
#
#n = common_vars.n()
#m = common_vars.m()
#zeroFirst = enriched.Forall([n, m],
#    enriched.Implies(
#      predicate = enriched.And(
#        [ enriched.Intersect(n, enriched.Project(natural, equivalence.domainSymbol))
#        , enriched.Intersect(m, enriched.Project(natural, equivalence.domainSymbol))
#        , Successor(n, m) ]),
#      consequent = enriched.Not(Equal(n, zero))))
#lib = library.Library(claims = [isEquivalence, zeroNatural, zeroFirst, existsUniqueSuccessor, successorIsGreater],
    #variables = [natural, zero, natural_less, natural_successor])

lib = library.Library(claims = [], variables = [])
