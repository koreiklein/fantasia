# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol, constructors, enriched
from lib import equivalence, library, common_vars, function

natural = constructors.StringVariable('N')

natural_less = constructors.StringVariable('<')
smaller = symbol.StringSymbol('smaller')
greater = symbol.StringSymbol('greater')

natural_successor = constructors.StringVariable('S')
before = symbol.StringSymbol('before')
after = symbol.StringSymbol('after')

def Natural(n):
  return equivalence.InDomain(n, natural)

def Successor(a, b):
  return constructors.Holds(constructors.ProductVariable([(before, a), (after, b)]), natural_successor)

def Equal(a, b):
  return equivalence.EqualUnder(a, b, natural)

def Less(a, b):
  return constructors.Holds(constructors.ProductVariable([(smaller, a), (greater, b)]), natural_less)

successorIsFunction = function.IsFunction(natural_successor)

#a = common_vars.a()
#successorIsGreater = constructors.EnrichedForall(
#    [constructors.VariableBinding(variable = a, equivalence = natural, unique = True)],
#    Less(a, constructors.Call(a, natural_successor)))
#
#zero = constructors.StringVariable('zero')
#zeroNatural = constructors.Intersect(zero, constructors.Project(natural, equivalence.domainSymbol))
#
#n = common_vars.n()
#m = common_vars.m()
#zeroFirst = constructors.Forall([n, m],
#    constructors.Implies(
#      predicate = constructors.And(
#        [ constructors.Intersect(n, constructors.Project(natural, equivalence.domainSymbol))
#        , constructors.Intersect(m, constructors.Project(natural, equivalence.domainSymbol))
#        , Successor(n, m) ]),
#      consequent = constructors.Not(Equal(n, zero))))
#lib = library.Library(claims = [isEquivalence, zeroNatural, zeroFirst, existsUniqueSuccessor, successorIsGreater],
    #variables = [natural, zero, natural_less, natural_successor])

lib = library.Library(claims = [], variables = [])
