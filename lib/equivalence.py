# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import enriched
from lib import library, common_vars
from lib.common_symbols import leftSymbol, rightSymbol, relationSymbol, domainSymbol

equivalence = enriched.StringVariable('equivalence')

def InDomain(x, e):
  return enriched.EnrichedHolds(x, enriched.VariableProject(e, domainSymbol))

def EqualUnder(a, b, e):
  return enriched.EnrichedHolds(
      enriched.VariableProduct([(leftSymbol, a), (rightSymbol, b)]),
      enriched.VariableProject(e, relationSymbol))

x = common_vars.x()
def reflexive(e):
  return enriched.BasicForall([x],
      enriched.Implies(predicate = InDomain(x, e),
        consequent = EqualUnder(x, x, e)))

x = common_vars.x()
y = common_vars.y()
def symmetric(e):
  return enriched.BasicForall([x, y],
      enriched.Implies(
        predicate = enriched.And(
          [ InDomain(x, e)
          , InDomain(y, e)
          , EqualUnder(x, y, e)]),
        consequent = EqualUnder(y, x, e)))

x = common_vars.x()
y = common_vars.y()
z = common_vars.z()
def transitive(e):
  return enriched.BasicForall([x, y, z],
      enriched.Implies(
        predicate = enriched.And(
          [ InDomain(x, e)
          , InDomain(y, e)
          , InDomain(z, e)
          , EqualUnder(x, y, e)
          , EqualUnder(y, z, e) ]),
        consequent = EqualUnder(x, z, e)))

def IsEquivalence(e):
  return enriched.EnrichedHolds(e, equivalence)

A = common_vars.A()
claim = enriched.BasicForall([A],
    enriched.Iff(
      left = enriched.And(
        [ reflexive(A)
        , symmetric(A)
        , transitive(A)]),
      right = IsEquivalence(A)))

lib = library.Library(claims = [claim], variables = [equivalence])
