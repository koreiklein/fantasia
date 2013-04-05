# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic, enriched, variable, symbol, relation, limit
from lib import common_vars

five = variable.StringVariable('5')
from sets import Set

natural = variable.StringVariable('N')

natural_less = variable.StringVariable('<')
natural_less_or_equal = variable.StringVariable('<')
smallerSymbol = variable.StringVariable('smaller')
greaterSymbol = variable.StringVariable('greater')

natural_successor = variable.StringVariable('S')
before = variable.StringVariable('before')
after = variable.StringVariable('after')

# Stating that a variable is a natural number.
def IsNatural(n):
  return relation.Holds(natural, n)

def Compare(lesser, greater, strict):
  if strict:
    return relation.Holds(natural_less,
        limit.newLimit([(smallerSymbol, lesser), (greaterSymbol, greater)]))
  else:
    return relation.Holds(natural_less_or_equal,
        limit.newLimit([(smallerSymbol, lesser), (greaterSymbol, greater)]))

def Successor(a, b):
  return relation.Holds(natural_successor, limit.newLimit([(before, a), (after, b)]))

zero = variable.StringVariable('zero')

five = variable.StringVariable('5')

zero_natural = IsNatural(zero)

exists_five = enriched.Exists([five], IsNatural(five))

t = common_vars.t()
r = common_vars.r()
increasing = enriched.Forall([t, r],
    enriched.Implies(predicate = Successor(t, r),
      consequent = Compare(lesser = t, greater = r, strict = True)))

n = common_vars.n()
reflexivity = enriched.Forall([n],
    enriched.Implies(predicate = IsNatural(n),
      consequent = Compare(lesser = n, greater = n, strict = False)))

s = common_vars.s()
l = common_vars.l()
weakening = enriched.Forall([s, l],
    enriched.Implies(predicate = Compare(s, l, strict = True),
      consequent = Compare(s, l, strict = False)))

n = common_vars.n()
m = common_vars.m()
successorExists = enriched.Forall([n],
    enriched.Implies(predicate = IsNatural(n),
      consequent = enriched.Exists([m],
        enriched.And([IsNatural(m), Successor(n, m), Successor(n, m)]))))

a = common_vars.a()
b = common_vars.b()
c = common_vars.c()
transitivity = enriched.Forall([a, b, c],
    enriched.Implies(predicate = enriched.And([ Compare(a, b, False)
                                              , Compare(b, c, True)]),
                     consequent = Compare(a, c, True)))


# This definition of induction should by no means be considered final.
# As the combinators in calculus.enriched become more sophisticated, we may
# wish to give more elaborate definitions of induction.
# For example, all claims about numbers being natural might be hidden.
# For another example, we may use m = n + 1 instead of natural.Successor(n, m).

n = common_vars.n()
m = common_vars.m()
k = common_vars.k()
# claim: a function from a variable to a formula saying the claim holds of
# that variable.
def byInduction(claim):
  return enriched.Implies(
      predicate = enriched.And([ claim(zero)
                               , enriched.Forall([n]
                               , enriched.Implies(
                                  predicate = enriched.And([ IsNatural(n)
                                                           , claim(n)]),
                                  consequent =
                                    enriched.Exists([m],
                                      enriched.And([ IsNatural(m)
                                                   , Successor(n, m)
                                                   , claim(m)]))))]),
      consequent = enriched.Forall([k],
        enriched.Implies(
          predicate = IsNatural(k),
          consequent = claim(k))))

