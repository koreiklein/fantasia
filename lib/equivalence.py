# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import variable
from calculus.basic import formula
from lib import library, common_vars
from lib.common_symbols import leftSymbol, rightSymbol, relationSymbol, domainSymbol

equivalence = variable.StringVariable('equivalence')

def InDomain(x, e):
  return formula.Holds(x, variable.ProjectionVariable(e, domainSymbol))

def EqualUnder(a, b, e):
  return formula.Holds(
      variable.ProductVariable([(leftSymbol, a), (rightSymbol, b)]),
      variable.ProjectionVariable(e, relationSymbol))

x = common_vars.x()
def reflexive(e):
  return formula.MultiForall([x],
      formula.Implies(predicate = InDomain(x, e),
        consequent = EqualUnder(x, x, e)))

x = common_vars.x()
y = common_vars.y()
def symmetric(e):
  return formula.MultiForall([x, y],
      formula.Implies(
        predicate = formula.MultiAnd(
          [ InDomain(x, e)
          , InDomain(y, e)
          , EqualUnder(x, y, e)]),
        consequent = EqualUnder(y, x, e)))

x = common_vars.x()
y = common_vars.y()
z = common_vars.z()
def transitive(e):
  return formula.MultiForall([x, y, z],
      formula.Implies(
        predicate = formula.MultiAnd(
          [ InDomain(x, e)
          , InDomain(y, e)
          , InDomain(z, e)
          , EqualUnder(x, y, e)
          , EqualUnder(y, z, e) ]),
        consequent = EqualUnder(x, z, e)))

def IsEquivalence(e):
  return formula.Holds(e, equivalence)

A = common_vars.A()
claim = formula.MultiForall([A],
    formula.ExpandIff(
      left = formula.MultiAnd(
        [ reflexive(A)
        , symmetric(A)
        , transitive(A)]),
      right = IsEquivalence(A)))

lib = library.Library(claims = [claim], variables = [equivalence])
