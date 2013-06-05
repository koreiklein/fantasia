# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic
from lib import library, common_vars
from lib.common_symbols import leftSymbol, rightSymbol, relationSymbol, domainSymbol

equivalence = basic.StringVariable('equivalence')

def InDomain(x, e):
  return basic.Holds(x, basic.ProjectionVariable(e, domainSymbol))

def EqualUnder(a, b, e):
  return basic.Holds(
      basic.ProductVariable([(leftSymbol, a), (rightSymbol, b)]),
      basic.ProjectionVariable(e, relationSymbol))

x = common_vars.x()
def reflexive(e):
  return basic.MultiForall([x],
      basic.Implies(predicate = InDomain(x, e),
        consequent = EqualUnder(x, x, e)))

x = common_vars.x()
y = common_vars.y()
def symmetric(e):
  return basic.MultiForall([x, y],
      basic.Implies(
        predicate = basic.MultiAnd(
          [ InDomain(x, e)
          , InDomain(y, e)
          , EqualUnder(x, y, e)]),
        consequent = EqualUnder(y, x, e)))

x = common_vars.x()
y = common_vars.y()
z = common_vars.z()
def transitive(e):
  return basic.MultiForall([x, y, z],
      basic.Implies(
        predicate = basic.MultiAnd(
          [ InDomain(x, e)
          , InDomain(y, e)
          , InDomain(z, e)
          , EqualUnder(x, y, e)
          , EqualUnder(y, z, e) ]),
        consequent = EqualUnder(x, z, e)))

def IsEquivalence(e):
  return basic.Holds(e, equivalence)

A = common_vars.A()
claim = basic.MultiForall([A],
    basic.Iff(
      left = basic.MultiAnd(
        [ reflexive(A)
        , symmetric(A)
        , transitive(A)]),
      right = IsEquivalence(A)))

lib = library.Library(claims = [claim], variables = [equivalence])
