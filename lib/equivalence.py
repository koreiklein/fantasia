# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol, basicConstructors as constructors
from lib import library, common_vars
from lib.common_symbols import leftSymbol, rightSymbol, relationSymbol, domainSymbol

equivalence = constructors.StringVariable('equivalence')

def InDomain(x, e):
  return constructors.Holds(x, constructors.VariableProject(e, domainSymbol))

def EqualUnder(a, b, e):
  return constructors.Holds(
      constructors.VariableProduct([(leftSymbol, a), (rightSymbol, b)]),
      constructors.VariableProject(e, relationSymbol))

x = common_vars.x()
def reflexive(e):
  return constructors.Forall([x],
      constructors.Implies(predicate = InDomain(x, e),
        consequent = EqualUnder(x, x, e)))

x = common_vars.x()
y = common_vars.y()
def symmetric(e):
  return constructors.Forall([x, y],
      constructors.Implies(
        predicate = constructors.And(
          [ InDomain(x, e)
          , InDomain(y, e)
          , EqualUnder(x, y, e)]),
        consequent = EqualUnder(y, x, e)))

x = common_vars.x()
y = common_vars.y()
z = common_vars.z()
def transitive(e):
  return constructors.Forall([x, y, z],
      constructors.Implies(
        predicate = constructors.And(
          [ InDomain(x, e)
          , InDomain(y, e)
          , InDomain(z, e)
          , EqualUnder(x, y, e)
          , EqualUnder(y, z, e) ]),
        consequent = EqualUnder(x, z, e)))

A = common_vars.A()
claim = constructors.Forall([A],
    constructors.Iff(
      left = constructors.And(
        [ reflexive(A)
        , symmetric(A)
        , transitive(A)]),
      right = constructors.Holds(A, equivalence)))

lib = library.Library(claims = [claim], variables = [equivalence])
