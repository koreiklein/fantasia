# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol, basicConstructors as constructors
from lib import library, common_vars

equivalence = constructors.StringVariable('equivalence')
leftSymbol = symbol.StringSymbol('left')
rightSymbol = symbol.StringSymbol('right')

relationSymbol = symbol.StringSymbol('=')
domainSymbol = symbol.StringSymbol('\'')

reflexiveSymbol = symbol.StringSymbol('reflexive')
symmetricSymbol = symbol.StringSymbol('symmetric')
transitiveSymbol = symbol.StringSymbol('transitive')

def AreEquivalence(r, d):
  return constructors.Intersect(
      left = constructors.SymbolAnd([(relationSymbol, r), (domainSymbol, d)]),
      right = equivalence)

def EquivalentUnder(a, b, r):
  return constructors.Intersect(
      left = constructors.SymbolAnd([(leftSymbol, a), (rightSymbol, b)]),
      right = r)

x = common_vars.x()
def reflexive(e):
  return constructors.Forall([x],
      constructors.Implies(predicate = constructors.Intersect(x, constructors.Project(e, domainSymbol)),
        consequent = EquivalentUnder(x, x, constructors.Project(e, relationSymbol))))

x = common_vars.x()
y = common_vars.y()
def symmetric(e):
  return constructors.Forall([x, y],
      constructors.Implies(
        predicate = constructors.And(
          [ constructors.Intersect(x, constructors.Project(e, domainSymbol))
          , constructors.Intersect(y, constructors.Project(e, domainSymbol))
          , EquivalentUnder(x, y, constructors.Project(e, relationSymbol)) ]),
        consequent = EquivalentUnder(y, x, constructors.Project(e, relationSymbol))))

x = common_vars.x()
y = common_vars.y()
z = common_vars.z()
def transitive(e):
  return constructors.Forall([x, y, z],
      constructors.Implies(
        predicate = constructors.And(
          [ constructors.Intersect(x, constructors.Project(e, domainSymbol))
          , constructors.Intersect(y, constructors.Project(e, domainSymbol))
          , constructors.Intersect(z, constructors.Project(e, domainSymbol))
          , EquivalentUnder(x, y, constructors.Project(e, relationSymbol))
          , EquivalentUnder(y, z, constructors.Project(e, relationSymbol)) ]),
        consequent = EquivalentUnder(x, z, constructors.Project(e, relationSymbol))))

A = common_vars.A()
claim = constructors.Forall([A],
    constructors.Iff(
      left = constructors.SymbolAnd(
        [ (reflexiveSymbol, reflexive(A))
        , (symmetricSymbol, symmetric(A))
        , (transitiveSymbol, transitive(A))]),
      right = constructors.Intersect(left = A, right = equivalence)))

lib = library.Library(claims = [claim], variables = [equivalence])
