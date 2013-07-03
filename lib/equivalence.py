# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import variable
from calculus.enriched import constructors
from lib import library, common_vars
from lib.common_symbols import leftSymbol, rightSymbol, relationSymbol, domainSymbol
from lib.common_formulas import InDomain, Equal, IsEquivalence

x = common_vars.x()
def reflexive(e):
  return constructors.Forall([constructors.BoundedVariableBinding(x, e)],
      Equal(x, x, e))

x = common_vars.x()
y = common_vars.y()
def symmetric(e):
  return constructors.Forall([ constructors.BoundedVariableBinding(x, e)
                             , constructors.BoundedVariableBinding(y, e)],
      constructors.Implies(
        predicates = [Equal(x, y, e)],
        consequent = Equal(y, x, e)))

x = common_vars.x()
y = common_vars.y()
z = common_vars.z()
def transitive(e):
  return constructors.Forall([ constructors.BoundedVariableBinding(x, e)
                             , constructors.BoundedVariableBinding(y, e)
                             , constructors.BoundedVariableBinding(z, e)],
      constructors.Implies(
        predicates = [ Equal(x, y, e)
                     , Equal(y, z, e) ],
        consequent = Equal(x, z, e)))

A = common_vars.A()
claim = constructors.Forall([constructors.OrdinaryVariableBinding(A)],
    constructors.Iff(
      right = constructors.And(
        [ reflexive(A)
        , symmetric(A)
        , transitive(A)]),
      left = IsEquivalence(A)))

lib = library.Library(claims = [claim],
    variables = [common_vars.equivalence], sub_libraries = [],
    name = "Equivalence")
