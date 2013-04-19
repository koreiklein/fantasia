# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic, enriched, basicConstructors as constructors
from lib import equivalence, common_vars

multiple_conjunction = constructors.multiple_conjunction

SymbolAnd = constructors.SymbolAnd
SymbolOr = constructors.SymbolOr
And = constructors.And
Or = constructors.Or
Implies = constructors.Implies
Iff = constructors.Iff
Exists = constructors.Exists
Forall = constructors.Forall
Intersect = constructors.Intersect
Not = constructors.Not
Project = constructors.Project
Inject = constructors.Inject
Coinject = constructors.Coinject
StringVariable = constructors.StringVariable

true = constructors.true
false = constructors.false

def Call(left, right, intermediate_variable = None):
  return enriched.Call(left = left, right = right, intermediate_variable = intermediate_variable)

def EnrichedExists(bindings, value):
  return basic.Always(enriched.Exists(bindings = bindings, value = value))

def EnrichedForall(bindings, value):
  return basic.Always(enriched.Forall(bindings = bindings, value = value))

def VariableBinding(variable, equivalence, unique = False, alternate_variable = None):
  return enriched.VariableBinding(
    variable = variable,
    equivalence = equivalence,
    unique = unique,
    alternate_variable = alternate_variable)
