# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic, enriched, basicConstructors as constructors

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

def EnrichedExists(bindings, value):
  return basic.Always(enriched.Exists(bindings = bindings, value = value))

def EnrichedForall(bindings, value):
  return basic.Always(basic.Not(enriched.Exists(bindings = bindings, value = basic.Not(value))))

def VariableBinding(variable, equivalence, unique = False, alternate_variable = None):
  return enriched.VariableBinding(
    variable = variable,
    equivalence = equivalence,
    unique = unique,
    alternate_variable = alternate_variable)
