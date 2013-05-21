# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic, enriched, basicConstructors as constructors
from lib import equivalence, common_vars

multiple_conjunction = constructors.multiple_conjunction

And = constructors.And
Or = constructors.Or
Implies = constructors.Implies
Iff = enriched.Iff
Exists = constructors.Exists
Forall = constructors.Forall
Not = constructors.Not
StringVariable = constructors.StringVariable

true = constructors.true
false = constructors.false

def Call(left, right, intermediate_variable = None):
  return enriched.Call(left = left, right = right, intermediate_variable = intermediate_variable)

def EnrichedExists(bindings, value):
  return basic.Always(enriched.Exists(bindings = bindings, value = value))

def EnrichedForall(bindings, value):
  return basic.Always(enriched.Forall(bindings = bindings, value = value))

def BoundedForall(variableEquivalencePairs, value):
  return EnrichedForall(
      bindings = [VariableBinding(variable = v, equivalence = e, unique = False)
                  for (v,e) in variableEquivalencePairs],
      value = value)

def BoundedExists(variableEquivalencePairs, value):
  return EnrichedExists(
      bindings = [VariableBinding(variable = v, equivalence = e, unique = False)
                  for (v,e) in variableEquivalencePairs],
      value = value)

def VariableBinding(variable, equivalence, unique = False, alternate_variable = None):
  return enriched.VariableBinding(
    variable = variable,
    equivalence = equivalence,
    unique = unique,
    alternate_variable = alternate_variable)

Holds = constructors.Holds
VariableProject = constructors.VariableProject
VariableProduct = constructors.VariableProduct

