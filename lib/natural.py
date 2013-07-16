# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol, variable
from calculus.enriched import constructors
from lib import equivalence, library, common_vars, common_symbols, function
from lib.common_formulas import IsEquivalence, InDomain, Identical

from common_symbols import inputSymbol, outputSymbol, domainSymbol, leftSymbol, rightSymbol, functionPairsSymbol

smaller = symbol.StringSymbol('smaller', type = symbol.projection)
greater = symbol.StringSymbol('greater', type = symbol.projection)
natural_less = variable.StringVariable('<', infix = (smaller, greater))

natural = common_vars.natural
S = common_vars.S
S_pairs = common_vars.S_pairs

def Natural(n):
  return InDomain(n, natural)

def Successor(a, b):
  return constructors.Always(
      constructors.Holds(variable.ProductVariable(
        [(inputSymbol, a), (outputSymbol, b)]), S_pairs))

def Less(a, b):
  return constructors.Always(constructors.Holds(
      variable.ProductVariable([(smaller, a), (greater, b)]), natural_less))

def ForallNatural(variables, value):
  return constructors.Forall(
      [constructors.BoundedVariableBinding(var, natural) for var in variables],
      value)

def ExistsNatural(variables, value):
  return constructors.Exists(
      [constructors.BoundedVariableBinding(var, natural) for var in variables],
      value)

naturalIsEquivalence = constructors.Always(IsEquivalence(natural))

successorIsFunction = function.IsFunction(S)

a = common_vars.a()
b = common_vars.b()
successorIsGreater = constructors.Always(ForallNatural([a], Less(a, constructors.S(a))))

zero = common_vars.zero
zeroNatural = Natural(zero)

a = common_vars.a()
zeroOrLess = constructors.Always(ForallNatural([a],
    constructors.Or([constructors.Always(Identical(zero, a)), Less(zero, a)])))

n = common_vars.n()
m = common_vars.m()
zeroFirst = constructors.Always(ForallNatural([n],
  constructors.Not(constructors.Always(Identical(zero, constructors.S(n))))))

a = common_vars.a()
b = common_vars.b()
c = common_vars.c()
transitivity = constructors.Always(ForallNatural([a, b, c],
    constructors.Implies([ Less(a, b), Less(b, c) ],
      Less(a, c))))

a = common_vars.a()
b = common_vars.b()
trichotomy = constructors.Always(ForallNatural([a, b],
    constructors.Or([ Less(a, b), constructors.Always(Identical(a, b)), Less(b, a) ])))

a = common_vars.a()
z = common_vars.z()
discrete = constructors.Always(ForallNatural([a, z],
    constructors.Not(constructors.And([Less(a, z), Less(z, constructors.S(a))]))))


allClaims = [ naturalIsEquivalence
            , successorIsFunction
            , zeroNatural
            , zeroFirst
            , zeroOrLess
            , successorIsGreater
            , transitivity
            , trichotomy
            , discrete
            ]

naturalClaims = constructors.And(allClaims)

lib = library.Library(
    name = "Nat",
    claims = [naturalClaims],
    variables = [natural, zero, natural_less, S],
    sub_libraries = [function.lib])

