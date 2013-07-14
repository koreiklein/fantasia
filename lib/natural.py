# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol, variable
from calculus.enriched import constructors
from lib import equivalence, library, common_vars, common_symbols, function
from lib.common_formulas import IsEquivalence, InDomain, Equal

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

naturalIsEquivalence = constructors.Always(IsEquivalence(natural))

successorIsFunction = function.IsFunction(S)

a = common_vars.a()
b = common_vars.b()
successorIsGreater = constructors.Forall(
    [ constructors.BoundedVariableBinding(a, natural)
    , constructors.BoundedVariableBinding(b, natural)],
    constructors.Implies(predicates = [Successor(a, b)], consequent = Less(a, b)))

zero = common_vars.zero
zeroNatural = Natural(zero)

n = common_vars.n()
m = common_vars.m()
zeroFirst = constructors.Forall(
    [ constructors.BoundedVariableBinding(n, natural)
    , constructors.BoundedVariableBinding(m, natural)],
    constructors.Implies(predicates = [Successor(n, m)],
      consequent = constructors.Not(Equal(m, zero, natural))))

allClaims = [ successorIsGreater
            , naturalIsEquivalence
            , zeroNatural
            , zeroFirst
            , successorIsFunction]

naturalClaims = constructors.And(allClaims)

lib = library.Library(
    name = "Nat",
    claims = [naturalClaims],
    variables = [natural, zero, natural_less, S],
    sub_libraries = [function.lib])

