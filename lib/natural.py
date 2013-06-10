# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol, basic
from lib import equivalence, library, common_vars, common_symbols, function

from common_symbols import inputSymbol, outputSymbol

natural = basic.StringVariable('N')

smaller = symbol.StringSymbol('smaller')
greater = symbol.StringSymbol('greater')
natural_less = basic.StringVariable('<', infix = (smaller, greater))

natural_successor = basic.StringVariable('S')

def Natural(n):
  return basic.Always(equivalence.InDomain(n, natural))

def Successor(a, b):
  return basic.Always(
      basic.Holds(basic.ProductVariable([(inputSymbol, a), (outputSymbol, b)]), natural_successor))

def Equal(a, b):
  return equivalence.EqualUnder(a, b, natural)

def Less(a, b):
  return basic.Always(basic.Holds(
      basic.ProductVariable([(smaller, a), (greater, b)]), natural_less))

naturalIsEquivalence = basic.Always(equivalence.IsEquivalence(natural))

natural_successor_function = basic.ProductVariable(
    [ (common_symbols.functionPairsSymbol, natural_successor)
    , (common_symbols.srcSymbol, natural)
    , (common_symbols.tgtSymbol, natural)])

successorIsFunction = function.IsFunction(natural_successor_function)

a = common_vars.a()
b = common_vars.b()
successorIsGreater = basic.MultiBoundedForall([(a, natural)],
    basic.MultiExists([b],
      basic.MultiAnd([Successor(a, b), Less(a, b)])))

zero = basic.StringVariable('zero')
zeroNatural = Natural(zero)

n = common_vars.n()
m = common_vars.m()
zeroFirst = basic.MultiBoundedForall([(n, natural), (m, natural)],
    basic.Implies(predicate = Successor(n, m),
      consequent = basic.Not(Equal(m, zero))))

pre_lib = library.Library(
    claims = [ successorIsGreater
             , naturalIsEquivalence
             , zeroNatural
             , zeroFirst
             , successorIsFunction
              ],
    variables = [natural, zero, natural_less, natural_successor])

lib = pre_lib.union(function.lib)
