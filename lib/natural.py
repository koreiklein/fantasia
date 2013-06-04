# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol, basic
from lib import equivalence, library, common_vars, common_symbols, function

natural = basic.StringVariable('N')

smaller = symbol.StringSymbol('smaller')
greater = symbol.StringSymbol('greater')
natural_less = basic.StringVariable('<', infix = (smaller, greater))

natural_successor = basic.StringVariable('S')
before = symbol.StringSymbol('before')
after = symbol.StringSymbol('after')

def Natural(n):
  return basic.Always(equivalence.InDomain(n, natural))

def Successor(a, b):
  return basic.Always(
      basic.Holds(basic.ProductVariable([(before, a), (after, b)]), natural_successor))

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
successorIsGreater = basic.MultiBoundedForall([(a, natural)],
    Less(a, basic.Apply(a, natural_successor_function)))

zero = basic.StringVariable('zero')
zeroNatural = Natural(zero)

n = common_vars.n()
zeroFirst = basic.MultiBoundedForall([(n, natural)],
    basic.Not(Equal(basic.Apply(n, natural_successor_function), zero)))

pre_lib = library.Library(
    claims = [ successorIsGreater
             , naturalIsEquivalence
             , zeroNatural
             , zeroFirst
             , successorIsFunction
              ],
    variables = [natural, zero, natural_less, natural_successor])

lib = pre_lib.union(function.lib)
