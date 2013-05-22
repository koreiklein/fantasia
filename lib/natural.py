# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol, enriched
from lib import equivalence, library, common_vars, common_symbols, function

natural = enriched.StringVariable('N')

natural_less = enriched.StringVariable('<')
smaller = symbol.StringSymbol('smaller')
greater = symbol.StringSymbol('greater')

natural_successor = enriched.StringVariable('S')
before = symbol.StringSymbol('before')
after = symbol.StringSymbol('after')

def Natural(n):
  return equivalence.InDomain(n, natural)

def Successor(a, b):
  return enriched.EnrichedHolds(enriched.ProductVariable([(before, a), (after, b)]), natural_successor)

def Equal(a, b):
  return equivalence.EqualUnder(a, b, natural)

def Less(a, b):
  return enriched.EnrichedHolds(
      enriched.VariableProduct([(smaller, a), (greater, b)]), natural_less)

naturalIsEquivalence = equivalence.IsEquivalence(natural)

natural_successor_function = enriched.VariableProduct(
    [ (common_symbols.functionPairsSymbol, natural_successor)
    , (common_symbols.srcSymbol, natural)
    , (common_symbols.tgtSymbol, natural)])

successorIsFunction = function.IsFunction(natural_successor_function)

a = common_vars.a()
successorIsGreater = enriched.SimpleEnrichedForall([(a, natural)],
    Less(a, enriched.Apply(a, natural_successor_function)))

zero = enriched.StringVariable('zero')
zeroNatural = Natural(zero)

n = common_vars.n()
zeroFirst = enriched.SimpleEnrichedForall([(n, natural)],
    enriched.Not(Equal(enriched.Apply(n, natural_successor_function), zero)))

pre_lib = library.Library(
    claims = [ successorIsGreater.translate()
             , naturalIsEquivalence
             , zeroNatural
             , zeroFirst
             , successorIsFunction
              ],
    variables = [natural, zero, natural_less, natural_successor])

lib = pre_lib.union(function.lib)
