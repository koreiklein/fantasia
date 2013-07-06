# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import formula, constructors, endofunctor
from lib.common_symbols import leftSymbol, rightSymbol, relationSymbol, domainSymbol, inputSymbol, outputSymbol, functionPairsSymbol
from lib import common_vars
from calculus import variable

def IsEquivalence(e):
  return constructors.Always(constructors.Holds(e, common_vars.equivalence))

def Maps(a, b, f):
  return constructors.Always(constructors.Holds(
      variable.ProductVariable([ (inputSymbol, a)
                               , (outputSymbol, b)]),
      variable.ApplySymbolVariable(f, functionPairsSymbol)))

def IsFunction(f):
  return constructors.Always(constructors.Holds(f, common_vars.function))

InDomain = formula.InDomain
Equal = formula.Equal
