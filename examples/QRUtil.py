# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>
import cPickle as pickle

from calculus.enriched import constructors
from calculus.enriched.constructors import *
from calculus.enriched.formula import Identical as EnrichedIdentical
from calculus import variable
from calculus.enriched.path import new_path, Arrow as PathArrow
from lib import natural, library, common_vars, equivalence, function, common_symbols, common_formulas

def sendProofToFile(proof, save_filename):
  pickle.dump(proof.arrow.enrichedArrow.compress(), open(save_filename, 'w'))

def readProofFromFile(save_filename):
  enrichedArrow = pickle.load(open(save_filename, 'r'))
  proof = library.Proof(library = lib,
      arrow = PathArrow(src = new_path(enrichedArrow.src),
        tgt = new_path(enrichedArrow.tgt),
        enrichedArrow = enrichedArrow))
  return proof

def ForallNatural(xs, value):
  return Forall(
      [BoundedVariableBinding(x, natural.natural) for x in xs],
      value)

def ExistsNatural(xs, value):
  return Exists(
      [BoundedVariableBinding(x, natural.natural) for x in xs],
      value)

# define addition
plus = variable.StringVariable('+', infix = (common_symbols.leftSymbol, common_symbols.rightSymbol))

def Plus(a, b):
  return variable.ApplySymbolVariable(
      variable.ProductVariable(
        [ (common_symbols.leftSymbol, a)
        , (common_symbols.rightSymbol, b) ]), plus)

def ExpandPlus(a, b, c):
  base = And([Equal(natural.zero, a),
    Equal(b, c)])
  z = common_vars.z()
  step = ExistsNatural([z],
      And([Equal(S(z), a),
        Equal(S(Plus(z, b)), c)]))
  return Or([base, step])

a = common_vars.a()
b = common_vars.b()
c = common_vars.c()
define_plus = Always(ForallNatural([a, b, c],
    Iff(left = Equal(Plus(a, b), c),
        right = ExpandPlus(a, b, c))))

a = common_vars.a()
b = common_vars.b()
plus_natural = Always(ForallNatural([a, b],
  natural.Natural(Plus(a, b))))


# define multiplication
times = variable.StringVariable('*', infix = (common_symbols.leftSymbol, common_symbols.rightSymbol))

def Times(a, b):
  return variable.ApplySymbolVariable(
      variable.ProductVariable(
        [ (common_symbols.leftSymbol, a)
        , (common_symbols.rightSymbol, b) ]), times)

def ExpandTimes(a, b, c):
  base = And([Equal(natural.zero, a), Equal(natural.zero, c)])
  z = common_vars.z()
  step =ExistsNatural([z],
      And([Equal(S(z), a), Equal(Plus(b, Times(z, b)), c)]))
  return Or([base, step])

a = common_vars.a()
b = common_vars.b()
c = common_vars.c()
define_times = Always(ForallNatural([a, b, c],
    Iff(left = Equal(Times(a, b), c),
        right = ExpandTimes(a, b, c))))

a = common_vars.a()
b = common_vars.b()
times_natural = Always(ForallNatural([a, b],
  natural.Natural(Times(a, b))))

a = common_vars.a()
times_absorbs = Always(ForallNatural([a],
  Equal(Times(natural.zero, a), natural.zero)))

supplementals = [define_plus, plus_natural, define_times, times_natural, times_absorbs]

# A proof that forall a : N, b : N . if b != 0 then exists q : N, r : N . r < b | r + q*b = a
a = common_vars.a()
b = common_vars.b()

q = common_vars.q()
r = common_vars.r()

claim = ForallNatural([a, b],
    Implies([constructors.Always(Not(Equal(natural.zero, b)))],
      ExistsNatural([q, r], And([ natural.Less(r, b)
                                , Equal(Plus(r, Times(q,b)), a)]))))

lib = library.Library(claims = supplementals, variables = [plus, times], sub_libraries =[natural.lib], name = "+/*")

