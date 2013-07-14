# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import constructors
from calculus.enriched.constructors import *
from calculus import variable
from lib import natural, library, common_vars, equivalence, function, common_symbols, common_formulas

def ForallNatural(xs, value):
  return Forall(
      [BoundedVariableBinding(x, natural.natural) for x in xs],
      value)

def ExistsNatural(xs, value):
  return Exists(
      [BoundedVariableBinding(x, natural.natural) for x in xs],
      value)

def S(a):
  return variable.ApplySymbolVariable(a, natural.S)

def Equal(a, b):
  return Identical(a, b)

# define addition
plus = variable.StringVariable('+', infix = (common_symbols.leftSymbol, common_symbols.rightSymbol))

def Plus(a, b):
  return variable.ApplySymbolVariable(
      variable.ProductVariable(
        [ (common_symbols.leftSymbol, a)
        , (common_symbols.rightSymbol, b) ]), plus)

def ExpandPlus(a, b, c):
  base = And([Equal(a, natural.zero),
    Equal(b, c)])
  z = common_vars.z()
  step = ExistsNatural([z],
      And([Equal(S(z), a),
        Equal(S(Plus(z, b)), c)]))
  return Or([base, step])

a = common_vars.a()
b = common_vars.b()
c = common_vars.c()
define_plus = Iff(
    left = Equal(Plus(a, b), c),
    right = ExpandPlus(a, b, c))

# define multiplication
times = variable.StringVariable('*', infix = (common_symbols.leftSymbol, common_symbols.rightSymbol))

def Times(a, b):
  return variable.ApplySymbolVariable(
      variable.ProductVariable(
        [ (common_symbols.leftSymbol, a)
        , (common_symbols.rightSymbol, b) ]), times)

def ExpandTimes(a, b, c):
  base = And([Equal(a, natural.zero), Equal(c, natural.zero)])
  z = common_vars.z()
  step =ExistsNatural([z],
      And([Equal(S(z), a), Equal(Plus(b, Times(z, b)), c)]))
  return Or([base, step])

a = common_vars.a()
b = common_vars.b()
c = common_vars.c()
define_times = Iff(
    left = Equal(Times(a, b), c),
    right = ExpandTimes(a, b, c))

supplementals = [define_plus, define_times]

# A proof that forall a : N, b : N . if b != 0 then exists q : N, r : N . r < b | r + q*b = a
a = common_vars.a()
b = common_vars.b()

q = common_vars.q()
r = common_vars.r()

claim = ForallNatural([a, b],
    Implies([Not(Equal(b, natural.zero))],
      ExistsNatural([q, r], And([ natural.Less(r, b)
                                , Equal(Plus(r, Times(q,b)), a)]))))

lib = library.Library(claims = supplementals, variables = [plus, times], sub_libraries =[natural.lib], name = "+/*")
proof = lib.beginProof()

proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      constructors.assume(x, claim)))

proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      x.forwardSimplify()))

proof = proof.forwardFollow(lambda p:
    p.advance().forwardFollow(lambda p:
      p.advance(0).forwardFollow(lambda p:
        p.advance())))


def g(p):
  return p.onPathFollow(lambda x:
      common_formulas.forwardInductionOnIExists(x, 0))

proof = proof.forwardFollow(lambda p:
    g(p))

def f(x):
  return x.identity()

proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x: f(x)))
