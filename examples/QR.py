# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

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
plus = variable.StringVariable('+')

def Plus(a, b):
  return variable.ApplySymbolVariable(
      variables.ProductVariable(
        [ (common_symbols.leftSymbol, a)
        , (common_symbols.rightSymbol, b) ]), plus)

def ExpandPlus(a, b, c):
  base = And([Equal(a, natural.zero),
    Equal(c, natural.zero)])
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
times = variables.StringVariable('*')

def Times(a, b):
  return variable.ApplySymbolVariable(
      variables.ProductVariable(
        [ (common_symbols.leftSymbol, a)
        , (common_symbols.rightSymbol, b) ]), times)

def ExpandTimes(a, b, c):
  base = And([Equal(a, natural.zero), Equal(c, natural.zero)])
  z = common_vars.z()
  step = And([Equal(S(z), a), Equal(Plus(b, Times(z, b)), c)])
  return Or([base, step])

a = common_vars.a()
b = common_vars.b()
c = common_vars.c()
define_times = Iff(
    left = Equal(Times(a, b), c),
    righht = ExpandTimes(a, b, c))

supplementals = And([])

# A proof that forall a : N, b : N . if b != 0 then exists q : N, r : N . r < b | r + q*b = a
a = common_vars.a()
b = common_vars.b()

q = common_vars.a()
r = common_vars.b()

claim = ForallNatural([a, b],
    Implies(Not(Equal(b, natural.zero)),
      ExistsNatural([q, r], And([natural.Less(r, b), Equal(Plus(r, Time(q,b)), a)]))))

proof = natural.lib.beginProof().forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      constructors.assume(x, claim)))

#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.forwardSimplify()))
