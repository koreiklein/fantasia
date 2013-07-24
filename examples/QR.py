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

def G(xs):
  raise Exception("%s"%(xs,))

proof = lib.beginProof()

proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      constructors.assume(x, claim)))

proof = proof.forwardFollow(lambda p:
    p.simplifyBottom())

proof = proof.forwardFollow(lambda p:
    p.advance().forwardFollow(lambda p:
      p.advance(0).forwardFollow(lambda p:
        p.advance())))

proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      common_formulas.forwardInductionOnIExists(x, 0)))

proof = proof.forwardFollow(lambda p:
    p.advanceAll([None, None, 0, None, 1, None]))

proof = proof.forwardFollow(lambda p:
    p.instantiateBottomInOrder([natural.zero, natural.zero]))

proof = proof.forwardFollow(lambda p:
    p.advanceAll([0]))

proof = proof.forwardFollow(lambda p:
    p.importAboutNegating(variables = [b],
      f = lambda bindings, value: natural.natural_less in value.translate().freeVariables(),
      g = lambda xs: 0))

proof = proof.forwardFollow(lambda p:
    p.retreat(4))

proof = proof.forwardFollow(lambda p:
    p.heavySimplify())


proof = proof.forwardFollow(lambda p:
    p.advanceAll([1, None]))

proof = proof.forwardFollow(lambda p:
    p.importAboutNegating(variables = [natural.zero, b],
      f = lambda bindings, value: times in value.applied_variables(),
      g = lambda xs: 0))

proof = proof.forwardFollow(lambda p:
    p.retreat(3).forwardFollow(lambda p:
      p.simplifyBottom()))

proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [natural.zero, Times(natural.zero, b), natural.zero],
      f = lambda bindings, value: plus in value.applied_variables(),
      g = lambda xs: 0).forwardFollow(lambda p:
        p.simplifyBottom()))

proof = proof.forwardFollow(lambda p:
    p.advance(0).forwardFollow(lambda p:
      p.onPathFollow(lambda x:
        x.forwardUnalways().forwardFollow(lambda x:
          x.forwardRightToLeft()))))

proof = proof.forwardFollow(lambda p:
    p.heavySimplify())

proof = proof.forwardFollow(lambda p:
    p.advanceAll([None, None, 0]))



proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      x.backwardAdmitRight()))

proof = proof.forwardFollow(lambda p:
    p.importAboutNegating(variables = [b],
      f = lambda bindings, value: times in value.applied_variables() and natural.zero in value.translate().freeVariables(),
      g = lambda xs: 0))

proof = proof.forwardFollow(lambda p:
    p.retreat(9))

proof = proof.forwardFollow(lambda p:
    p.heavySimplify())

proof = proof.forwardFollow(lambda p:
    p.heavySimplify())

proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      x.forwardGatherExistentials()))

a_prime = proof.arrow.tgt.bottom().bindings[1].variable

proof = proof.forwardFollow(lambda p:
    p.advance())
proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [r],
      f = lambda bindings, value: natural.S in value.applied_variables(),
      g = lambda xs: 0))

proof = proof.forwardFollow(lambda p:
    p.simplifyBottom())
proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [constructors.S(r), b],
      f = lambda bindings, value: natural.natural_less in value.translate().freeVariables(),
      g = lambda xs: 0))
proof = proof.forwardFollow(lambda p:
    p.simplifyBottom())
proof = proof.forwardFollow(lambda p:
    p.advanceAll([0, None, 2]))
proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [r, b],
      f = lambda bindings, value: natural.natural_less in value.translate().freeVariables(),
      g = lambda xs: 1))
proof = proof.forwardFollow(lambda p:
    p.retreat(1))
proof = proof.forwardFollow(lambda p:
    p.heavySimplify())
proof = proof.forwardFollow(lambda p:
    p.retreat(1))
proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      x.forwardUnalways()))
proof = proof.forwardFollow(lambda p:
    p.retreat(1))

proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      x.forwardDistribute(5, 0)))
proof = proof.forwardFollow(lambda p:
    p.advanceAll([0, 0, 0, None]))

proof = proof.forwardFollow(lambda p:
    p.instantiateBottomInOrder([q, S(r)]))
proof = proof.forwardFollow(lambda p:
    p.heavySimplify())
proof = proof.forwardFollow(lambda p:
    p.retreat(1))

proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [q, b],
      f = lambda bindings, value: times in value.applied_variables(),
      g = lambda x: 0).forwardFollow(lambda p:
        p.simplifyBottom()))
proof = proof.forwardFollow(lambda p:
    p.advance(1))
proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [a_prime],
      f = lambda bindings, value: natural.S in value.applied_variables(),
      g = lambda xs: 0).forwardFollow(lambda p:
        p.simplifyBottom()))
proof = proof.forwardFollow(lambda p:
    p.advance(1))

proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [S(r), Times(q, b), S(a_prime)],
      f = lambda bindings, value: plus in value.applied_variables(),
      g = lambda xs: 0).forwardFollow(lambda p:
        p.simplifyBottom().forwardFollow(lambda p:
          p.advanceAll([0, None]))))

proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      x.forwardRightToLeft()))
proof = proof.forwardFollow(lambda p:
    p.retreat(2))
proof = proof.forwardFollow(lambda p:
    p.heavySimplify())
proof = proof.forwardFollow(lambda p:
    p.advanceAll([0, None, None, 0]))
proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      x.backwardAdmitLeft()))
proof = proof.forwardFollow(lambda p:
    p.instantiateBottomInOrder(variables = [r]))
proof = proof.forwardFollow(lambda p:
    p.retreat(2))
proof = proof.forwardFollow(lambda p:
    p.simplifyBottom())

proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [r, Times(q, b)],
      f = lambda bindings, value: plus in value.applied_variables(),
      g = lambda xs: 0))
proof = proof.forwardFollow(lambda p:
    p.retreat(3))
proof = proof.forwardFollow(lambda p:
    p.simplifyBottom())

proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [Plus(r, Times(q, b)), a_prime],
      f = lambda bindings, value: natural.S in value.applied_variables(),
      g = lambda xs: 0))

proof = proof.forwardFollow(lambda p:
    p.retreat(4))

proof = proof.forwardFollow(lambda p:
    p.heavySimplify())

proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [q],
      f = lambda bindings, value: natural.S in value.applied_variables(),
      g = lambda xs: 0))

proof = proof.forwardFollow(lambda p:
    p.heavySimplify())

proof = proof.forwardFollow(lambda p:
    p.advanceAll([1, None]))

proof = proof.forwardFollow(lambda p:
    p.instantiateBottomInOrder(variables = [S(q), natural.zero]))

proof = proof.forwardFollow(lambda p:
    p.retreat(1))

proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [b],
      f = lambda bindings, value: natural.zero in value.translate().freeVariables(),
      g = lambda xs: 2))
proof = proof.forwardFollow(lambda p:
    p.retreat(1))
proof = proof.forwardFollow(lambda p:
    p.heavySimplify())

proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [a_prime],
      f = lambda bindings, value: natural.S in value.applied_variables(),
      g = lambda xs: 0))

proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [S(q), b],
      f = lambda bindings, value: times in value.applied_variables(),
      g = lambda xs: 0))
proof = proof.forwardFollow(lambda p:
    p.heavySimplify())

proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [natural.zero, Times(S(q), b), S(a_prime)],
      f = lambda bindings, value: plus in value.applied_variables(),
      g = lambda xs: 0))
proof = proof.forwardFollow(lambda p:
    p.simplifyBottom())
proof = proof.forwardFollow(lambda p:
    p.advanceAll([0, None]))
proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      x.forwardRightToLeft()))
proof = proof.forwardFollow(lambda p:
    p.advanceAll([None, None, 0]))
proof = proof.forwardFollow(lambda p:
    p.heavySimplify())
proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      x.backwardAdmitRight()))
proof = proof.forwardFollow(lambda p:
    p.retreat(5))
proof = proof.forwardFollow(lambda p:
    p.heavySimplify())

proof = proof.forwardFollow(lambda p:
    p.advanceAll([0, None, None, 0]))

proof = proof.forwardFollow(lambda p:
    p.importAboutNegating(variables = [S(q), b, S(a_prime)],
      f = lambda bindings, value: times in value.applied_variables(),
      g = lambda xs: 0))

proof = proof.forwardFollow(lambda p:
    p.advanceAll([0, None]))

proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      x.forwardRightToLeft()))
proof = proof.forwardFollow(lambda p:
    p.advanceAll([None, None, 0]))

proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      x.backwardAdmitLeft()))
proof = proof.forwardFollow(lambda p:
    p.instantiateBottomInOrder(variables = [q]))

proof = proof.forwardFollow(lambda p:
    p.retreat(0))
proof = proof.forwardFollow(lambda p:
    p.heavySimplify())

def F(bindings, value):
  free = value.translate().freeVariables()
  return r in free and q in free and b in free and a_prime in free

proof = proof.forwardFollow(lambda p:
    p.importAboutNegating(variables = [],
      f = F,
      g = lambda xs: 0))

proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [q, b],
      f = lambda bindings, value: natural.natural in value.translate().freeVariables(),
      g = lambda xs: 1))

proof = proof.forwardFollow(lambda p:
    p.heavySimplify())

proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [S(r), Times(q, b), S(a_prime)],
      f = lambda bindings, value: plus in value.applied_variables(),
      g = lambda xs: 0))

proof = proof.forwardFollow(lambda p:
    p.simplifyBottom())
proof = proof.forwardFollow(lambda p:
    p.advanceAll([0, None]))
proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      x.forwardRightToLeft()))
proof = proof.forwardFollow(lambda p:
    p.advanceAll([None, None, 0]))
proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      x.backwardAdmitLeft()))
proof = proof.forwardFollow(lambda p:
    p.instantiateBottomInOrder(variables = [r]))
proof = proof.forwardFollow(lambda p:
    p.retreat(2).forwardFollow(lambda p:
      p.heavySimplify()))

proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [r, Times(q, b)],
      f = lambda bindings, value: natural.natural in value.translate().freeVariables(),
      g = lambda xs: 0))

proof = proof.forwardFollow(lambda p:
    p.heavySimplify())

proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [Plus(r, Times(q, b)), a_prime],
      f = lambda bindings, value: natural.S in value.applied_variables(),
      g = lambda xs: 0))

proof = proof.forwardFollow(lambda p:
    p.retreat(3).forwardFollow(lambda p:
      p.heavySimplify()))

proof = proof.forwardFollow(lambda p:
    p.importAbout(variables = [],
      f = lambda bindings, value: value.__class__ == EnrichedIdentical,
      g = lambda xs: 1))
proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      x.forwardSubstituteIdentical(b, S(r))))
proof = proof.forwardFollow(lambda p:
    p.retreat(14))
proof = proof.forwardFollow(lambda p:
    p.heavySimplify())

def f(e, x):
  print "Class = ", x.__class__
  print "Covariant" if e.covariant() else "Contravariant"
  print x
  print x.top_level_render()._backend
  print '==========================================================='
  return x.identity()

proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x: f(p.endofunctor, x)))
