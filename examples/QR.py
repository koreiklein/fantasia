# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from examples.QRUtil import *

proof = lib.beginProof()

# Uncomment the next block of code (or try adding your own) to continue the proof.
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      constructors.assume(x, claim)))


#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.forwardSimplify()))
#
#proof = proof.forwardFollow(lambda p:
#    p.advance().forwardFollow(lambda p:
#      p.advance(0).forwardFollow(lambda p:
#        p.advance())))
#
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      common_formulas.forwardInductionOnIExists(x, 0)))
#
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([None, None, 0, None, 1, None]))
#
#proof = proof.forwardFollow(lambda p:
#    p.instantiateBottomInOrder([natural.zero, natural.zero]))
#
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([0]))
#
#proof = proof.forwardFollow(lambda p:
#    p.importAboutNegating(variables = [b],
#      f = lambda bindings, value: natural.natural_less in value.translate().freeVariables(),
#      g = lambda xs: 0))
#
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([None, 0]))
#
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.forwardSimplify()))
#
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.forwardUnalways()))
#
#proof = proof.forwardFollow(lambda p:
#    p.retreat())
#
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.forwardDistributePairOther()))
#
#proof = proof.forwardFollow(lambda p:
#    p.retreat(4))
#
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([1, None]))
#
#proof = proof.forwardFollow(lambda p:
#    p.importAboutNegating(variables = [natural.zero, b],
#      f = lambda bindings, value: times in value.applied_variables(),
#      g = lambda xs: 0))
#
#proof = proof.forwardFollow(lambda p:
#    p.retreat(1).forwardFollow(lambda p:
#      p.simplifyBottom()))
#
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [natural.zero, Times(natural.zero, b), natural.zero],
#      f = lambda bindings, value: plus in value.applied_variables(),
#      g = lambda xs: 0).forwardFollow(lambda p:
#        p.simplifyBottom()))
#
#proof = proof.forwardFollow(lambda p:
#    p.advance(0).forwardFollow(lambda p:
#      p.onPathFollow(lambda x:
#        x.forwardUnalways().forwardFollow(lambda x:
#          x.forwardRightToLeft()))))
#
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([None, None, 0]))
#
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.backwardAdmitRight()))
#
#proof = proof.forwardFollow(lambda p:
#    p.importAboutNegating(variables = [b],
#      f = lambda bindings, value: times in value.applied_variables() and natural.zero in value.translate().freeVariables(),
#      g = lambda xs: 0))
#
#proof = proof.forwardFollow(lambda p:
#    p.retreat(7))
#
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([None, None, 0, None, 0, None, None]))
#proof = proof.forwardFollow(lambda p:
#    p.simplifyBottom())
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([None]))
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#proof = proof.forwardFollow(lambda p:
#    p.retreat(10))
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.forwardGatherExistentials()))
#
#a_prime = proof.arrow.tgt.bottom().bindings[1].variable
#
#proof = proof.forwardFollow(lambda p:
#    p.advance())
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [r],
#      f = lambda bindings, value: natural.S in value.applied_variables(),
#      g = lambda xs: 0))
#
#proof = proof.forwardFollow(lambda p:
#    p.simplifyBottom())
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [constructors.S(r), b],
#      f = lambda bindings, value: natural.natural_less in value.translate().freeVariables(),
#      g = lambda xs: 0))
#proof = proof.forwardFollow(lambda p:
#    p.simplifyBottom())
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([0, None, 2]))
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [r, b],
#      f = lambda bindings, value: natural.natural_less in value.translate().freeVariables(),
#      g = lambda xs: 1))
#proof = proof.forwardFollow(lambda p:
#    p.retreat(1))
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#proof = proof.forwardFollow(lambda p:
#    p.retreat(1))
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.forwardUnalways()))
#proof = proof.forwardFollow(lambda p:
#    p.retreat(1))
#
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.forwardDistribute(5, 0)))
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([0, 0, 0, None]))
#
#proof = proof.forwardFollow(lambda p:
#    p.instantiateBottomInOrder([q, S(r)]))
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#proof = proof.forwardFollow(lambda p:
#    p.retreat(1))
#
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [q, b],
#      f = lambda bindings, value: times in value.applied_variables(),
#      g = lambda x: 0).forwardFollow(lambda p:
#        p.simplifyBottom()))
#proof = proof.forwardFollow(lambda p:
#    p.advance(1))
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [a_prime],
#      f = lambda bindings, value: natural.S in value.applied_variables(),
#      g = lambda xs: 0).forwardFollow(lambda p:
#        p.simplifyBottom()))
#proof = proof.forwardFollow(lambda p:
#    p.advance(1))
#
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [S(r), Times(q, b), S(a_prime)],
#      f = lambda bindings, value: plus in value.applied_variables(),
#      g = lambda xs: 0).forwardFollow(lambda p:
#        p.simplifyBottom().forwardFollow(lambda p:
#          p.advanceAll([0, None]))))
#
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.forwardRightToLeft()))
#proof = proof.forwardFollow(lambda p:
#    p.retreat(2))
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([0, None, None, 0]))
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.backwardAdmitLeft()))
#proof = proof.forwardFollow(lambda p:
#    p.instantiateBottomInOrder(variables = [r]))
#proof = proof.forwardFollow(lambda p:
#    p.retreat(2))
#proof = proof.forwardFollow(lambda p:
#    p.simplifyBottom())
#
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [r, Times(q, b)],
#      f = lambda bindings, value: plus in value.applied_variables(),
#      g = lambda xs: 0))
#proof = proof.forwardFollow(lambda p:
#    p.retreat(3))
#proof = proof.forwardFollow(lambda p:
#    p.simplifyBottom())
#
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [Plus(r, Times(q, b)), a_prime],
#      f = lambda bindings, value: natural.S in value.applied_variables(),
#      g = lambda xs: 0))
#
#proof = proof.forwardFollow(lambda p:
#    p.retreat(4))
#
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [q],
#      f = lambda bindings, value: natural.S in value.applied_variables(),
#      g = lambda xs: 0))
#
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([1, None]))
#
#proof = proof.forwardFollow(lambda p:
#    p.instantiateBottomInOrder(variables = [S(q), natural.zero]))
#
#proof = proof.forwardFollow(lambda p:
#    p.retreat(1))
#
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [b],
#      f = lambda bindings, value: natural.zero in value.translate().freeVariables(),
#      g = lambda xs: 2))
#proof = proof.forwardFollow(lambda p:
#    p.retreat(1))
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [a_prime],
#      f = lambda bindings, value: natural.S in value.applied_variables(),
#      g = lambda xs: 0))
#
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [S(q), b],
#      f = lambda bindings, value: times in value.applied_variables(),
#      g = lambda xs: 0))
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [natural.zero, Times(S(q), b), S(a_prime)],
#      f = lambda bindings, value: plus in value.applied_variables(),
#      g = lambda xs: 0))
#proof = proof.forwardFollow(lambda p:
#    p.simplifyBottom())
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([0, None]))
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.forwardRightToLeft()))
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([None, None, 0]))
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.backwardAdmitRight()))
#proof = proof.forwardFollow(lambda p:
#    p.retreat(5))
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([0, None, None, 0]))
#
#proof = proof.forwardFollow(lambda p:
#    p.importAboutNegating(variables = [S(q), b, S(a_prime)],
#      f = lambda bindings, value: times in value.applied_variables(),
#      g = lambda xs: 0))
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([None, 0, None]))
#
#proof = proof.forwardFollow(lambda p:
#    p.simplifyBottom())
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.forwardRightToLeft()))
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([None, None, 0]))
#
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.backwardAdmitLeft()))
#proof = proof.forwardFollow(lambda p:
#    p.instantiateBottomInOrder(variables = [q]))
#
#proof = proof.forwardFollow(lambda p:
#    p.retreat(0))
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#
#def F(bindings, value):
#  free = value.translate().freeVariables()
#  return r in free and q in free and b in free and a_prime in free
#proof = proof.forwardFollow(lambda p:
#    p.importAboutNegating(variables = [],
#      f = F,
#      g = lambda xs: 0))
#
#proof = proof.forwardFollow(lambda p:
#    p.advance())
#
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [q, b],
#      f = lambda bindings, value: natural.natural in value.translate().freeVariables(),
#      g = lambda xs: 1))
#
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [S(r), Times(q, b), S(a_prime)],
#      f = lambda bindings, value: plus in value.applied_variables(),
#      g = lambda xs: 0))
#
#proof = proof.forwardFollow(lambda p:
#    p.simplifyBottom())
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([0, None]))
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.forwardRightToLeft()))
#proof = proof.forwardFollow(lambda p:
#    p.advanceAll([None, None, 0]))
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.backwardAdmitLeft()))
#proof = proof.forwardFollow(lambda p:
#    p.instantiateBottomInOrder(variables = [r]))
#proof = proof.forwardFollow(lambda p:
#    p.retreat(2).forwardFollow(lambda p:
#      p.heavySimplify()))
#
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [r, Times(q, b)],
#      f = lambda bindings, value: natural.natural in value.translate().freeVariables(),
#      g = lambda xs: 0))
#
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())
#
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [Plus(r, Times(q, b)), a_prime],
#      f = lambda bindings, value: natural.S in value.applied_variables(),
#      g = lambda xs: 0))
#
#proof = proof.forwardFollow(lambda p:
#    p.retreat(3).forwardFollow(lambda p:
#      p.heavySimplify()))
#
#proof = proof.forwardFollow(lambda p:
#    p.importAbout(variables = [],
#      f = lambda bindings, value: value.__class__ == EnrichedIdentical,
#      g = lambda xs: 1))
#proof = proof.forwardFollow(lambda p:
#    p.onPathFollow(lambda x:
#      x.forwardSubstituteIdentical(b, S(r))))
#proof = proof.forwardFollow(lambda p:
#    p.retreat(14))
#proof = proof.forwardFollow(lambda p:
#    p.heavySimplify())

