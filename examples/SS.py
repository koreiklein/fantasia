# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic
from lib import natural, library, common_vars, equivalence, function

# A proof that forall n : N . S (S n) > n
n = common_vars.n()
# FIXME(koreiklein) Don't do it this way.  Implement an enriched functional notation.
a = common_vars.a()
b = common_vars.b()
#claim = constructors.EnrichedForall([constructors.VariableBinding(variable = n,
#                                     equivalence = natural.natural)],
#        constructors.EnrichedExists(
#          [ constructors.VariableBinding(variable = a, equivalence = natural.natural)
#          , constructors.VariableBinding(variable = b, equivalence = natural.natural)],
#          constructors.And(
#            [ natural.Successor(n, a)
#            , natural.Successor(a, b)
#            , natural.Less(n, b) ])))

# FIXME Reimplement.
#claim = constructors.EnrichedForall(
#    [constructors.VariableBinding(variable = n, equivalence = natural.natural, unique = True)],
#    natural.Less(n, constructors.Call(constructors.Call(n, natural.natural_successor),
#      natural.natural_successor)))

#proof = equivalence.lib.beginProof()
#proof = proof.forwardFollow(lambda x:
#          x.forwardAssume(claim))




proof = natural.lib.beginProof()

#L = proof.arrow.tgt.importFiltered(lambda x: natural.zero in x.freeVariables())
#L = proof.arrow.tgt.importFiltered(lambda x: True)
#for (B,f) in L:
#  print B

#proof = proof.forwardFollow(lambda p:
#    p.doImportFiltered(lambda x: natural.zero in x.freeVariables(), 1))
#compressedProof =  proof.arrow.arrow.translate().compress()

#a = common_vars.a()
#b = common_vars.b()
#c = common_vars.c()
#proof = proof.forwardFollow(lambda p:
#    p.forwardOnPathFollow(lambda x:
#      x.forwardAssume(basic.MultiBoundedForall([ (a, natural.natural)
#                                               , (b, natural.natural)
#                                               , (c, natural.natural)],
#        basic.Implies(predicate = basic.MultiAnd(
#          [ natural.Successor(a, b)
#          , natural.Successor(b, c)]),
#          consequent = natural.Less(a, c))))))
#
##print "Originally"
##print proof.arrow.tgt.bottom().simplify().tgt
##print "Was the formula."
#
#proof = proof.forwardFollow(lambda p:
#        p.advance().forwardFollow(lambda p:
#        p.advanceLeft().forwardFollow(lambda p:
#        p.advance().forwardFollow(lambda p:
#        p.advance().forwardFollow(lambda p:
#        p.advance().forwardFollow(lambda p:
#        p.advance().forwardFollow(lambda p:
#        p.advance().forwardFollow(lambda p:
#        p.advanceRight().forwardFollow(lambda p:
#        p.advanceRight().forwardFollow(lambda p:
#        p.advanceRight().forwardFollow(lambda p:
#        p.advance().forwardFollow(lambda p:
#        p.advance().forwardFollow(lambda p:
#        p.advance().forwardFollow(lambda p:
#        p.advanceRight().forwardFollow(lambda p:
#        p.identity())))))))))))))))
#
##proof = proof.forwardFollow(lambda p:
##    p.universalIn([a])[2])
##
##proof = proof.forwardFollow(lambda p:
##    p.liftExists().forwardFollow(lambda p:
##      p.simplify()))
##
##def f(p):
##  xs = p.universalIn([p.variables()[2]])
##  return xs[2]
##
##proof = proof.forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advanceLeft().forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advanceLeft().forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advanceRight().forwardFollow(lambda p:
##    p.advanceRight().forwardFollow(lambda p:
##    p.advanceRight().forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advance().forwardFollow(lambda p:
##    p.advanceRight().forwardFollow(lambda p:
##    p.advanceRight().forwardFollow(lambda p:
##      f(p))))))))))))))))))))))))))
##
##def t(p):
##  variables = p.variables()
##  #raise Exception("%s"%variables)
##  xs = p.universalIn([variables[3], variables[0], variables[1]])
##  raise Exception("%s"%[i.tgt for i in xs])
##proof = proof.forwardFollow(lambda p:
##    t(p))
###raise Exception("%s, %s"%(proof.arrow.tgt.bottom().__class__, proof.arrow.tgt.bottom()))
##
