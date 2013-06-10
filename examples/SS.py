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

proof = proof.forwardFollow(lambda p:
    p.advanceLeft())

#L = proof.arrow.tgt.importFiltered(lambda x: natural.zero in x.freeVariables())
#L = proof.arrow.tgt.importFiltered(lambda x: True)
#for (B,f) in L:
#  print B

#proof = proof.forwardFollow(lambda p:
#    p.doImportFiltered(lambda x: natural.zero in x.freeVariables(), 1))
#compressedProof =  proof.arrow.arrow.translate().compress()

a = common_vars.a()
b = common_vars.b()
c = common_vars.c()
proof = proof.forwardFollow(lambda p:
    p.forwardOnPathFollow(lambda x:
      x.forwardAssume(basic.MultiBoundedForall([ (a, natural.natural)
                                               , (b, natural.natural)
                                               , (c, natural.natural)],
        basic.Implies(predicate = basic.MultiAnd(
          [ natural.Successor(a, b)
          , natural.Successor(b, c)]),
          consequent = natural.Less(a, c))))))

proof = proof.forwardFollow(lambda p:
          p.advance().forwardFollow(lambda p:
            p.advanceLeft().forwardFollow(lambda p:
              p.advance().forwardFollow(lambda p:
                p.advance().forwardFollow(lambda p:
                    p.advance().forwardFollow(lambda p:
                      p.advance().forwardFollow(lambda p:
                        p.advance().forwardFollow(lambda p:
                          p.advanceRight().forwardFollow(lambda p:
                            p.advanceRight().forwardFollow(lambda p:
                              p.advanceRight()))))))))))

#print [B for (B,A) in proof.arrow.tgt.universalIn([a, b])]
#print proof.arrow.tgt.importables_universalIn([a, b])
proof = proof.forwardFollow(lambda p:
    p.universalIn([a])[2])

x = proof.arrow.tgt.top()

proof = proof.forwardFollow(lambda p:
    p.liftExists().forwardFollow(lambda p:
      p.simplify()))
