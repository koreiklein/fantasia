# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from logic import linearui
from logic.lib import natural
from logic.lib import common_vars
import marks

# These definitions of induction should by no means be considered final.
# As the combinators in logic.linearui become more sophisticated, we may
# wish to give more elaborate definitions of induction.
# For example, all claims about numbers being natural might be hidden.
# For another example, we may use m = n + 1 instead of natural.Successor(n, m).

n = common_vars.n()
m = common_vars.m()
k = common_vars.k()
# claim: a function from a variable to a formula saying the claim holds of
# that variable.
def byInduction(claim):
  return linearui.Implies(
      predicate = linearui.And([ claim(natural.zero)
                               , linearui.Forall([n]
                               , linearui.Implies(
                                  predicate = linearui.And([ natural.IsNatural(n)
                                                           , claim(n)]),
                                  consequent =
                                    linearui.Exists([m],
                                      linearui.And([ natural.IsNatural(m)
                                                   , natural.Successor(n, m)
                                                   , claim(m)]))))]),
      consequent = linearui.Forall([k],
        linearui.Implies(
          predicate = natural.IsNatural(k),
          consequent = claim(k))))

#p = common_vars.p()
#n = common_vars.n()
#m = common_vars.m()
#k = common_vars.k()
#induction = linearui.Forall([p],
#    linearui.Implies(
#      predicate = linearui.And([ linearui.Holds(p, [natural.zero])
#                               , linearui.Forall([n],
#                                 linearui.Implies(
#                                  predicate = And([ natural.IsNatural(n)
#                                                  , linearui.Holds(relation = p,
#                                                    arg = n)]),
#                                  consequent =
#                                    linearui.Exists([m],
#                                      linearui.And([ natural.IsNatural(m)
#                                                   , natural.Successor(n, m)
#                                                   , linearui.Holds(relation = p,
#                                                     arg = m) ]))
#                                  ))]),
#      consequent = linearui.Forall([k],
#        linearui.Implies(
#          predicate = natural.IsNatural(n = k),
#          consequent = linearui.Holds(relation = p, arg = k)))))

def ge_zero(n):
  return natural.Compare(natural.zero, n, False)

main = byInduction(ge_zero)

increasing = "increasing"
weakening = "weakening"
successorExists = "successorExists"
transitivity = "transitivity"


starting_claim = linearui.And([ natural.increasing.addMark(increasing)
                              , main.addMark(marks.selection)
                              , natural.weakening.addMark(weakening)
                              , natural.successorExists.addMark(successorExists)
                              , natural.transitivity.addMark(transitivity) ])

transition = starting_claim.forwardImportToPar(3, 1, 1)
transition.translate()

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda x:
        x.forwardConjQuantifier(0))))
transition.translate()

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda x:
        x.forwardOnBodyFollow(lambda x:
          x.forwardAssociateIn(0)))))
transition.translate()

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda quantifier:
        quantifier.forwardOnBodyFollow(lambda x:
          x.forwardOnIthFollow(3, lambda x:
            x.forwardEliminate(0, quantifier.variables()[0]))))))
transition.translate()

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda quantifier:
        quantifier.forwardOnBodyFollow(lambda x:
          x.forwardOnIthFollow(3, lambda x:
            x.forwardRemoveQuantifier())))))
transition.translate()

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda x:
        x.forwardOnBodyFollow(lambda x:
          x.forwardImportToPar(0, 3, 0)))))
transition.translate()

transition.translate()

ending_claim = transition.tgt()
