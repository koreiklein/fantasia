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

def ge_zero(n):
  return natural.Compare(natural.zero, n, False)

increasing = "increasing"
weakening = "weakening"
successorExists = "successorExists"
transitivity = "transitivity"
reflexivity = "reflexivity"
main = byInduction(ge_zero)

starting_claim = linearui.And([ natural.increasing.addMark(increasing)
                              , main.addMark(marks.selection)
                              , natural.successorExists.addMark(successorExists)
                              , natural.transitivity.addMark(transitivity)
                              , natural.weakening.addMark(weakening)
                              , natural.reflexivity.addMark(reflexivity)
                              , natural.zero_natural ])

transition = starting_claim.forwardImportToPar(2, 1, 1)

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda x:
        x.forwardConjQuantifier(0))))

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda x:
        x.forwardOnBodyFollow(lambda x:
          x.forwardAssociateIn(0)))))

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda quantifier:
        quantifier.forwardOnBodyFollow(lambda x:
          x.forwardOnIthFollow(3, lambda x:
            x.forwardEliminate(0, quantifier.variables()[0]))))))

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda quantifier:
        quantifier.forwardOnBodyFollow(lambda x:
          x.forwardOnIthFollow(3, lambda x:
            x.forwardRemoveQuantifier())))))

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda x:
        x.forwardOnBodyFollow(lambda x:
          x.forwardImportToPar(0, 3, 0)))))

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda x:
        x.forwardOnBodyFollow(lambda x:
          x.forwardOnIthFollow(2, lambda x:
            x.forwardOnIthFollow(0, lambda x:
              x.forwardApply(1, 0)))))))

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda x:
        x.forwardOnBodyFollow(lambda x:
          x.forwardOnIthFollow(2, lambda x:
            x.forwardRemoveUnit(0))))))

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda x:
        x.forwardOnBodyFollow(lambda x:
          x.forwardOnIthFollow(2, lambda x:
            x.forwardUnsingleton())))))

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda x:
        x.forwardOnBodyFollow(lambda x:
          x.forwardConjQuantifier(2)))))

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda x:
        x.forwardJoin())))

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda q:
        q.forwardOnBodyFollow(lambda x:
          x.forwardOnIthFollow(1, lambda x:
            x.forwardEliminate(0, q.variables()[1]).forwardFollow(lambda x:
              x.forwardRemoveQuantifier()))))))

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda x:
        x.forwardOnBodyFollow(lambda x:
          x.forwardAssociateIn(2).forwardFollow(lambda x:
          x.forwardImportToPar(2, 1, 0).forwardFollow(lambda x:
            x.forwardOnIthFollow(1, lambda x:
              x.forwardOnIthFollow(0, lambda x:
                x.forwardApply(1, 0)).forwardFollow(lambda x:
              x.forwardRemoveUnit(0)))))))))

transition = transition.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda x:
        x.forwardOnBodyFollow(lambda x:
          x.forwardImportToPar(2, 1, 0).forwardFollow(lambda x:
            x.forwardOnIthFollow(1, lambda x:
              x.forwardOnIthFollow(0, lambda x:
                x.forwardApply(1, 0)).forwardFollow(lambda x:
              x.forwardRemoveUnit(0))))))))

transition = transition.forwardFollow(lambda claim:
    claim.forwardImportToPar(0, 1, 1).forwardFollow(lambda x:
      x.forwardOnIthFollow(0, lambda x:
        x.forwardOnIthFollow(1, lambda x:
          x.forwardConjQuantifier(0).forwardFollow(lambda q:
            q.forwardOnBodyFollow(lambda x:
              x.forwardAssociateIn(0).forwardFollow(lambda x:
                x.forwardOnIthFollow(3, lambda x:
                  x.forwardEliminate(1, q.variables()[1]).forwardFollow(lambda x:
                    x.forwardEliminate(0, q.variables()[0]).forwardFollow(lambda x:
                      x.forwardRemoveQuantifier()))))))))))

transition = transition.forwardFollow(lambda x:
      x.forwardOnIthFollow(0, lambda x:
        x.forwardOnIthFollow(1, lambda x:
          x.forwardOnBodyFollow(lambda x:
            x.forwardImportToPar(2, 3, 0).forwardFollow(lambda x:
              x.forwardOnIthFollow(2, lambda x:
                x.forwardOnIthFollow(0, lambda x:
                  x.forwardApply(1, 0)).forwardFollow(lambda x:
                    x.forwardRemoveUnit(0).forwardFollow(lambda x:
                      x.forwardUnsingleton()))))))))

transition = transition.forwardFollow(lambda x:
    x.forwardImportToPar(1, 0, 1).forwardFollow(lambda x:
      x.forwardOnIthFollow(0, lambda x:
        x.forwardOnIthFollow(1, lambda x:
          x.forwardConjQuantifier(0).forwardFollow(lambda x:
            x.forwardOnBodyFollow(lambda x:
              x.forwardAssociateIn(0)))))))

transition = transition.forwardFollow(lambda x:
    x.forwardOnIthFollow(0, lambda x:
      x.forwardOnIthFollow(1, lambda q:
        q.forwardOnBodyFollow(lambda x:
          x.forwardOnIthFollow(3, lambda x:
            x.forwardEliminateMultiple(
              [natural.zero, q.variables()[0], q.variables()[1]]).forwardFollow(lambda x:
                x.forwardRemoveQuantifier()))))))

transition = transition.forwardFollow(lambda x:
    x.forwardOnIthFollow(0, lambda x:
      x.forwardOnIthFollow(1, lambda x:
        x.forwardOnBodyFollow(lambda x:
          x.forwardRemoveFromPar(0, 3, 0).forwardFollow(lambda x:
            x.forwardRemoveFromPar(1, 2, 0).forwardFollow(lambda x:
              x.forwardOnIthFollow(1, lambda x:
                x.forwardUnsingleton())))))))

transition = transition.forwardFollow(lambda x:
    x.forwardOnIthFollow(2, lambda x:
      x.forwardEliminate(0, natural.zero).forwardFollow(lambda x:
        x.forwardRemoveQuantifier())))

transition = transition.forwardFollow(lambda x:
    x.forwardRemoveFromPar(3, 2, 0).forwardFollow(lambda x:
      x.forwardOnIthFollow(2, lambda x:
        x.forwardUnsingleton())))

transition = transition.forwardFollow(lambda x:
    x.forwardRemoveFromPar(2, 0, 0))

transition = transition.forwardFollow(lambda x:
    x.forwardImportToPar(1, 0, 0)).forwardFollow(lambda x:
        x.forwardUnsingleton())

transition = transition.forwardFollow(lambda x:
    x.forwardOnIthFollow(0, lambda x:
      x.forwardConjQuantifier(0).forwardFollow(lambda x:
        x.forwardOnBodyFollow(lambda x:
          x.forwardAssociateIn(0)))))

transition = transition.forwardFollow(lambda x:
    x.forwardOnIthFollow(0, lambda q:
      q.forwardOnBodyFollow(lambda x:
        x.forwardOnIthFollow(2, lambda x:
          x.forwardEliminateMultiple([natural.zero, q.variables()[1]]).forwardFollow(lambda x:
            x.forwardRemoveQuantifier())).forwardFollow(lambda x:
              x.forwardRemoveFromPar(1, 2, 0).forwardFollow(lambda x:
                x.forwardOnIthFollow(1, lambda x:
                  x.forwardUnsingleton()))))))

transition = transition.forwardFollow(lambda x:
    x.forwardOnIthFollow(0, lambda x:
      x.forwardOnBodyFollow(lambda x:
        x.forwardOnIthFollow(0, lambda x:
          x.forwardUnsingleton()))))

transition = transition.forwardFollow(lambda x:
    x.forwardOnIthFollow(0, lambda x:
      x.forwardOnBodyFollow(lambda x:
        x.forwardApply(1, 0))))

transition = transition.forwardFollow(lambda x:
    x.forwardOnIthFollow(0, lambda x:
      x.forwardUnusedExistential(0).forwardFollow(lambda x:
        x.forwardUnusedExistential(0).forwardFollow(lambda x:
          x.forwardRemoveQuantifier()))))

transition = transition.forwardFollow(lambda x:
    x.forwardRemoveUnit(0).forwardFollow(lambda x:
      x.forwardUnsingleton()))

# Now wrap the preceeding transition into a transition that concludes that 5 is at least 0.

s = linearui.And([starting_claim, natural.exists_five])

t = s.forwardOnIthFollow(0, lambda x: transition)
t = t.forwardFollow(lambda x:
    x.forwardConjQuantifier(1))
t = t.forwardFollow(lambda x:
    x.forwardOnBodyFollow(lambda x:
      x.forwardOnIthFollow(0, lambda x:
        x.forwardEliminate(0, natural.five).forwardFollow(lambda x:
          x.forwardRemoveQuantifier()))))
t = t.forwardFollow(lambda x:
    x.forwardOnBodyFollow(lambda x:
      x.forwardRemoveFromPar(1, 0, 0)))

t = t.forwardFollow(lambda x:
    x.forwardOnBodyFollow(lambda x:
      x.forwardUnsingleton().forwardFollow(lambda x:
        x.forwardUnsingleton())))

ending_claim = t.tgt()


