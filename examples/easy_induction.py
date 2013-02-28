# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from extraction.python.lib import natural as naturalRep
from calculus import enriched
from lib import natural
from mark import common as marks

def ge_zero(n):
  return natural.Compare(natural.zero, n, False)

increasing = "increasing"
weakening = "weakening"
successorExists = "successorExists"
transitivity = "transitivity"
reflexivity = "reflexivity"
main = natural.byInduction(ge_zero)

starting_claim = enriched.And([ natural.increasing.addMark(increasing)
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

s = enriched.And([starting_claim, natural.exists_five])

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


