# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from extraction.python.lib import oldNatural as naturalRep
from calculus import enriched
from lib import oldNatural as natural
from mark import common as marks

from path import Path

import about
import importables

def ge_zero(n):
  return natural.Compare(natural.zero, n, False)

increasing = "increasing"
weakening = "weakening"
successorExists = "successorExists"
transitivity = "transitivity"
reflexivity = "reflexivity"
main = natural.byInduction(ge_zero)

starting_claim = enriched.And([ natural.increasing
                              , main.addMark(marks.selection)
                              , natural.successorExists
                              , natural.transitivity
                              , natural.weakening
                              , natural.reflexivity
                              , natural.zero_natural ])

arrow = starting_claim.forwardImportToClause(2, 1, 1)

arrow = arrow.forwardFollow(lambda claim:
    claim.forwardOnIthFollow(1, lambda x:
      x.forwardOnIthFollow(1, lambda x:
        x.forwardConjQuantifier(0))))

arrow = arrow.forwardFollow(lambda x:
    x.forwardHeavyClean())

arrow = arrow.forwardFollow(lambda x:
    importables.beginImportingOnIthFollow(x, 1, lambda x:
      importables.continueImportingOnOnIthFollow(x, 1, lambda q:
        importables.continueImportingOnBodyFollow(q, lambda x:
          importables.finishImporting(x,
            about.about(q.variables(), 1)))))).forwardFollow(lambda x:
              x.forwardHeavyClean())

arrow = arrow.forwardFollow(lambda x:
    importables.beginImportingOnIthFollow(x, 1, lambda x:
      importables.continueImportingOnOnIthFollow(x, 1, lambda q:
        importables.continueImportingOnBodyFollow(q, lambda x:
          importables.finishImporting(x, about.about(q.variables(), 0)))))).forwardFollow(lambda x:
              x.forwardClean())

def zero_and(rest):
  res = [natural.zero]
  res.extend(rest)
  return res

arrow = arrow.forwardFollow(lambda x:
    importables.beginImportingOnIthFollow(x, 0, lambda x:
      importables.continueImportingOnOnIthFollow(x, 1, lambda q:
        importables.continueImportingOnBodyFollow(q, lambda x:
          importables.finishImporting(x,
            about.about(zero_and(q.variables()), 0)))))).forwardFollow(lambda x:
              x.forwardClean())

arrow = arrow.forwardFollow(lambda x:
    x.forwardOnIthFollow(0, lambda x:
      x.forwardOnIthFollow(0, lambda x:
        x.forwardSingleton(enriched.andType))))

arrow = arrow.forwardFollow(lambda x:
    importables.beginImportingOnIthFollow(x, 0, lambda x:
      importables.continueImportingOnOnIthFollow(x, 0, lambda x:
        importables.finishImporting(x, about.about([natural.zero], 0))))).forwardFollow(lambda x:
            x.forwardClean())

arrow = arrow.forwardFollow(lambda x:
    importables.beginImportingOnIthFollow(x, 0, lambda x:
      importables.continueImportingOnOnIthFollow(x, 0, lambda q:
        importables.continueImportingOnBodyFollow(q, lambda x:
          importables.finishImporting(x,
            about.about(zero_and(q.variables()[1:]), 0)))))).forwardFollow(lambda x:
              x.forwardClean())

arrow = arrow.forwardFollow(lambda x:
    importables.beginImportingOnIthFollow(x, 0, lambda x:
      importables.continueImportingOnOnIthFollow(x, 0, lambda q:
        importables.continueImportingOnBodyFollow(q, lambda x:
          importables.finishImporting(x, about.about(q.variables()[1:], 0)))))).forwardFollow(lambda x:
              x.forwardHeavyClean())

arrow = arrow.forwardFollow(lambda x:
    x.forwardUnsingleton())

# Now wrap the preceeding arrow into a arrow that concludes that 5 is at least 0.

s = enriched.And([starting_claim, natural.exists_five])

t = s.forwardOnIthFollow(0, lambda x: arrow)
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

e = t.tgt()
ending_claim = e


