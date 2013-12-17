# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import formula, constructors, endofunctor
from calculus.basic import formula as basicFormula
from lib.common_symbols import leftSymbol, rightSymbol, relationSymbol, domainSymbol, inputSymbol, outputSymbol, functionPairsSymbol
from lib import common_vars
from calculus import variable

def IsEquivalence(e):
  return constructors.Always(constructors.Holds(e, common_vars.equivalence))

def Maps(a, b, f):
  return constructors.Always(constructors.Holds(
      variable.ProductVariable([ (inputSymbol, a)
                               , (outputSymbol, b)]),
      variable.ApplySymbolVariable(f, functionPairsSymbol)))

def IsFunction(f):
  return constructors.Always(constructors.Holds(f, common_vars.function))

InDomain = formula.InDomain
Equal = formula.Equal

Identical = formula.Identical

def InductionBase(var, claim):
  return claim.substituteVariable(var, common_vars.zero)

def InductionStep(var, claim):
  newVar = var.relatedVariable()
  return constructors.Forall([constructors.BoundedVariableBinding(newVar, common_vars.natural)],
      constructors.Implies([claim.substituteVariable(var, newVar)],
        claim.updateVariables().substituteVariable(var, variable.ApplySymbolVariable(newVar, common_vars.S))))

def InductionHypotheses(var, claim):
  return constructors.And([InductionBase(var, claim), InductionStep(var, claim)])

def InductionConclusion(var, claim):
  newVar = var.relatedVariable()
  return constructors.Forall([constructors.BoundedVariableBinding(newVar, common_vars.natural)],
      claim.substituteVariable(var, newVar))

def Induction(var, claim):
  return constructors.Implies([InductionBase(var, claim), InductionStep(var, claim)],
      InductionConclusion(var, claim))

def _forwardImportInduction(x, var, claim):
  hypotheses = InductionHypotheses(var, claim)
  conclusion = InductionConclusion(var, claim)
  return constructors.assume(x, hypotheses).forwardFollow(lambda x:
      formula.Arrow(src = x,
        tgt = constructors.Not(
          constructors.And([hypotheses, constructors.Not(constructors.And([conclusion, x]))])),
        basicArrow = x.translate().forwardOnNotFollow(lambda x:
          x.backwardOnRightFollow(lambda x:
            x.backwardOnNotFollow(lambda x:
              x.forwardOnLeftFollow(lambda x:
                basicFormula.Induction(src = x, tgt = conclusion.translate())))))))

def forwardImportInductionAndContradict(x, var, claim):
  assert(x.__class__ == formula.Exists)
  hypotheses = InductionHypotheses(var, claim)
  conclusion = InductionConclusion(var, claim)
  return constructors.assume(x.updateVariables(), hypotheses).forwardFollow(lambda x:
      formula.Arrow(src = x.updateVariables(), tgt = constructors.Not(hypotheses),
        basicArrow = x.translate().forwardOnNotFollow(lambda x:
          x.backwardOnRightFollow(lambda x:
            x.backwardOnNotFollow(lambda x:
              x.forwardOnLeftFollow(lambda x:
                basicFormula.Induction(src = x, tgt = conclusion.translate())).forwardFollow(lambda x:
                  x.forwardCommute().forwardFollow(lambda x:
                    x.forwardOnLeftFollow(lambda x:
                      x.forwardOnBodyFollow(lambda x:
                        x.forwardOnRightFollow(lambda x:
                          x.forwardDoubleDual())))).forwardFollow(lambda x:
                            x.forwardContradict())))).backwardFollow(lambda x:
                              x.backwardOnRightFollow(lambda x:
                                basicFormula.trueIsNotFalse).backwardFollow(lambda x:
                                  x.backwardIntroUnitLeft())))))

def forwardInductionOnIExists(x, i):
  var = x.bindings[i].variable
  claim = constructors.Not(x.value)
  a = x.forwardPushAndSplit(i)
  a = a.forwardFollow(lambda x:
      endofunctor.Exists(x.bindings).onArrow(forwardImportInductionAndContradict(x.value, var, claim)))
  return a

