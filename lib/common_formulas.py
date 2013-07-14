# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import formula, constructors, endofunctor
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

def InductionBase(var, claim):
  return claim.substituteVariable(var, common_vars.zero)

def InductionStep(var, claim):
  newVar = var.relatedVariable()
  return constructors.Forall([constructors.BoundedVariableBinding(newVar, common_vars.natural)],
      constructors.Implies([claim.substituteVariable(var, newVar)],
        claim.substituteVariable(var, variable.ApplySymbolVariable(newVar, common_vars.S))))

def InductionHypotheses(var, claim):
  return constructors.And([InductionBase(var, claim), InductionStep(var, claim)])

def InductionConclusion(var, claim):
  newVar = var.relatedVariable()
  return constructors.Forall([constructors.BoundedVariableBinding(newVar, common_vars.natural)],
      claim.substituteVariable(var, newVar))

def Induction(var, claim):
  return constructors.Implies([InductionBase(var, claim), InductionStep(var, claim)],
      InductionConclusion(var, claim))

def forwardInduction(x, var, claim):
  assert(x.__class__ == formula.And)
  assert(len(x.values) == 2)
  assert(x.values[0] == common_formulas.InductionBase(var, claim))
  assert(x.values[1] == common_formulas.InductionStep(var, claim))
  conclusion = common_formulas.InductionConclusion(var, claim)
  return Arrow(src = x, tgt = conclusion,
      basicArrow = basicFormula.Induction(src = x.translate(),
        tgt = conclusion.translate()))

def backwardInduction(x):
  assert(x.__class__ == formula.Exists)
  assert(len(x.bindings) == 1)
  binding = x.bindings[0]
  binding.assertBoundedNatural()
  var = binding.variable
  claim = x.value
  hypotheses = common_formulas.InductionHypotheses(var, claim)
  return Arrow(src = hypotheses, tgt = x,
      basicArrow = basicFormula.Induction(src = hypothesis.translate(), tgt = x.translate()))

