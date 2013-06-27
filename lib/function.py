# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from lib import equivalence, common_vars, common_symbols, library
from calculus import symbol, basic
from calculus.basic import formula

function = basic.StringVariable('function')

def Maps(a, b, f):
  return formula.Holds(
      basic.ProductVariable([ (common_symbols.inputSymbol, a)
                                   , (common_symbols.outputSymbol, b)]),
      basic.ProjectionVariable(f, common_symbols.functionPairsSymbol))

def projectSrc(f):
  return basic.ProjectionVariable(f, common_symbols.srcSymbol)
def projectTgt(f):
  return basic.ProjectionVariable(f, common_symbols.tgtSymbol)
def projectDomain(e):
  return basic.ProjectionVariable(e, common_symbols.domainSymbol)
def projectRelation(e):
  return basic.ProjectionVariable(e, common_symbols.relationSymbol)

a = common_vars.a()
b = common_vars.b()
def defined(f):
  return formula.MultiBoundedForall([(a, projectSrc(f))],
      formula.MultiBoundedExists([(b, projectTgt(f))],
        Maps(a, b, f)))

a = common_vars.a()
b = common_vars.b()
aprime = common_vars.aprime()
bprime = common_vars.bprime()
def wellDefined(f):
  return formula.MultiBoundedForall(
      [ (a, projectSrc(f))
      , (aprime, projectSrc(f))
      , (b, projectTgt(f))
      , (bprime, projectTgt(f))],
      formula.Implies(
        predicate = formula.MultiAnd([ Maps(a, b, f)
                                   , Maps(aprime, bprime, f)
                                   , equivalence.EqualUnder(a, aprime, projectSrc(f))]),
        consequent = equivalence.EqualUnder(b, bprime, projectTgt(f))))

a = common_vars.a()
b = common_vars.b()
aprime = common_vars.aprime()
bprime = common_vars.bprime()
def unique(f):
  return formula.MultiBoundedForall(
      [ (a, projectSrc(f))
      , (aprime, projectSrc(f))
      , (b, projectTgt(f))
      , (bprime, projectTgt(f))],
      formula.Implies(
        predicate = formula.MultiAnd([ Maps(a, b, f)
                                   , Maps(aprime, bprime, f)
                                   , equivalence.EqualUnder(b, bprime, projectSrc(f))]),
        consequent = equivalence.EqualUnder(a, aprime, projectTgt(f))))

def IsFunction(f):
  return formula.Holds(f, function)

A = common_vars.A()
claim = formula.MultiForall([A],
    formula.Iff(
      left = formula.MultiAnd([ equivalence.IsEquivalence(projectSrc(A))
                            , equivalence.IsEquivalence(projectTgt(A))
                            , defined(A)
                            , wellDefined(A)
                            , unique(A)]),
      right = IsFunction(A)))

lib = library.Library(
    claims = [ formula.Hidden(claim, "Function")
               #claim
             #, equivalence.claim
             , formula.Hidden(equivalence.claim, "Equivalence")
    ],
    variables = [equivalence.equivalence, function])

