# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from lib import equivalence, common_vars, common_symbols, library
from calculus import symbol, enriched

function = enriched.StringVariable('function')

def Maps(a, b, f):
  return enriched.Holds(
      enriched.ProductVariable([ (common_symbols.inputSymbol, a)
                                   , (common_symbols.outputSymbol, b)]),
      enriched.ProjectionVariable(f, common_symbols.functionPairsSymbol))

def projectSrc(f):
  return enriched.ProjectionVariable(f, common_symbols.srcSymbol)
def projectTgt(f):
  return enriched.ProjectionVariable(f, common_symbols.tgtSymbol)
def projectDomain(e):
  return enriched.ProjectionVariable(e, common_symbols.domainSymbol)
def projectRelation(e):
  return enriched.ProjectionVariable(e, common_symbols.relationSymbol)

a = common_vars.a()
b = common_vars.b()
def defined(f):
  return enriched.Forall([(a, projectSrc(f))],
      enriched.Exists([(b, projectTgt(f))],
        Maps(a, b, f)))

a = common_vars.a()
b = common_vars.b()
aprime = common_vars.aprime()
bprime = common_vars.bprime()
def wellDefined(f):
  return enriched.Forall(
      [ (a, projectSrc(f))
      , (aprime, projectSrc(f))
      , (b, projectTgt(f))
      , (bprime, projectTgt(f))],
      enriched.Implies(
        predicate = enriched.And([ Maps(a, b, f)
                                     , Maps(aprime, bprime, f)
                                     , equivalence.EqualUnder(a, aprime, projectSrc(f))]),
        consequent = equivalence.EqualUnder(b, bprime, projectTgt(f))))

a = common_vars.a()
b = common_vars.b()
aprime = common_vars.aprime()
bprime = common_vars.bprime()
def unique(f):
  return enriched.Forall(
      [ (a, projectSrc(f))
      , (aprime, projectSrc(f))
      , (b, projectTgt(f))
      , (bprime, projectTgt(f))],
      enriched.Implies(
        predicate = enriched.And([ Maps(a, b, f)
                                     , Maps(aprime, bprime, f)
                                     , equivalence.EqualUnder(b, bprime, projectSrc(f))]),
        consequent = equivalence.EqualUnder(a, aprime, projectTgt(f))))

def IsFunction(f):
  return enriched.Holds(f, function)

A = common_vars.A()
claim = enriched.BasicForall([A],
    enriched.Iff(
      left = enriched.And([ equivalence.IsEquivalence(projectSrc(A))
                              , equivalence.IsEquivalence(projectTgt(A))
                              , defined(A)
                              , wellDefined(A)
                              , unique(A)]),
      right = IsFunction(A)))

equivalencelib = library.Library(claims = [claim], variables = [equivalence])

lib = library.Library(
    claims = [ enriched.Hidden(claim, "Function")
               #claim
             #, equivalence.claim
             , enriched.Hidden(equivalence.claim, "Equivalence")
    ],
    variables = [equivalence.equivalence, function])

