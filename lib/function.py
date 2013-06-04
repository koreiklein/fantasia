# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from lib import equivalence, common_vars, common_symbols, library
from calculus import symbol, basic

function = basic.StringVariable('function')

def Maps(a, b, f):
  return basic.Holds(
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
  return basic.MultiBoundedForall([(a, projectSrc(f))],
      basic.MultiBoundedExists([(b, projectTgt(f))],
        Maps(a, b, f)))

a = common_vars.a()
b = common_vars.b()
aprime = common_vars.aprime()
bprime = common_vars.bprime()
def wellDefined(f):
  return basic.MultiBoundedForall(
      [ (a, projectSrc(f))
      , (aprime, projectSrc(f))
      , (b, projectTgt(f))
      , (bprime, projectTgt(f))],
      basic.Implies(
        predicate = basic.MultiAnd([ Maps(a, b, f)
                                   , Maps(aprime, bprime, f)
                                   , equivalence.EqualUnder(a, aprime, projectSrc(f))]),
        consequent = equivalence.EqualUnder(b, bprime, projectTgt(f))))

a = common_vars.a()
b = common_vars.b()
aprime = common_vars.aprime()
bprime = common_vars.bprime()
def unique(f):
  return basic.MultiBoundedForall(
      [ (a, projectSrc(f))
      , (aprime, projectSrc(f))
      , (b, projectTgt(f))
      , (bprime, projectTgt(f))],
      basic.Implies(
        predicate = basic.MultiAnd([ Maps(a, b, f)
                                   , Maps(aprime, bprime, f)
                                   , equivalence.EqualUnder(b, bprime, projectSrc(f))]),
        consequent = equivalence.EqualUnder(a, aprime, projectTgt(f))))

def IsFunction(f):
  return basic.Holds(f, function)

A = common_vars.A()
claim = basic.MultiForall([A],
    basic.Iff(
      left = basic.MultiAnd([ equivalence.IsEquivalence(projectSrc(A))
                            , equivalence.IsEquivalence(projectTgt(A))
                            , defined(A)
                            , wellDefined(A)
                            , unique(A)]),
      right = IsFunction(A)))

equivalencelib = library.Library(claims = [claim], variables = [equivalence])

lib = library.Library(
    claims = [ basic.Hidden(claim, "Function")
               #claim
             #, equivalence.claim
             , basic.Hidden(equivalence.claim, "Equivalence")
    ],
    variables = [equivalence.equivalence, function])

