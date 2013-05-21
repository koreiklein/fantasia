# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from lib import equivalence, common_vars, common_symbols, library
from calculus import symbol, constructors

function = constructors.StringVariable('function')

def Maps(a, b, f):
  return constructors.Holds(
      constructors.VariableProduct([ (common_symbols.inputSymbol, a)
                                   , (common_symbols.outputSymbol, b)]),
      constructors.VariableProject(f, common_symbols.functionPairsSymbol))

def projectSrc(f):
  return constructors.VariableProject(f, common_symbols.srcSymbol)
def projectTgt(f):
  return constructors.VariableProject(f, common_symbols.tgtSymbol)
def projectDomain(e):
  return constructors.VariableProject(e, common_symbols.domainSymbol)
def projectRelation(e):
  return constructors.VariableProject(e, common_symbols.relationSymbol)


a = common_vars.a()
b = common_vars.b()
def defined(f):
  return constructors.BoundedForall([(a, projectSrc(f))],
      constructors.BoundedExists([(b, projectTgt(f))],
        Maps(a, b, f)))

a = common_vars.a()
b = common_vars.b()
aprime = common_vars.aprime()
bprime = common_vars.bprime()
def wellDefined(f):
  return constructors.BoundedForall(
      [ (a, projectSrc(f))
      , (aprime, projectSrc(f))
      , (b, projectTgt(f))
      , (bprime, projectTgt(f))],
      constructors.Implies(
        predicate = constructors.And([ Maps(a, b, f)
                                     , Maps(aprime, bprime, f)
                                     , equivalence.EqualUnder(a, aprime, projectSrc(f))]),
        consequent = equivalence.EqualUnder(b, bprime, projectTgt(f))))

a = common_vars.a()
b = common_vars.b()
aprime = common_vars.aprime()
bprime = common_vars.bprime()
def unique(f):
  return constructors.BoundedForall(
      [ (a, projectSrc(f))
      , (aprime, projectSrc(f))
      , (b, projectTgt(f))
      , (bprime, projectTgt(f))],
      constructors.Implies(
        predicate = constructors.And([ Maps(a, b, f)
                                     , Maps(aprime, bprime, f)
                                     , equivalence.EqualUnder(b, bprime, projectSrc(f))]),
        consequent = equivalence.EqualUnder(a, aprime, projectTgt(f))))

def IsFunction(f):
  return constructors.Holds(f, function)

A = common_vars.A()
claim = constructors.Forall([A],
    constructors.Iff(
      left = constructors.And([ equivalence.IsEquivalence(projectSrc(A))
                              , equivalence.IsEquivalence(projectTgt(A))
                              , defined(A)
                              , wellDefined(A)
                              , unique(A)]),
      right = IsFunction(A)))

lib = library.Library(claims = [claim], variables = [function])

