# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from lib import equivalence, common_vars, common_symbols, library
from calculus import symbol, variable
from calculus.enriched import constructors
from lib.common_symbols import leftSymbol, rightSymbol, relationSymbol

function = variable.StringVariable('function')

def IsEquivalence(e):
  return constructors.Holds(e, equivalence.equivalence)

def Maps(a, b, f):
  return constructors.Holds(
      variable.ProductVariable([ (common_symbols.inputSymbol, a)
                                   , (common_symbols.outputSymbol, b)]),
      variable.ProjectionVariable(f, common_symbols.functionPairsSymbol))

def projectSrc(f):
  return variable.ProjectionVariable(f, common_symbols.srcSymbol)
def projectTgt(f):
  return variable.ProjectionVariable(f, common_symbols.tgtSymbol)
def projectDomain(e):
  return variable.ProjectionVariable(e, common_symbols.domainSymbol)
def projectRelation(e):
  return variable.ProjectionVariable(e, common_symbols.relationSymbol)

def EqualUnder(a, b, e):
  return constructors.Holds(
      variable.ProductVariable([(leftSymbol, a), (rightSymbol, b)]),
      variable.ProjectionVariable(e, relationSymbol))

a = common_vars.a()
b = common_vars.b()
def defined(f):
  return constructors.Forall([constructors.BoundedVariableBinding(a, projectSrc(f))],
      constructors.Exists([constructors.BoundedVariableBinding(b, projectTgt(f))],
        Maps(a, b, f)))

a = common_vars.a()
b = common_vars.b()
aprime = common_vars.aprime()
bprime = common_vars.bprime()
def wellDefined(f):
  return constructors.Forall(
      [ constructors.BoundedVariableBinding(a, projectSrc(f))
      , constructors.BoundedVariableBinding(aprime, projectSrc(f))
      , constructors.BoundedVariableBinding(b, projectTgt(f))
      , constructors.BoundedVariableBinding(bprime, projectTgt(f))],
      constructors.Implies(
        predicate = constructors.And([ Maps(a, b, f)
                                     , Maps(aprime, bprime, f)
                                     , EqualUnder(a, aprime, projectSrc(f))]),
        consequent = EqualUnder(b, bprime, projectTgt(f))))

a = common_vars.a()
b = common_vars.b()
aprime = common_vars.aprime()
bprime = common_vars.bprime()
def unique(f):
  return constructors.Forall(
      [ constructors.BoundedVariableBinding(a, projectSrc(f))
      , constructors.BoundedVariableBinding(aprime, projectSrc(f))
      , constructors.BoundedVariableBinding(b, projectTgt(f))
      , constructors.BoundedVariableBinding(bprime, projectTgt(f))],
      constructors.Implies(
        predicate = constructors.And([ Maps(a, b, f)
                                     , Maps(aprime, bprime, f)
                                     , EqualUnder(b, bprime, projectSrc(f))]),
        consequent = EqualUnder(a, aprime, projectTgt(f))))

def IsFunction(f):
  return constructors.Holds(f, function)

A = common_vars.A()
claim = constructors.Forall([constructors.OrdinaryVariableBinding(A)],
    constructors.Iff(
      left = constructors.And([ IsEquivalence(projectSrc(A))
                              , IsEquivalence(projectTgt(A))
                              , defined(A)
                              , wellDefined(A)
                              , unique(A)]),
      right = IsFunction(A)))

lib = library.Library(
    claims = [ constructors.Hidden(claim, "Function") ],
    variables = [function],
    sub_libraries = [equivalence.lib])

