# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from lib import equivalence, common_vars, common_symbols, library
from calculus import symbol, variable
from calculus.enriched import constructors
from lib.common_formulas import Maps, IsEquivalence, IsFunction, Equal
from lib import common_vars

def projectSrc(f):
  return variable.ApplySymbolVariable(f, common_symbols.srcSymbol)
def projectTgt(f):
  return variable.ApplySymbolVariable(f, common_symbols.tgtSymbol)
def projectDomain(e):
  return variable.ApplySymbolVariable(e, common_symbols.domainSymbol)
def projectRelation(e):
  return variable.ApplySymbolVariable(e, common_symbols.relationSymbol)

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
        predicates = [ Maps(a, b, f)
                     , Maps(aprime, bprime, f)
                     , Equal(a, aprime, projectSrc(f))],
        consequent = Equal(b, bprime, projectTgt(f))))

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
        predicates =[ Maps(a, b, f)
                    , Maps(aprime, bprime, f)
                    , Equal(b, bprime, projectSrc(f))],
        consequent = Equal(a, aprime, projectTgt(f))))

A = common_vars.A()
claim = constructors.Forall([constructors.OrdinaryVariableBinding(A)],
    constructors.Iff(
      right = constructors.And([ IsEquivalence(projectSrc(A))
                              , IsEquivalence(projectTgt(A))
                              , defined(A)
                              , wellDefined(A)
                              , unique(A)]),
      left = IsFunction(A)))

lib = library.Library(
    name = "F",
    claims = [claim],
    variables = [common_vars.function],
    sub_libraries = [equivalence.lib])

