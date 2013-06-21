# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from misc import *
from calculus import variable
from calculus.enriched import formula as formula
from calculus.basic import formula as basicFormula
from calculus.basic import endofunctor as basic
from calculus.basic import bifunctor as basicBifunctor
from lib.equivalence import InDomain, EqualUnder

class Endofunctor:
  # return a basic endofunctor
  def translate(self):
    raise Exception("Abstract superclass.")
  def onObject(self, object):
    return formula.Application(endofunctor = self, formula = object)

class VariableBinding:
  # variable: a variable
  # welldefined: an equivalence relation or None
  def __init__(self, variable, welldefined):
    self.variable = variable
    self.welldefined = welldefined

  def translate(self):
    result = basic.Exists(self.variable)
    if self.welldefined is not None:
      newVariable = variable.Variable()
      result = WellDefined(self.variable, newVariable, self.welldefined).compose(result)
    return result

class Exists(Endofunctor):
  def __init__(self, bindings):
    self.bindings = bindings

  def translate(self):
    result = basic.identity_functor
    for binding in self.bindings[::-1]:
      result = result.compose(bindings.translate())
    return result

class DirectTranslate(Endofunctor):
  def __init__(self, basicEndofunctor):
    self.basicEndofunctor = basicEndofunctor
  def translate(self):
    return self.basicEndofunctor

always_functor = DirectTranslate(basic.always_functor)
not_functor = DirectTranslate(basic.not_functor)
identity_functor = DirectTranslate(basic.identity_functor)

def ExpandWellDefined(variable, newVariable, equivalence):
  isEqual = basicFormula.And(
        basicFormula.Always(InDomain(newVariable, equivalence)),
        basicFormula.Always(EqualUnder(newVariable, variable, equivalence)))
  F = basic.SubstituteVariable(variable, newVariable).compose(
      basic.not_functor.compose(
        basic.Exists(newVariable)).compose(
          basic.And(side = right, other = isEqual)).compose(
            basic.not_functor))
  return basicBifunctor.and_functor.precomposeRight(F).join()

def Not(x):
  return formula.Application(not_functor, x)
def Always(x):
  return formula.Application(always_functor, x)

def WelldefinedObject(variable, newVariable, equivalence, value):
  return formula.Application(WellDefined(variable, newVariable, equivalence), value)

class WellDefinedFunctor(Endofunctor):
  def __init__(self, variable, newVariable, equivalence):
    self.variable = variable
    self.newVariable = newVariable
    self.equivalence = equivalence
    self.expanded = ExpandWellDefined(variable, newVariable, equivalence)

  def translate(self):
    return self.expanded

