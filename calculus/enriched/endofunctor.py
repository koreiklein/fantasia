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
  def covariant(self):
    raise Exception("Abstract superclass.")
  def onObject(self, object):
    return formula.Application(endofunctor = self, formula = object)
  def onArrow(self, arrow):
    basicArrow = self.translate().onArrow(arrow)
    if self.covariant():
      src = self.onObject(arrow.src)
      tgt = self.onObject(arrow.tgt)
    else:
      src = self.onObject(arrow.tgt)
      tgt = self.onObject(arrow.src)
    return formula.Arrow(src = src, tgt = tgt, basicArrow = basicArrow)

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

  def covariant(self):
    return True

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
  def covariant(self):
    return self.basicEndofunctor.covariant()

always_functor = DirectTranslate(basic.always_functor)
not_functor = DirectTranslate(basic.not_functor)
identity_functor = DirectTranslate(basic.identity_functor)

class Conjunction(Endofunctor):
  def __init__(self, values, index):
    self.values = values
    self.index = index
    self.first = values[:index]
    self.rest = values[index:]

  def covariant(self):
    return True

  def onObject(self, object):
    newValues = list(self.values)
    newValues.insert(self.index, object)
    return self.multiOp()(newValues)

  def translate(self):
    # e.g.
    # self.values = [a, b, c, d]
    # self.index = 2
    # self.rest = [c, d]
    # self.first = [a, b]
    # [a, b, ., c, d] -> a|(b|(.|(c|(d|1))))
    back = self.multiOp()(self.rest).translate()
    result = self.basicEndofunctor()(side = left, other = back)
    for value in self.first[::-1]:
      result = result.compose(basicEndofunctor()(side = right, other = value.translate()))
    return result

class And(Endofunctor):
  def basicEndofunctor(self):
    return basicEndofunctor.And
  def multiOp(self):
    return formula.And

class Or(Endofunctor):
  def basicEndofunctor(self):
    return basicEndofunctor.Or
  def multiOp(self):
    return formula.Or

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

  def covariant(self):
    return True
  def translate(self):
    return self.expanded

