# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from misc import *
import misc
from calculus.variable import ApplySymbolVariable, ProductVariable, StringVariable, Variable
from calculus.enriched import formula as formula
from calculus.basic import formula as basicFormula
from calculus.basic import endofunctor as basicEndofunctor
from calculus.basic import bifunctor as basicBifunctor
from lib import common_symbols
from lib.common_symbols import leftSymbol, rightSymbol, relationSymbol, domainSymbol

from ui.render.gl import primitives, colors, distances
from ui.stack import gl
from ui.stack import stack

def Maps(a, b, f):
  return basicFormula.Holds(
      ProductVariable([ (common_symbols.inputSymbol, a)
                               , (common_symbols.outputSymbol, b)]),
      ApplySymbolVariable(f, common_symbols.functionPairsSymbol))

class Endofunctor:
  # return a basic endofunctor
  def translate(self):
    raise Exception("Abstract superclass.")
  def covariant(self):
    raise Exception("Abstract superclass.")

  def is_and_functor(self):
    return False

  def updateVariables(self):
    raise Exception("Abstract superclass.")

  # self must not be the identity functor.
  # return a pair of endofunctors (a, b) such that a.compose(b) == self, a is non-trivial
  # and a is "as small as possible".
  def factor_left(self):
    return (self, identity_functor)

  # self must not be the identity functor.
  # return a pair of endofunctors (a, b) such that a.compose(b) == self, b is non-trivial
  # and b is "as small as possible".
  def factor_right(self):
    return (identity_functor, self)

  def onArrow(self, arrow):
    if self.is_identity():
      return arrow
    else:
      basicArrow = self.translate().onArrow(arrow)
      if self.covariant():
        src = self.onObject(arrow.src)
        tgt = self.onObject(arrow.tgt)
      else:
        src = self.onObject(arrow.tgt)
        tgt = self.onObject(arrow.src)
      return formula.Arrow(src = src, tgt = tgt, basicArrow = basicArrow)

  def compose(self, other):
    return Composite(self, other)

  def is_identity(self):
    return is_identity_functor(self)

class Composite(Endofunctor):
  def __init__(self, left, right):
    self.left = left
    self.right = right

  def onObject(self, object):
    return self.right.onObject(self.left.onObject(object))

  def onArrow(self, arrow):
    return self.right.onArrow(self.left.onArrow(arrow))

  def __repr__(self):
    return "%s o\n%s"%(self.left, self.right)

  def is_and_functor(self):
    return self.right.is_and_functor()

  def factor_left(self):
    if is_identity_functor(self.right):
      return self.left.factor_left()
    elif is_identity_functor(self.left):
      return self.right.factor_left()
    else:
      a, b = self.left.factor_left()
      return (a, b.compose(self.right))

  def factor_right(self):
    if is_identity_functor(self.right):
      return self.left.factor_right()
    elif is_identity_functor(self.left):
      return self.right.factor_right()
    else:
      a, b = self.right.factor_right()
      return (self.left.compose(a), b)

  def translate(self):
    return self.left.translate().compose(self.right.translate())
  def covariant(self):
    if self.left.covariant():
      return self.right.covariant()
    else:
      return not self.right.covariant()

class VariableBinding:
  # return: an endofunctor representing existential quantification
  #         over this variable.
  def translate(self):
    raise Exception("Abstract superclass.")
  def render(self, context):
    return gl.newTextualGLStack(colors.variableColor, repr(self))

class BoundedVariableBinding(VariableBinding):
  def __init__(self, variable, relation):
    self.variable = variable
    self.relation = relation
    self.domain = ApplySymbolVariable(self.relation, common_symbols.domainSymbol)

  def translate(self):
    return basicEndofunctor.Exists(self.variable).compose(
        basicEndofunctor.And(side = right,
          other = basicFormula.Holds(held = self.variable,
            holding = self.domain)))

  def render(self, context):
    return (renderBoundedVariableBinding(self.variable, self.domain), context)

def renderBoundedVariableBinding(variable, domain):
  middleStack = gl.newTextualGLStack(colors.variableColor, ":")
  return variable.render({}).stack(0, middleStack,
      spacing = distances.variable_binding_spacing).stackCentered(0, domain.render({}),
          spacing = distances.variable_binding_spacing)

class OrdinaryVariableBinding(VariableBinding):
  def __init__(self, variable):
    self.variable = variable

  def __repr__(self):
    return repr(self.variable)

  def translate(self):
    return basicEndofunctor.Exists(self.variable)

  def render(self, context):
    return (self.variable.render(), context)

class WelldefinedVariableBinding(VariableBinding):
  # variable: a variable
  # relation: an equivalence relation
  def __init__(self, variable, relation):
    self.variable = variable
    self.relation = relation

  def __repr__(self):
    return "%s wd in %s"%(self.variable, self.relation)

  def translate(self):
    result = basicEndofunctor.Exists(self.variable)
    newVariable = variable.Variable()
    result = formula.ExpandWellDefined(self.variable, newVariable, self.relation).compose(result)
    return result

  def render(self, context):
    # TODO Render in a clearer way.
    return (self.variable.render(), context)

class Exists(Endofunctor):
  def __init__(self, bindings):
    self.bindings = bindings

  def __repr__(self):
    return "Exists%s"%(self.bindings,)

  def onObject(self, object):
    return formula.Exists(bindings = self.bindings, value = object)

  def covariant(self):
    return True

  def translate(self):
    result = basicEndofunctor.identity_functor
    for binding in self.bindings[::-1]:
      result = result.compose(binding.translate())
    return result

class DirectTranslate(Endofunctor):
  def __init__(self, basicEndofunctor, _onObject):
    self.basicEndofunctor = basicEndofunctor
    self._onObject = _onObject
  def __repr__(self):
    return "direct(%s)"%(self.basicEndofunctor,)
  def translate(self):
    return self.basicEndofunctor
  def covariant(self):
    return self.basicEndofunctor.covariant()
  def onObject(self, object):
    return self._onObject(object)
  def factor_left(self):
    if is_identity_functor(self):
      raise Exception("Can't factor the identity functor.")
    else:
      return (self, identity_functor)
  def factor_right(self):
    if is_identity_functor(self):
      raise Exception("Can't factor the identity functor.")
    else:
      return (identity_functor, self)

  def updateVariables(self):
    return self

always_functor = DirectTranslate(basicEndofunctor.always_functor,
    _onObject = formula.Always)
not_functor = DirectTranslate(basicEndofunctor.not_functor,
    _onObject = formula.Not)
identity_functor = DirectTranslate(basicEndofunctor.identity_functor,
    _onObject = lambda x: x)

def is_identity_functor(f):
  return f.__class__ == DirectTranslate and f.basicEndofunctor.__class__ == basicEndofunctor.Id

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
    if len(self.rest) > 0:
      back = self.multiOp()(self.rest).translate()
      result = self.basicEndofunctor()(side = left, other = back)
    else:
      result = basicEndofunctor.identity_functor
    for value in self.first[::-1]:
      result = result.compose(self.basicEndofunctor()(side = right, other = value.translate()))
    return result

class And(Conjunction):
  def is_and_functor(self):
    return True

  def basicEndofunctor(self):
    return basicEndofunctor.And
  def multiOp(self):
    return formula.And

class Or(Conjunction):
  def basicEndofunctor(self):
    return basicEndofunctor.Or
  def multiOp(self):
    return formula.Or

class WellDefinedFunctor(Endofunctor):
  def __init__(self, variable, newVariable, equivalence):
    self.variable = variable
    self.newVariable = newVariable
    self.equivalence = equivalence
    self.expanded = formula.ExpandWellDefined(variable, newVariable, equivalence)

  def onObject(self, object):
    return formula.WellDefined(
        variable = self.variable,
        newVariable = self.newVariable,
        equivalence = self.equivalence,
        value = object)

  def covariant(self):
    return True
  def translate(self):
    return self.expanded
