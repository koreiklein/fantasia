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

  def renderOn(self, context, f):
    raise Exception("Abstract superclass.")

  def onObject(self, object):
    if self.is_identity():
      return object
    else:
      return formula.Application(endofunctor = self, formula = object)
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

  def renderOn(self, context, f):
    return self.right.renderOn(context, lambda context:
        self.left.renderOn(context, lambda context:
          f(context)))

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
    result = ExpandWellDefined(self.variable, newVariable, self.relation).compose(result)
    return result

  def render(self, context):
    # TODO Render in a clearer way.
    return (self.variable.render(), context)

class Exists(Endofunctor):
  def __init__(self, bindings):
    self.bindings = bindings

  def __repr__(self):
    return "Exists%s"%(self.bindings,)

  def renderOn(self, context, f):
    quantifierStackingDimension = _dimension_for_variance(context.covariant)
    variableStackingDimension = primitives._dual_dimension(quantifierStackingDimension)
    if len(self.bindings) == 0:
      variablesStack = gl.nullStack
    else:
      variablesStack, context = self.bindings[0].render(context)
      for binding in self.bindings[1:]:
        rendered_binding, context = binding.render(context)
        variablesStack = variablesStack.stack(variableStackingDimension,
            rendered_binding,
            spacing = distances.quantifier_variables_spacing)
    kid = f(context)
    divider = primitives.quantifierDivider(context.covariant,
        max(kid.widths()[variableStackingDimension],
          variablesStack.widths()[variableStackingDimension]))
    return variablesStack.stackCentered(quantifierStackingDimension, divider,
        spacing = distances.quantifier_before_divider_spacing).stackCentered(
        quantifierStackingDimension, kid,
        spacing = distances.quantifier_after_divider_spacing)

  def covariant(self):
    return True

  def translate(self):
    result = basicEndofunctor.identity_functor
    for binding in self.bindings[::-1]:
      result = result.compose(binding.translate())
    return result

class DirectTranslate(Endofunctor):
  def __init__(self, basicEndofunctor, _render):
    self.basicEndofunctor = basicEndofunctor
    self._render = _render
  def __repr__(self):
    return "direct(%s)"%(self.basicEndofunctor,)
  def translate(self):
    return self.basicEndofunctor
  def covariant(self):
    return self.basicEndofunctor.covariant()
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
  def renderOn(self, context, f):
    return self._render(context, f)
    return self._render(f(context), context)

  def updateVariables(self):
    return self

always_functor = DirectTranslate(basicEndofunctor.always_functor, lambda context, f:
    renderWithBackground(f(context),
      distances.exponential_border_width,
      colors.exponentialColor(context.covariant)))
not_functor = DirectTranslate(basicEndofunctor.not_functor, lambda context, f:
    f(context.negate()))
identity_functor = DirectTranslate(basicEndofunctor.identity_functor, lambda context, f:
    f(context))

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

  def renderOn(self, context, f):
    if context.covariant:
      dimension = 0
      other_dimension = 1
    else:
      dimension = 1
      other_dimension = 0

    length = distances.min_unit_divider_length
    values = []
    for kid in self.values:
      s = kid.render(context)
      length = max(length, s.widths()[other_dimension])
      values.append(s)
    inserted_kid = f(context)
    length = max(length, inserted_kid.widths()[other_dimension])
    values.insert(self.index, inserted_kid)
    return stack.stackAll(dimension,
        misc._interleave(self.renderDivider(context.covariant, length), values),
        spacing = distances.divider_spacing)

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
      result = result.compose(self.basicEndofunctor()(side = right, other = value.translate()))
    return result

class And(Conjunction):
  def is_and_functor(self):
    return True

  def basicEndofunctor(self):
    return basicEndofunctor.And
  def multiOp(self):
    return formula.And

  def renderDivider(self, covariant, length):
    return primitives.andDivider(covariant)(length)

class Or(Conjunction):
  def basicEndofunctor(self):
    return basicEndofunctor.Or
  def multiOp(self):
    return formula.Or

  def renderDivider(self, covariant, length):
    return primitives.orDivider(covariant)(length)

def ExpandWellDefined(variable, newVariable, equivalence):
  isEqual = basicFormula.And(
        basicFormula.Always(InDomain(newVariable, equivalence)),
        basicFormula.Always(Equal(newVariable, variable, equivalence)))
  F = basicEndofunctor.SubstituteVariable(variable, newVariable).compose(
      basicEndofunctor.not_functor.compose(
        basicEndofunctor.Exists(newVariable)).compose(
          basicEndofunctor.And(side = right, other = isEqual)).compose(
            basicEndofunctor.not_functor))
  return basicBifunctor.and_functor.precomposeRight(F).join()

def InDomain(a, e):
  return Always(formula.Holds(a, ApplySymbolVariable(e, domainSymbol)))

def Equal(a, b, e):
  return Always(formula.Holds(
      ProductVariable([(leftSymbol, a), (rightSymbol, b)]),
      ApplySymbolVariable(e, relationSymbol)))

def Not(x):
  return formula.Application(formula = x, endofunctor = not_functor)
def Always(x):
  return formula.Application(formula = x, endofunctor = always_functor)

def WelldefinedObject(variable, newVariable, equivalence, value):
  return formula.Application(formula = value,
      endofunctor = WellDefinedFunctor(variable, newVariable, equivalence))

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

  def renderOn(self, context, f):
    # TODO render this case more clearly?
    return f(context)

# x: an enriched formula
# index: an index
#   self must be equivalent to a b.onObject(a) where
#   b == And(...) or b == Or(...)
# return: a, b  or throw an exception if self is not of the appropriate form.
def factor_index(x, index):
  if x.__class__ == formula.Application:
    if x.endofunctor.is_identity():
      return factor_index(x.formula, index)
    else:
      a, b = x.endofunctor.factor_right()
      if b.__class__ == And or b.__class__ == Or:
        return (Application(formula = x.formula, endofunctor = a), b)
      else:
        raise Exception("The given endofunctor did not factor properly.")
  elif isinstance(x, formula.Conjunction):
    if x.__class__ == formula.And:
      F = And
    else:
      assert(x.__class__ == formula.Or)
      F = Or
    return (x.values[index],
        F(values = [x.values[i] for i in range(len(x.values)) if i != index],
          index = index))
  else:
    raise Exception("The given endofunctor did not factor properly.")

def renderWithBackground(s, border_width, color):
  widths = [x + 2 * border_width for x in s.widths()]
  widths[2] = 0.0
  return primitives.solidSquare(color, widths).stackCentered(2, s,
      spacing = distances.epsilon )

def _dimension_for_variance(covariant):
  if covariant:
    return 0
  else:
    return 1

