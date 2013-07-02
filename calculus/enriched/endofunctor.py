# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from misc import *
from calculus.variable import ProjectionVariable, ProductVariable, InjectionVariable, StringVariable, GeneralizedVariable
from calculus.enriched import formula as formula
from calculus.basic import formula as basicFormula
from calculus.basic import endofunctor as basic
from calculus.basic import bifunctor as basicBifunctor
from lib.equivalence import InDomain, EqualUnder
from lib import common_symbols

def Maps(a, b, f):
  return basicFormula.Holds(
      ProductVariable([ (common_symbols.inputSymbol, a)
                               , (common_symbols.outputSymbol, b)]),
      ProjectionVariable(f, common_symbols.functionPairsSymbol))

class Endofunctor:
  # return a basic endofunctor
  def translate(self):
    raise Exception("Abstract superclass.")
  def covariant(self):
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
    return (self, identity_functor)

  def renderOn(self, context, f):
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

  def compose(self, other):
    return Composite(self, other)

class Composite(Endofunctor):
  def __init__(self, left, right):
    self.left = left
    self.right = right

  def factor_left(self):
    if is_identity_functor(self.right):
      return self.left.factor()
    elif is_identity_functor(self.left):
      return self.right.factor()
    else:
      a, b = self.left.factor()
      return (a, b.compose(self.right))

  def factor_right(self):
    if is_identity_functor(self.right):
      return self.left.factor()
    elif is_identity_functor(self.left):
      return self.right.factor()
    else:
      a, b = self.right.factor()
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
    self.domain = ProjectionVariable(self.relation, common_symbols.domainSymbol)

  def translate(self):
    return basic.Exists(self.variable).compose(
        basic.And(side = right,
          other = basic.Holds(held = variable,
            holding = self.domain)))

  def render(self, context):
    return (renderBoundedVariableBinding(self.variable, self.domain), context)

def renderBoundedVariableBinding(variable, domain):
  middleStack = gl.newTextualGLStack(colors.variableColor, ":")
  return variable.stack(0, middleStack,
      spacing = distances.variable_binding_spacing).stackCentered(0, domain,
          spacing = distances.variable_binding_spacing)

class OrdinaryVariableBinding(VariableBinding):
  def __init__(self, variable):
    self.variable = variable

  def translate(self):
    return basic.Exists(self.variable)

  def render(self, context):
    return (renderVariable(context.bindings), context)

def renderVariable(x, bindings):
  if isinstance(x, GeneralizedVariable) and bindings.has_key(x):
    (inputVariable, functionVariable) = bindings[x]
    return renderApply( renderVariable(inputVariable, bindings)
                      , renderVariable(functionVariable, bindings))
  elif x.__class__ == StringVariable:
    return renderStringVariable(x)
  elif x.__class__ == ProjectionVariable:
    return renderProjectionVariable(x)
  elif x.__class__ == InjectionVariable:
    return renderInjectionVariable(x, bindings)
  elif x.__class__ == ProductVariable:
    return renderProductVariable(x, bindings)
  else:
    raise Exception("Unrecognized logic object %s"%(x,))


class WelldefinedVariableBinding(VariableBinding):
  # variable: a variable
  # relation: an equivalence relation
  def __init__(self, variable, relation):
    self.variable = variable
    self.relation = relation

  def translate(self):
    result = basic.Exists(self.variable)
    newVariable = variable.Variable()
    result = ExpandWellDefined(self.variable, newVariable, self.relation).compose(result)
    return result

  def render(self, context):
    # TODO Render in a clearer way.
    return (renderVariable(self.variable, context.bindings), context)

class ImageVariableBinding(VariableBinding):
  def __init__(self, variable, preimage, function):
    self.variable = variable
    self.preimage = preimage
    self.function = function

  def translate(self):
    return basic.Exists(self.variable).compose(
        basic.And(side = right,
          other = basicFormula.Always(Maps(self.preimage, self.variable, self.function))))

  def render(self, context):
    return (gl.nullStack, context.bind(self.variable, (self.preimage, self.function)))

class Exists(Endofunctor):
  def __init__(self, bindings):
    self.bindings = bindings

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
    result = basic.identity_functor
    for binding in self.bindings[::-1]:
      result = result.compose(bindings.translate())
    return result

class DirectTranslate(Endofunctor):
  def __init__(self, basicEndofunctor, _render):
    self.basicEndofunctor = basicEndofunctor
    self._render = _render
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
      return (self, identity_functor)
  def renderOn(self, context, f):
    return self._render(context, f)
    return self._render(f(context), context)

always_functor = DirectTranslate(basic.always_functor, lambda context, f:
    renderWithBackground(f(context),
      distances.exponential_border_width,
      colors.exponentialColor(context.covariant)))
not_functor = DirectTranslate(basic.not_functor, lambda context, f:
    f(context.negate()))
identity_functor = DirectTranslate(basic.identity_functor, lambda context, f:
    f(context))

def is_identity_functor(f):
  return f.__class__ == DirectTranslate and f.basicEndofunctor.__class__ == basic.Id

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
      length = max(length, s.widths[other_dimension])
      values.apppend(s)
    inserted_kid = f(context)
    length = max(length, inserted_kid[other_dimension])
    values.insert(self.index, inserted_kid)
    return stack.stackAll(dimension,
        _interleave(self.renderDivider(context.covariant, length), values),
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
      result = result.compose(basicEndofunctor()(side = right, other = value.translate()))
    return result

class And(Conjunction):
  def basicEndofunctor(self):
    return basicEndofunctor.And
  def multiOp(self):
    return formula.And

class Or(Conjunction):
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
  return formula.Application(WellDefinedFunctor(variable, newVariable, equivalence), value)

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

