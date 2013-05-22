# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic, enriched, symbol
from ui.render.gl import primitives, distances, colors
from ui.stack import gl

def render(x, covariant = True):
  if isinstance(x, basic.Conjunction):
    return renderConjunction(x, covariant = covariant)
  elif x.__class__ == basic.Exists:
    return renderExists(valueStack = render(x.value, covariant),
        variablesList = [renderVariable(variable, covariant) for variable in x.variables],
        covariant = covariant)
  elif x.__class__ == enriched.Iff:
    return renderEnrichedIff(x, covariant = covariant)
  elif x.__class__ == enriched.Hidden:
    return renderEnrichedHidden(x, covariant = covariant)
  elif x.__class__ == enriched._Quantifier:
    return renderExists(valueStack = render(x.value, covariant),
        variablesList = [renderVariableBinding(
          variable = renderVariable(binding.variable, covariant),
          unique = binding.unique,
          equivalence = renderVariable(binding.equivalence, covariant),
          covariant = covariant)
          for binding in x.bindings],
        covariant = covariant if x.isExists() else not covariant)
  elif x.__class__ == enriched.EnrichedHolds:
    return renderEnrichedHolds(x, covariant = covariant)
  elif x.__class__ == basic.Not:
    if x.rendered:
      return renderNotWithSymbol(render(x.value, covariant))
    else:
      return render(x.value, not covariant)
  elif x.__class__ == basic.Always:
    return renderAlways(render(x.value, covariant), covariant)
  elif x.__class__ == basic.AndUnit:
    return renderAndUnit(x, covariant = covariant)
  elif x.__class__ == basic.OrUnit:
    return renderOrUnit(x, covariant = covariant)
  elif x.__class__ == basic.Holds:
    return renderHolds(x, covariant = covariant)
  else:
    raise Exception("Unrecognized logic object %s of class %s"%(x,x.__class__))

def renderVariable(x, covariant = True):
  if x.__class__ == basic.StringVariable:
    return renderStringVariable(x, covariant = covariant)
  elif x.__class__ == basic.ProjectionVariable:
    return renderProjectionVariable(x, covariant = covariant)
  elif x.__class__ == basic.InjectionVariable:
    return renderProjectionVariable(x, covariant = covariant)
  elif x.__class__ == basic.ProductVariable:
    return renderProjectionVariable(x, covariant = covariant)
  else:
    raise Exception("Unrecognized logic object %s"%(x,))

def renderConjunction(x, covariant = True):
  left = render(x.left, covariant)
  right = render(x.right, covariant)
  if x.right == basic.unit_for_conjunction(x.__class__):
    return left
  elif x.left == basic.unit_for_conjunction(x.__class__):
    return right
  else:
    if x.__class__ == basic.And:
      return renderAnd(left, right, covariant)
    elif x.__class__ == basic.Or:
      return renderOr(left, right, covariant)
    else:
      raise Exception("Unrecognized logic object %s"%(x,))

def _dimension_for_variance(covariant):
  if covariant:
    return 0
  else:
    return 1

def renderTripleCentered(dimension, left, middle, right):
  codimension = primitives._dual_dimension(dimension)
  m = max(left.widths()[codimension], right.widths()[codimension])
  return left.stackCentered(dimension,
      middle(length = m),
      spacing = distances.divider_spacing).stackCentered(dimension,
          right,
          spacing = distances.divider_spacing)

def renderTriple(dimension, left, middle, right):
  codimension = primitives._dual_dimension(dimension)
  m = max(left.widths()[codimension], right.widths()[codimension])
  return left.stack(dimension,
      middle(length = m),
      spacing = distances.divider_spacing).stack(dimension,
          right,
          spacing = distances.divider_spacing)

def renderIntersect(x, covariant = True):
  res = renderTripleCentered(dimension = _dimension_for_variance(covariant = True),
      left = render(x.left, True),
      middle = primitives.intersectDivider(True),
      right = render(x.right, True))
  if covariant:
    return res
  else:
    return renderNotWithSymbol(res)

def renderAnd(left, right, covariant):
  return renderTriple(dimension = _dimension_for_variance(covariant),
      left = left,
      middle = primitives.andDivider(covariant),
      right = right)

def renderOr(left, right, covariant):
  return renderTriple(dimension = _dimension_for_variance(covariant),
      left = left,
      middle = primitives.orDivider(covariant),
      right = right)

def renderNot(value, covariant):
  return render(value, not variant)

def renderNotWithSymbol(value):
  return primitives.notSymbol(value.widths()[:2]).below(
      value.shift(distances.notShiftOffset))

def renderExists(valueStack, variablesList, covariant):
  quantifierStackingDimension = _dimension_for_variance(covariant)
  variableStackingDimension = primitives._dual_dimension(quantifierStackingDimension)
  if len(variablesList) == 0:
    variablesStack = gl.nullStack
  else:
    variablesStack = variablesList[0]
    for variable in variablesList[1:]:
      variablesStack = variablesStack.stack(variableStackingDimension,
          variable,
          spacing = distances.quantifier_variables_spacing)
  divider = primitives.quantifierDivider(covariant,
      max(valueStack.widths()[variableStackingDimension],
        variablesStack.widths()[variableStackingDimension]))
  return variablesStack.stackCentered(quantifierStackingDimension, divider,
      spacing = distances.quantifier_before_divider_spacing).stackCentered(
      quantifierStackingDimension, valueStack,
      spacing = distances.quantifier_after_divider_spacing)

def renderVariableBinding(variable, unique, equivalence, covariant):
  dimension = 0
  if unique:
    c = '!'
  else:
    c = ':'
  middleStack = gl.newTextualGLStack(colors.variableColor, c)
  return variable.stack(dimension,
      middleStack,
      spacing = distances.enriched_variable_binding_spacing).stackCentered(dimension,
          equivalence,
          spacing = distances.enriched_variable_binding_spacing)

def _renderVariableBinding(binding, covariant = True):
  dimension = 0
  if binding.unique:
    c = '!'
  else:
    c = ':'
  middleStack = gl.newTextualGLStack(colors.variableColor, c)
  return renderVariable(binding.variable, covariant).stack(dimension,
      middleStack,
      spacing = distances.enriched_variable_binding_spacing).stackCentered(dimension,
          renderVariable(binding.equivalence, covariant),
          spacing = distances.enriched_variable_binding_spacing)

def renderAlways(value, covariant):
  widths = [x + 2 * distances.exponential_border_width for x in value.widths()]
  widths[2] = 0.0
  return primitives.exponentialBox(covariant, widths).stackCentered(2, value,
      spacing = distances.epsilon )

def renderAndUnit(x, covariant = True):
  return primitives.trueDivider(distances.min_unit_divider_length)

def renderOrUnit(x, covariant = True):
  return primitives.falseDivider(distances.min_unit_divider_length)

def renderStringVariable(x, covariant = True):
  return gl.newTextualGLStack(colors.variableColor, repr(x))

def _renderDot(left, dot, s):
  return left.stack(0,
      dot, spacing = distances.before_dot_spacing).stack(0,
      s, spacing = distances.after_dot_spacing)

def renderSymbol(s):
  if s.__class__ == symbol.StringSymbol:
    return renderStringSymbol(s)
  else:
    raise Exception("Unrecognized symbol %s"%(s,))

def renderStringSymbol(s):
  return gl.newTextualGLStack(colors.symbolColor, repr(s))

def renderCall(x, covariant = True):
  res = render(x.left, True).stack(0,
      primitives.callDot,
      spacing = distances.callSpacing).stack(0,
          render(x.right, True),
          spacing = distances.callSpacing)
  if covariant:
    return res
  else:
    return renderNotWithSymbol(res)

def renderEnrichedIff(x, covariant):
  res = render(x.left, True).stack(0,
      primitives.iff(),
      spacing = distances.iffSpacing).stack(0,
          render(x.right, True),
          spacing = distances.iffSpacing)
  if covariant:
    return res
  else:
    return renderNotWithSymbol(res)

def renderEnrichedHolds(x, covariant):
  return gl.newTextualGLStack(colors.relationColor, repr(x))

def renderEnrichedHidden(x, covariant):
  return gl.newTextualGLStack(colors.hiddenColor, "<<" + x.name + ">>")

def renderHolds(x, covariant):
  holds =  gl.newTextualGLStack(colors.relationColor, repr(x))
  if covariant:
    return holds
  else:
    return renderNotWithSymbol(holds)

def renderProjectionVariable(v, covariant):
  return gl.newTextualGLStack(colors.variableColor, repr(v))

def renderInjectionVariable(v, covariant):
  return gl.newTextualGLStack(colors.variableColor, repr(v))

def renderProductVariable(v, covariant):
  return gl.newTextualGLStack(colors.variableColor, repr(v))

