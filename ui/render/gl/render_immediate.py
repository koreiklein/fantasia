# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic, enriched, symbol
from ui.render.gl import primitives, distances, colors
from ui.stack import gl
from ui.stack import stack

def render(x, covariant = True):
  if isinstance(x, basic.Conjunction):
    return renderConjunction(x, covariant = covariant)
  elif x.__class__ == basic.Exists:
    return renderExists(valueStack = render(x.value, covariant),
        variablesList = [renderVariable(variable) for variable in x.variables],
        covariant = covariant)
  elif x.__class__ == enriched.Iff:
    return renderEnrichedIff(x, covariant = covariant)
  elif x.__class__ == enriched.Hidden:
    return renderEnrichedHidden(x, covariant = covariant)
  elif x.__class__ == enriched._Quantifier:
    return renderExists(valueStack = render(x.value, covariant),
        variablesList = [renderVariableBinding(
          variable = renderVariable(binding.variable),
          unique = binding.unique,
          equivalence = renderVariable(binding.equivalence),
          covariant = covariant)
          for binding in x.bindings],
        covariant = covariant if x.isExists() else not covariant)
  elif x.__class__ == enriched.EnrichedHolds:
    return renderHolds(x, covariant = covariant)
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

def renderVariable(x):
  if x.__class__ == basic.StringVariable:
    return renderStringVariable(x)
  elif x.__class__ == basic.ProjectionVariable:
    return renderProjectionVariable(x)
  elif x.__class__ == basic.InjectionVariable:
    return renderProjectionVariable(x)
  elif x.__class__ == basic.ProductVariable:
    return renderProductVariable(x)
  elif x.__class__ == enriched.Apply:
    return renderApply(renderVariable(x.x), renderVariable(x.f))
  else:
    raise Exception("Unrecognized logic object %s"%(x,))

def renderApply(x, f):
  return stack.stackAll(0, [x, primitives.apply(), f], spacing = distances.applySpacing)

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
  return renderVariable(binding.variable).stack(dimension,
      middleStack,
      spacing = distances.enriched_variable_binding_spacing).stackCentered(dimension,
          renderVariable(binding.equivalence),
          spacing = distances.enriched_variable_binding_spacing)

def renderAlways(value, covariant):
  return renderWithBackground( value
                             , distances.exponential_border_width
                             , colors.exponentialColor(covariant))

def renderWithBackground(s, border_width, color):
  widths = [x + 2 * border_width for x in s.widths()]
  widths[2] = 0.0
  return primitives.solidSquare(color, widths).stackCentered(2, s,
      spacing = distances.epsilon )

def renderAndUnit(x, covariant = True):
  return primitives.trueDivider(distances.min_unit_divider_length)

def renderOrUnit(x, covariant = True):
  return primitives.falseDivider(distances.min_unit_divider_length)

def renderStringVariable(x):
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

def renderEnrichedHidden(x, covariant):
  return gl.newTextualGLStack(colors.hiddenColor, "<<" + x.name + ">>")

def renderHolds(x, covariant):
  if (x.holding.__class__ == basic.StringVariable
      and x.holding.infix is not None
      and x.held.__class__ == basic.ProductVariable):
    (firstSymbol, secondSymbol) = x.holding.infix
    assert(len(x.held.symbol_variable_pairs) == 2)
    (aSymbol, aVariable) = x.held.symbol_variable_pairs[0]
    (bSymbol, bVariable) = x.held.symbol_variable_pairs[1]
    if aSymbol == secondSymbol:
      assert(bSymbol == firstSymbol)
      (firstSymbol, secondSymbol) = (secondSymbol, firstSymbol)
    else:
      assert(aSymbol == firstSymbol)
      assert(bSymbol == secondSymbol)
    # Now aSymbol == firstSymbol and bSymbol == secondSymbol
    return stack.stackAll(0, [ renderVariable(aVariable)
                             , renderVariable(x.holding)
                             , renderVariable(bVariable)],
                             spacing = distances.infixSpacing)
  else:
    holds = stack.stackAll(0, [ renderVariable(x.held)
                              , primitives.holds()
                              , renderVariable(x.holding)],
                              spacing = distances.holdsSpacing)

  if covariant:
    return holds
  else:
    return renderNotWithSymbol(holds)

def renderProjectionVariable(v):
  return gl.newTextualGLStack(colors.variableColor, repr(v))

def renderInjectionVariable(v):
  return gl.newTextualGLStack(colors.variableColor, repr(v))

def borderStack(dimension, color, a, b, borderWidth):
  return renderWithBackground(a.stack(dimension, b, spacing = borderWidth), borderWidth, color)

def renderSymbolVariablePair(s, v, c0, c1):
  widths = [max(s.widths()[0], v.widths()[0]) , 0.0, 0.0]
  return borderStack(1
                    , colors.symbolVariablePairBorderColor
                    , renderWithBackground(s.atLeast(widths),
                        distances.symbolBackgroundBorderWidth, c0)
                    , renderWithBackground(v.atLeast(widths),
                        distances.variableBackgroundBorderWidth, c1)
                    , distances.productVariableBorder)

def renderProductVariable(productVariable):
  symbolVariablePairs = []
  for i in range(len(productVariable.symbol_variable_pairs)):
    (s,v) = productVariable.symbol_variable_pairs[i]
    (c0, c1) = colors.productPairsColor(i)
    symbolVariablePairs.append(renderSymbolVariablePair(renderSymbol(s),
      renderVariable(v), c0, c1))
  return stack.stackAll(0, symbolVariablePairs,
      spacing = distances.productVariableHorizontalSpacing)

