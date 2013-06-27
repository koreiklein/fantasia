# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import formula
from ui.render.gl import primitives, distances, colors
from ui.stack import gl
from ui.stack import stack
from lib.common_symbols import inputSymbol, outputSymbol, relationSymbol, leftSymbol, rightSymbol

# bindings: a dictionary mapping certain variables to stacks that should be used to
# render them.
def render(x, covariant, bindings):
  if isinstance(x, basic.Conjunction):
    return renderConjunction(x, covariant = covariant, bindings = bindings)
  elif x.__class__ == basic.Exists:
    variables = []
    while x.__class__ == basic.Exists:
      bound = tryBind(x.value, x.variable, bindings)
      if bound is not None:
        bindings = _addBinding(bindings, x.variable, bound)
      else:
        variables.append(x.variable)
      x = x.value
    renderedVariables = []
    while True:
      if x.__class__ == basic.And:
        if x.left.__class__ == basic.Always and x.left.value.__class__ == basic.Holds:
          matched = False
          for i in range(len(variables)):
            v = variables[i]
            if x.left.value.held == v:
              renderedVariables.append(
                  renderVariableBinding( renderVariable(v, bindings)
                                       , renderVariable(x.left.value.holding, bindings)))
              x = x.right
              matched = True
              variables.pop(i)
              break
          if matched:
            continue
      break
    for v in variables:
      renderedVariables.append(renderVariable(v, bindings))
    if len(renderedVariables) == 0:
      return render(x, covariant, bindings)
    else:
      return renderExists(valueStack = render(x, covariant, bindings),
          variablesList = renderedVariables,
          covariant = covariant,
          bindings = bindings)
  elif x.__class__ == basic.Iff:
    return renderIff(x, covariant = covariant)
  elif x.__class__ == basic.Hidden:
    return renderHidden(x, covariant = covariant)
  elif x.__class__ == basic.Holds:
    return renderHolds(x, covariant = covariant, bindings = bindings)
  elif x.__class__ == basic.Not:
    if x.rendered or (x.value.__class__ == basic.Holds and covariant):
      return renderNotWithSymbol(render(x.value, covariant, bindings))
    else:
      return render(x.value, not covariant, bindings)
  elif x.__class__ == basic.Always:
    return renderAlways(render(x.value, covariant, bindings), covariant)
  elif x.__class__ == basic.AndUnit:
    return renderAndUnit(x, covariant = covariant)
  elif x.__class__ == basic.OrUnit:
    return renderOrUnit(x, covariant = covariant)
  else:
    raise Exception("Unrecognized logic object %s of class %s"%(x,x.__class__))

def renderVariable(x, bindings):
  if isinstance(x, basic.Variable) and bindings.has_key(x):
    (inputVariable, functionVariable) = bindings[x]
    return renderApply( renderVariable(inputVariable, bindings)
                      , renderVariable(functionVariable, bindings))
  elif x.__class__ == basic.StringVariable:
    return renderStringVariable(x)
  elif x.__class__ == basic.ProjectionVariable:
    return renderProjectionVariable(x)
  elif x.__class__ == basic.InjectionVariable:
    return renderInjectionVariable(x, bindings)
  elif x.__class__ == basic.ProductVariable:
    return renderProductVariable(x, bindings)
  else:
    raise Exception("Unrecognized logic object %s"%(x,))

def renderApply(x, f):
  return stack.stackAll(0, [x, primitives.apply(), f], spacing = distances.applySpacing)

# return: The pair (a, F) such that ({input : a, output : x} : F) occurs "at the top of" formula.
#         or None if no such pair exists.
def tryBind(formula, v, bindings):
  if (formula.__class__ == basic.Holds and
      formula.held.__class__ == basic.ProductVariable and
      len(formula.held.symbol_variable_pairs) == 2 and
      (outputSymbol, v) in formula.held.symbol_variable_pairs):
    for symbol, variable in formula.held.symbol_variable_pairs:
      if symbol == inputSymbol:
        return (variable, formula.holding)
    raise Exception("Should always find an inputSymbol when you find an inputSymbol.")
  if (formula.__class__ == basic.Holds and
        formula.held.__class__ == basic.ProductVariable and
        formula.holding.__class__ == basic.ProjectionVariable and
        formula.holding.symbol == relationSymbol):
    (leftVariable, rightVariable) = _getLeftAndRightVariables(formula.held)
    if rightVariable == v and bindings.has_key(leftVariable):
      return bindings[leftVariable]
    elif leftVariable == v and bindings.has_key(rightVariable):
      return bindings[rightVariable]
  if formula.__class__ == basic.And:
    result = tryBind(formula.left, v, bindings)
    return (result if result is not None else tryBind(formula.right, v, bindings))
  if formula.__class__ == basic.Always:
    return tryBind(formula.value, v, bindings)
  if formula.__class__ == basic.Exists:
    return tryBind(formula.value, v, bindings)
  return None

def renderConjunction(x, covariant, bindings):
  if x.__class__ == basic.And:
    free = x.freeVariables()
    for v in free:
      if not bindings.has_key(v):
        bound = tryBind(x, v, bindings)
        if bound is not None:
          bindings = _addBinding(bindings, v, bound)
    if _isUnnecessaryInputOutputRelation(x.left, bindings):
      return render(x.right, covariant, bindings)
    elif _isUnnecessaryInputOutputRelation(x.right, bindings):
      return render(x.left, covariant, bindings)
    else:
      # TODO: This construct is a mess.  Use something cleaner.
      pass # Pass through to the below code.
  left = render(x.left, covariant, bindings)
  right = render(x.right, covariant, bindings)
  if x.right == basic.unit_for_conjunction(x.__class__):
    return left
  #elif x.left == basic.unit_for_conjunction(x.__class__):
  #  return right
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

def renderNotWithSymbol(value):
  return primitives.notSymbol(value.widths()[:2]).below(
      value.shift(distances.notShiftOffset))

def renderExists(valueStack, variablesList, covariant, bindings):
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

def renderVariableBinding(variable, domain):
  middleStack = gl.newTextualGLStack(colors.variableColor, ":")
  return variable.stack(0, middleStack,
      spacing = distances.variable_binding_spacing).stackCentered(0, domain,
          spacing = distances.variable_binding_spacing)

def renderAlways(value, covariant):
  return renderWithBackground( value
                             , distances.exponential_border_width
                             , colors.exponentialColor(covariant))

def renderWithBackground(s, border_width, color):
  widths = [x + 2 * border_width for x in s.widths()]
  widths[2] = 0.0
  return primitives.solidSquare(color, widths).stackCentered(2, s,
      spacing = distances.epsilon )

def renderAndUnit(x, covariant):
  return (primitives.trueDivider(distances.min_unit_divider_length) if covariant
          else primitives.falseDivider(distances.min_unit_divider_length))

def renderOrUnit(x, covariant):
  return (primitives.falseDivider(distances.min_unit_divider_length) if covariant
          else primitives.trueDivider(distances.min_unit_divider_length))

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

def renderCall(x, covariant):
  res = render(x.left, True).stack(0,
      primitives.callDot,
      spacing = distances.callSpacing).stack(0,
          render(x.right, True),
          spacing = distances.callSpacing)
  if covariant:
    return res
  else:
    return renderNotWithSymbol(res)

def renderIff(x, covariant):
  res = render(x.left, True).stack(0,
      primitives.iff(),
      spacing = distances.iffSpacing).stack(0,
          render(x.right, True),
          spacing = distances.iffSpacing)
  if covariant:
    return res
  else:
    return renderNotWithSymbol(res)

def renderHidden(x, covariant):
  return gl.newTextualGLStack(colors.hiddenColor, "<<" + x.name + ">>")

# holds: a basic.Holds
# return: the pair of infix symbols, or None of no such symbols exist.
def getInfix(holds):
  if holds.held.__class__ != basic.ProductVariable:
    return None
  variable = holds.holding
  if variable.__class__ == basic.StringVariable and variable.infix is not None:
    return variable.infix
  elif variable.__class__ == basic.ProjectionVariable and variable.symbol.infix is not None:
    return variable.symbol.infix
  else:
    return None

# x: a basic.ProductVariable
# return: (inputVariable, outputVariable) if possible otherwise None
def _getInputAndOutputVariables(x):
  return _getPair(x, (inputSymbol, outputSymbol))

def _getLeftAndRightVariables(x):
  return _getPair(x, (leftSymbol, rightSymbol))

def _getPair(x, (left, right)):
  assert(x.__class__ == basic.ProductVariable)
  if len(x.symbol_variable_pairs) == 2:
    if x.symbol_variable_pairs[0][0] == left:
      assert(x.symbol_variable_pairs[1][0] == right)
      return (x.symbol_variable_pairs[0][1], x.symbol_variable_pairs[1][1])
    elif x.symbol_variable_pairs[0][0] == right:
      assert(x.symbol_variable_pairs[1][0] == left)
      return (x.symbol_variable_pairs[1][1], x.symbol_variable_pairs[0][1])
  return None

def _isNearlyAndUnit(x):
  return (x == basic.unit_for_conjunction(basic.And) or
      (x.__class__ == basic.Always and _isNearlyAndUnit(x.value)))

def _isUnnecessaryInputOutputRelation(formula, bindings):
  if formula.__class__ == basic.Always:
    return _isUnnecessaryInputOutputRelation(formula.value, bindings)
  elif formula.__class__ == basic.And:
    if _isNearlyAndUnit(formula.left):
      return _isUnnecessaryInputOutputRelation(formula.right, bindings)
    elif _isNearlyAndUnit(formula.right):
      return _isUnnecessaryInputOutputRelation(formula.left, bindings)
    elif (_isUnnecessaryInputOutputRelation(formula.left, bindings) and
        _isUnnecessaryInputOutputRelation(formula.right, bindings)):
      return True
  if (formula.__class__ == basic.Holds and
      formula.held.__class__ == basic.ProductVariable):
    ioVariables = _getInputAndOutputVariables(formula.held)
    if ioVariables is not None:
      (inputVariable, outputVariable) = ioVariables
      if bindings.has_key(outputVariable):
        (boundInputVariable, boundFunctionVariable) = bindings[outputVariable]
        if boundFunctionVariable == formula.holding:
          return True
  if _isNearlyAndUnit(formula):
    return True
  return False

def renderHolds(x, covariant, bindings):
  infix = getInfix(x)
  if infix is not None:
    (firstSymbol, secondSymbol) = infix
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
    holds =  stack.stackAll(0, [ renderVariable(aVariable, bindings)
                               , renderVariable(x.holding, bindings)
                               , renderVariable(bVariable, bindings)],
                               spacing = distances.infixSpacing)
  else:
    holds = stack.stackAll(0, [ renderVariable(x.held, bindings)
                              , primitives.holds()
                              , renderVariable(x.holding, bindings)],
                              spacing = distances.holdsSpacing)

  return holds

def renderProjectionVariable(v):
  return gl.newTextualGLStack(colors.variableColor, repr(v))

def renderInjectionVariable(v, bindings):
  return renderSymbolVariablePair(renderSymbol(v.symbol), renderVariable(v.variable, bindings),
      colors.injectionSymbolBackgroundColor,
      colors.injectionVariableBackgroundColor)

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

def renderProductVariable(productVariable, bindings):
  symbolVariablePairs = []
  for i in range(len(productVariable.symbol_variable_pairs)):
    (s,v) = productVariable.symbol_variable_pairs[i]
    (c0, c1) = colors.productPairsColor(i)
    symbolVariablePairs.append(renderSymbolVariablePair(renderSymbol(s),
      renderVariable(v, bindings), c0, c1))
  return stack.stackAll(0, symbolVariablePairs,
      spacing = distances.productVariableHorizontalSpacing)

def _addBinding(bindings, key, value):
  result = dict(bindings)
  result[key] = value
  return result

