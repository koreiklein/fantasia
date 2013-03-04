# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import enriched
from ui.render.gl import primitives, distances, colors

from lib import natural
from ui.stack import gl


# object: a enriched.Logic object
# return: a stack.stack.Stack object s that represents object.
#         s will be 3-d and dispatch to a stack.gl.GLBackend backend.
def render(logic):
  if logic.__class__ == enriched.Conj:
    return renderConj(logic)
  elif logic.__class__ == enriched.Quantifier:
    return renderQuantifier(logic)
  elif logic.__class__ == enriched.Always:
    return renderAlways(logic)
  elif logic.__class__ == enriched.Maybe:
    return renderMaybe(logic)
  elif logic.__class__ == enriched.Not:
    return renderNot(logic)
  elif logic.__class__ == enriched.Var:
    return renderVariable(logic)
  elif logic.__class__ == natural.IsNatural:
    return renderIsNatural(logic)
  elif logic.__class__ == natural.Compare:
    return renderCompare(logic)
  elif logic.__class__ == natural.Successor:
    return renderSuccessor(logic)
  else:
    raise Exception("Unrecognized logic object %s"%(logic,))

def renderConj(conj):
  dimension = primitives.stackingDimensionOfConjType(conj.type())
  length = distances.min_unit_divider_length
  kids = [render(logic) for logic in conj.values()]
  for kid in kids:
    length = max(length, kid.widths()[primitives.transposeDimension(dimension)])
  length += distances.conj_increase
  res = primitives.unitDivider(conj.type(), length)
  for kid in kids:
    divider = primitives.conjDivider(conj.type(), length)
    res = (res.stack(dimension, kid, spacing = distances.conj_clause_spacing)
      .stack(dimension, divider, spacing = distances.conj_clause_spacing))
  return res

def renderQuantifier(quantifier):
  quantifierStackingDimension = primitives.stackingDimensionOfQuanifierType(quantifier.type())
  variableStackingDimension = primitives.transposeDimension(quantifierStackingDimension)
  if len(quantifier.variables()) == 0:
    variablesStack = gl.nullStack
  else:
    variablesStack = render(quantifier.variables()[0])
    for variable in quantifier.variables()[1:]:
      variablesStack = variablesStack.stack(variableStackingDimension, render(variable),
          spacing = distances.quantifier_variables_spacing)
  bodyStack = render(quantifier.body())
  divider = primitives.quantifierDivider(quantifier.type(),
      max(bodyStack.widths()[variableStackingDimension],
        variablesStack.widths()[variableStackingDimension]))
  return variablesStack.stackCentered(quantifierStackingDimension, divider,
      spacing = distances.quantifier_before_divider_spacing).stackCentered(
      quantifierStackingDimension, bodyStack,
      spacing = distances.quantifier_after_divider_spacing)

def renderAlways(always):
  return renderExponential(True, always)
def renderMaybe(maybe):
  return renderExponential(False, maybe)

def renderExponential(isAlways, exponential):
  value = render(exponential.value())
  widths = [x + 2 * distances.exponential_border_width for x in value.widths()[:2]]
  return primitives.exponentialBox(isAlways, widths).stackCentered(2, value,
      spacing = distances.epsilon)

def renderNot(notObject):
  value = render(notObject.value())
  return primitives.notSymbol(value.widths()[:2]).below(value.shift(distances.notShiftOffset))

def renderVariable(variable):
  return gl.newTextualGLStack(colors.variableColor, variable.name())

def renderIsNatural(isNatural):
  return gl.newTextualGLStack(colors.textColor, isNatural.n().name()  + " : N")

def renderCompare(compare):
  if compare.strict():
    c = " < "
  else:
    c = " <= "
  return gl.newTextualGLStack(colors.textColor,
      compare.lesser().name() + c + compare.greater().name())

def renderSuccessor(successor):
  return gl.newTextualGLStack(colors.textColor,
      "S( %s ) = %s"%(successor.a().name(), successor.b().name()))

