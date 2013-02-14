# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from logic import linearui, gl_primitives, gl_distances, gl_colors
from logic.lib import natural, induction
from stack import gl


# object: a linearui.Logic object
# return: a stack.stack.Stack object s that represents object.
#         s will be 3-d and dispatch to a stack.gl.GLBackend backend.
def render(logic):
  if logic.__class__ == linearui.Conj:
    return renderConj(logic)
  elif logic.__class__ == linearui.Quantifier:
    return renderQuantifier(logic)
  elif logic.__class__ == linearui.Always:
    return renderAlways(logic)
  elif logic.__class__ == linearui.Maybe:
    return renderMaybe(logic)
  elif logic.__class__ == linearui.Not:
    return renderNot(logic)
  elif logic.__class__ == linearui.Var:
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
  dimension = gl_primitives.stackingDimensionOfConjType(conj.type())
  length = gl_distances.min_unit_divider_length
  kids = [render(logic) for logic in conj.values()]
  for kid in kids:
    length = max(length, kid.widths()[gl_primitives.transposeDimension(dimension)])
  length += gl_distances.conj_increase
  res = gl_primitives.unitDivider(conj.type(), length)
  for kid in kids:
    divider = gl_primitives.conjDivider(conj.type(), length)
    res = (res.stack(dimension, kid, spacing = gl_distances.conj_clause_spacing)
      .stack(dimension, divider, spacing = gl_distances.conj_clause_spacing))
  return res

def renderQuantifier(quantifier):
  quantifierStackingDimension = gl_primitives.stackingDimensionOfQuanifierType(quantifier.type())
  variableStackingDimension = gl_primitives.transposeDimension(quantifierStackingDimension)
  if len(quantifier.variables()) == 0:
    variablesStack = gl.nullStack
  else:
    variablesStack = render(quantifier.variables()[0])
    for variable in quantifier.variables()[1:]:
      variablesStack = render(variable).stack(variableStackingDimension, variablesStack,
          spacing = gl_distances.quantifier_variables_spacing)
  bodyStack = render(quantifier.body())
  divider = gl_primitives.quantifierDivider(quantifier.type(),
      max(bodyStack.widths()[variableStackingDimension],
        variablesStack.widths()[variableStackingDimension]))
  return variablesStack.stackCentered(quantifierStackingDimension, divider,
      spacing = gl_distances.quantifier_before_divider_spacing).stackCentered(
      quantifierStackingDimension, bodyStack,
      spacing = gl_distances.quantifier_after_divider_spacing)

def renderAlways(always):
  return renderExponential(True, always)
def renderMaybe(maybe):
  return renderExponential(False, maybe)

def renderExponential(isAlways, exponential):
  value = render(exponential.value())
  widths = [x + 2 * gl_distances.exponential_border_width for x in value.widths()[:2]]
  return gl_primitives.exponentialBox(isAlways, widths).stackCentered(2, value,
      spacing = gl_distances.epsilon)

def renderNot(notObject):
  value = render(notObject.value())
  return gl_primitives.notSymbol(value.widths()[:2]).below(value.shift(gl_distances.notShiftOffset))

def renderVariable(variable):
  return gl.newTextualGLStack(gl_colors.variableColor, variable.name())

def renderIsNatural(isNatural):
  return gl.newTextualGLStack(gl_colors.textColor, isNatural.n().name()  + " : N")

def renderCompare(compare):
  if compare.strict():
    c = " < "
  else:
    c = " <= "
  return gl.newTextualGLStack(gl_colors.textColor,
      compare.lesser().name() + c + compare.greater().name())

def renderSuccessor(successor):
  return gl.newTextualGLStack(gl_colors.textColor,
      "S( %s ) = %s"%(successor.a().name(), successor.b().name()))

