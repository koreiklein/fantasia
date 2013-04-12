# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import enriched, relation, variable, datum
from ui.render.gl import primitives, distances, colors

from lib import oldNatural, natural
from ui.stack import gl
from ui.stack.stack import stackAll


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
  elif isinstance(logic, variable.Variable):
    return renderVariable(logic)
  elif logic.__class__ == relation.Holds:
    return renderHolds(logic)
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
  widths = [x + 2 * distances.exponential_border_width for x in value.widths()]
  widths[2] = 0.0
  return primitives.exponentialBox(isAlways, widths).stackCentered(2, value,
      spacing = distances.epsilon )

def renderNot(notObject):
  value = render(notObject.value())
  return primitives.notSymbol(value.widths()[:2]).below(value.shift(distances.notShiftOffset))

def renderVariable(variable):
  return gl.newTextualGLStack(colors.variableColor, repr(variable))

def renderHolds(holds):
  holding = renderVariable(holds.holding())
  held = renderDatum(holds.held())
  d = 1
  between = primitives.holdsStack(max(holding.widths()[d], held.widths()[d]))
  return stackAll(d, [holding, between, held])

def renderSymbol(symbol):
  return gl.newTextualGLStack(colors.symbolColor, repr(symbol))

def renderDatum(d):
  if d.__class__ == datum.Variable:
    return renderDatumVariable(d)
  elif d.__class__ == datum.Record:
    return renderDatumRecord(d)
  elif d.__class__ == datum.Case:
    return renderDatumCase(d)
  elif d.__class__ == datum.Projection:
    return renderDatumProjection(d)
  else:
    assert(d.__class__ == datum.Coinjection)
    return renderDatumCoinjection(d)


def renderDatumVariable(d):
  return renderVariable(d.variable())

def renderDatumRecord(d):
  res = primitives.empty()
  for (symbol, d) in d.pairs():
    res = res.stack(0, renderSymbol(symbol).stackCentered(1, renderDatum(d)))
  return res

def renderDatumCase(d):
  return renderSymbol(d.symbol()).stackCentered(1, renderDatum(d.value()))

def renderDatumProjection(d):
  return renderDatum(d.value()).stack(0,
      primitives.projectionDot()).stack(0,
          renderSymbol(d.symbol()))

def renderDatumCoinjection(d):
  return renderDatum(d.value()).stack(0,
      primitives.coinjectionDot()).stack(0,
          renderSymbol(d.symbol()))
