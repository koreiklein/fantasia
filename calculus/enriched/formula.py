# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import misc
from misc import *

from calculus import variable
from calculus.variable import Variable
from calculus.basic import formula as basicFormula, endofunctor as basicEndofunctor, bifunctor as basicBifunctor
from lib.common_symbols import leftSymbol, rightSymbol, relationSymbol, domainSymbol
from ui.stack import gl
from ui.stack import stack
from ui.render.gl import primitives, distances, colors

class Formula:
  def translate(self):
    raise Exception("Abstract superclass.")

  def __eq__(self, other):
    return isinstance(other, Formula) and self.translate() == other.translate()
  def __ne__(self, other):
    return not (self == other)

  def top_level_render(self):
    return self.render(RenderingContext(covariant = True))

  def render(self, context):
    return gl.newTextualGLStack(colors.genericColor, repr(self))

  def substituteVariable(self, a, b):
    raise Exception("Abstract superclass.")

  def updateVariables(self):
    raise Exception("Abstract superclass.")

  def is_and(self):
    return False

  def compress(self):
    return self

  def forwardAndTrue(self):
    values = [And([])]
    if self.is_and():
      values.extend(self.compress().values)
    else:
      values.append(self)
    return Arrow(src = self,
        tgt = And(values),
        basicArrow = self.translate().forwardAndTrue())

  def identity(self):
    return Arrow(src = self, tgt = self, basicArrow = self.translate().identity())

class Arrow:
  def __init__(self, src, tgt, basicArrow):
    self.src = src
    self.tgt = tgt
    self.basicArrow = basicArrow

  def translate(self):
    return self.basicArrow

  def forwardCompose(self, arrow):
    return Arrow(src = self.src, tgt = self.tgt,
        basicArrow = self.basicArrow.forwardCompose(arrow.basicArrow))

  def forwardFollow(self, f):
    return self.forwardCompose(f(self.tgt))

class Holds(Formula):
  def __init__(self, held, holding):
    self.held = held
    self.holding = holding

  def translate(self):
    return basicFormula.Holds(held = self.held,
        holding = self.holding)

  def render(self, context):
    infix = getInfix(self)
    if infix is not None:
      (firstSymbol, secondSymbol) = infix
      assert(len(self.held.symbol_variable_pairs) == 2)
      (aSymbol, aVariable) = self.held.symbol_variable_pairs[0]
      (bSymbol, bVariable) = self.held.symbol_variable_pairs[1]
      if aSymbol == secondSymbol:
        assert(bSymbol == firstSymbol)
        (firstSymbol, secondSymbol) = (secondSymbol, firstSymbol)
      else:
        assert(aSymbol == firstSymbol)
        assert(bSymbol == secondSymbol)
      # Now aSymbol == firstSymbol and bSymbol == secondSymbol
      holds =  stack.stackAll(0, [ aVariable.render()
                                 , self.holding.render()
                                 , bVariable.render()],
                                 spacing = distances.infixSpacing)
    else:
      holds = stack.stackAll(0, [ self.held.render()
                                , primitives.holds()
                                , self.holding.render()],
                                spacing = distances.holdsSpacing)

    return holds

  def substituteVariable(self, a, b):
    return Holds(held = self.held.substituteVariable(a, b),
        holding = self.holding.substituteVariable(a, b))

  def updateVariables(self):
    return self

class Not(Formula):
  def __init__(self, value):
    self.value = value
  def __repr__(self):
    return "~%s"%(self.value,)
  def translate(self):
    return basicFormula.Not(self.value.translate())
  def render(self, context):
    return self.value.render(context.negate())
  def substituteVariable(self, a, b):
    return Not(self.value.substituteVariable(a, b))
  def updateVariables(self):
    return Not(self.value.updateVariables())

class Exists(Formula):
  def __init__(self, bindings, value):
    self.bindings = bindings
    self.value = value
  def __repr__(self):
    return "Exists(%s) . %s"%(self.bindings, self.value)
  def translate(self):
    result = basicEndofunctor.identity_functor
    for binding in self.bindings[::-1]:
      result = result.compose(binding.translate())
    return result.onObject(self.value.translate())
  def render(self, context):
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
    kid = self.value.render(context)
    divider = primitives.quantifierDivider(context.covariant,
        max(kid.widths()[variableStackingDimension],
          variablesStack.widths()[variableStackingDimension]))
    return variablesStack.stackCentered(quantifierStackingDimension, divider,
        spacing = distances.quantifier_before_divider_spacing).stackCentered(
        quantifierStackingDimension, kid,
        spacing = distances.quantifier_after_divider_spacing)

class Always(Formula):
  def __init__(self, value):
    self.value = value
  def __repr__(self):
    return "!%s"%(self.value,)
  def translate(self):
    return basicFormula.Always(self.value.translate())
  def render(self, context):
    return renderWithBackground(self.value.render(context),
        distances.exponential_border_width,
        colors.exponentialColor(context.covariant))
  def substituteVariable(self, a, b):
    return Always(self.value.substituteVariable(a, b))
  def updateVariables(self):
    return Always(self.value.updateVariables())

class WellDefined(Formula):
  def __init__(variable, newVariable, equivalence, value):
    self.variable = variable
    self.newVariable = newVariable
    self.equivalence = equivalence
    self.value = value
  def translate(self):
    return ExpandWellDefined(self.variable, self.newVariable,
        self.equivalence).onObject(self.value.translate())
  def render(self, context):
    # TODO render a well defined formula more clearly?
    return self.value.render(context)
  def substituteVariable(self, a, b):
    return WellDefined(variable = self.variable.substituteVariable(a, b),
        newVariable = self.newVariable.substituteVariable(a, b),
        equivalence = self.equivalence.substituteVariable(a, b),
        value = self.value.substituteVariable(a, b))
  def updateVariables(self):
    return WellDefined(variable = self.variable,
        newVariable = self.newVariable,
        equivalence = self.equivalence,
        value = self.value.updateVariables())

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


class Conjunction(Formula):
  def __init__(self, values):
    for i in range(len(values)):
      value = values[i]
      if not(isinstance(value, Formula)):
        raise Exception("%s at index %s is not an enriched formula."%(value, i))
    self.values = values
    self.basicBinop = self.basicBinop()

  def translate(self):
    return basicFormula.multiple_conjunction(conjunction = self.basicBinop,
        values = [value.translate() for value in self.values])

  def substituteVariable(self, a, b):
    return self.__class__(values = [v.substituteVariable(a, b) for v in self.values])

  def updateVariables(self):
    return self.__class__(values = [v.updateVariables() for v in self.values])

  def render(self, context):
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
    return stack.stackAll(dimension,
        misc._interleave(self.renderDivider(context.covariant, length), values),
        spacing = distances.divider_spacing)

class And(Conjunction):
  def is_and(self):
    return True

  def basicBinop(self):
    return basicFormula.And

  def renderDivider(self, covariant, length):
    return primitives.andDivider(covariant)(length)

class Or(Conjunction):
  def basicBinop(self):
    return basicFormula.Or

  def renderDivider(self, covariant, length):
    return primitives.orDivider(covariant)(length)

true = And([])
false = Or([])

class Iff(Formula):
  def __init__(self, left, right):
    self.left = left
    self.right = right
  def __repr__(self):
    return "Iff(\n%s\n<==>\n%s\n)"%(self.left, self.right)
  def translate(self):
    return basicFormula.ExpandIff(self.left.translate(), self.right.translate())
  def updateVariables(self):
    return Iff(left = self.left.updateVariables(),
        right = self.right.updateVariables())
  def substituteVariable(self, a, b):
    return Iff(left = self.left.substituteVariable(a, b),
        right = self.right.substituteVariable(a, b))

  def render(self, context):
    kid_context = context.as_covariant()
    res = self.left.render(kid_context).stack(0,
        primitives.iff(),
        spacing = distances.iffSpacing).stack(0,
            self.right.render(kid_context),
            spacing = distances.iffSpacing)
    if context.covariant:
      return res
    else:
      return renderNotWithSymbol(res)

class Hidden(Formula):
  def __init__(self, base, name):
    self.base = base
    self.name = name

  def __repr__(self):
    return "<<" + self.name + ">>"
  def translate(self):
    return self.base.translate()
  def updateVariables(self):
    return Hidden(base = self.base.updateVariables(), name = self.name)
  def substituteVariable(self, a, b):
    return Hidden(base = self.base.substituteVariable(a, b), name = self.name)

def InDomain(x, e):
  return Always(Holds(x, variable.ApplySymbolVariable(e, domainSymbol)))

def Equal(a, b, e):
  return Always(Holds(
      variable.ProductVariable([(leftSymbol, a), (rightSymbol, b)]),
      variable.ApplySymbolVariable(e, relationSymbol)))

class Unique(Formula):
  def __init__(self, variable, equivalence, formula, newVariable = None):
    self.variable = variable
    self.equivalence = equivalence
    self.formula = formula
    if newVariable is None:
      self.newVariable = Variable()
    else:
      self.newVariable = newVariable

  def translate(self):
    formulaTranslate = self.formula.translate()
    all_others_are_equal = basicFormula.Not(
        basicFormula.Exists(self.newVariable,
          basicFormula.And(basicFormula.And(
            InDomain(self.newVariable, self.equivalence),
            formulaTranslate.substituteVariable(self.variable, self.newVariable)),
            basicFormula.Not(Equal(self.newVariable, self.variable, self.equivalence)))))
    return basicFormula.And(formulaTranslate, all_others_are_equal)

  def substituteVariable(self, a, b):
    assert(b != self.newVariable)
    assert(a != self.newVariable)
    return Unique(variable = self.variable.substituteVariable(a, b),
        equivalence = self.equivalence.substituteVariable(a, b),
        formula = self.formula.substituteVariable(a, b),
        newVariable = self.newVariable)

  def updateVariables(self):
    return Unique(variable = self.variable,
        equivalence = self.equivalence,
        formula = self.formula.updateVariables(),
        newVariable = self.newVariable.updateVariables())

  def render(self, context):
    return gl.newTextualGLStack(colors.variableColor,
        "%s ! in %s . "%(self.variable, self.equivalence)).stack(0,
            self.formula.render(context))


class RenderingContext:
  def __init__(self, covariant):
    self.covariant = covariant

  def negate(self):
    return RenderingContext(covariant = not self.covariant)

  def as_covariant(self):
    return self if self.covariant else self.negate()

# holds: a basic.Holds
# return: the pair of infix symbols, or None of no such symbols exist.
def getInfix(holds):
  if holds.held.__class__ != variable.ProductVariable:
    return None
  v = holds.holding
  if v.__class__ == variable.StringVariable and v.infix is not None:
    return v.infix
  elif v.__class__ == variable.ApplySymbolVariable and v.symbol.infix is not None:
    return v.symbol.infix
  else:
    return None

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

