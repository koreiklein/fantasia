# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import calculus.variable
from calculus.variable import Variable
from calculus.basic import formula as basicFormula
from lib.common_symbols import leftSymbol, rightSymbol, relationSymbol
from ui.stack import gl
from ui.stack import stack
from ui.render.gl import primitives, distances, colors

class Formula:
  def translate(self):
    raise Exception("Abstract superclass.")

  # index: an index
  #   self must be equivalent to a functor of the form a o b where
  #   b == And(...) or B == Or(...)
  # return: a, b  or throw an exception if self is not of the appropriate form.
  def factor_index(self, index):
    raise Exception("Abstract superclass.")

  def __eq__(self, other):
    return isinstance(other, Formula) and self.translate() == other.translate()
  def __ne__(self, other):
    return not (self == other)

  def render(self, context):
    return gl.newTextualGLStack(colors.genericColor, repr(self))

  def substituteVariable(self, a, b):
    raise Exception("Abstract superclass.")

  def updateVariables(self):
    raise Exception("Abstract superclass.")

class Arrow:
  def __init__(self, src, tgt, basicArrow):
    self.src = src
    self.tgt = tgt
    self.basicArrow = basicArrow
  def translate(self):
    return self.basicArrow

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
      holds =  stack.stackAll(0, [ renderVariable(aVariable, bindings)
                                 , renderVariable(self.holding, bindings)
                                 , renderVariable(bVariable, bindings)],
                                 spacing = distances.infixSpacing)
    else:
      holds = stack.stackAll(0, [ renderVariable(self.held, bindings)
                                , primitives.holds()
                                , renderVariable(self.holding, bindings)],
                                spacing = distances.holdsSpacing)

    return holds

  def substituteVariable(self, a, b):
    return Holds(held = self.held.substituteVariable(a, b),
        holding = self.holding.substituteVariable(a, b))

  def updateVariables(self):
    return self

class Application(Formula):
  def __init__(self, formula, endofunctor):
    if not(isinstance(formula, Formula)):
      raise Exception(("Application was given something other than an enriched"
          + " Formula.  Got %s")%(formula,))
    self.formula = formula
    self.endofunctor = endofunctor

  def __repr__(self):
    return "Apply %s to %s"%(self.endofunctor, self.formula)

  def factor_index(self, index):
    if is_identity_functor(self.endofunctor):
      return self.formula.factor_index(index)
    else:
      a, b = self.endofunctor.factor_right()
      if b.__class__ == And or b.__class__ == Or:
        return (Application(formula = self.formula, endofunctor = a), b)
      else:
        raise Exception("The given endofunctor did not factor properly.")

  def render(self, context):
    return self.endofunctor.renderOn(context, lambda context:
        formula.render(context))

  def translate(self):
    return self.endofunctor.translate().onObject(self.formula.translate())

  def substituteVariable(self, a, b):
    return Application(endofunctor = self.endofunctor.substituteVariable(a, b),
        formula = self.formula.substituteVariable(a, b))

  def updateVariables(self):
    return Application(endofunctor = self.endofunctor.updateVariables(),
        formula = self.formula.updateVariables())

class Conjunction(Formula):
  def __init__(self, values):
    for i in range(len(values)):
      value = values[i]
      if not(isinstance(value, Formula)):
        raise Exception("%s at index %s is not an enriched formula."%(value, i))
    self.values = values
    self.basicBinop = self.basicBinop()

  # index: an index
  #   self must be equivalent to a functor of the form a o b where
  #   b == And(...) or B == Or(...)
  # return: a, b  or throw an exception if self is not of the appropriate form.
  def factor_index(self, index):
    #FIXME
    assert(False)
    return 

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
      length = max(length, s.widths[other_dimension])
      values.apppend(s)
    return stack.stackAll(dimension,
        _interleave(self.renderDivider(context.covariant, length), values),
        spacing = distances.divider_spacing)

class And(Conjunction):
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
    res = render(self.left, kid_context).stack(0,
        primitives.iff(),
        spacing = distances.iffSpacing).stack(0,
            render(self.right, kid_context),
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
            basicFormula.Not(EqualUnder(self.newVariable, self.variable, self.equivalence)))))
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
  def __init__(self, covariant, bindings):
    self.covariant = covariant
    self.bindings = bindings

  def bind(self, key, value):
    bindings = dict(self.bindings)
    bindings[key] = value
    return RenderingContext(covariant = self.covariant, bindings = bindings)

  def negate(self):
    return RenderingContext(covariant = not self.covariant, bindings = self.bindings)

  def as_covariant(self):
    return self if self.covariant else self.negate()

def InDomain(x, e):
  return Holds(x, variable.ProjectionVariable(e, domainSymbol))

def EqualUnder(a, b, e):
  return Holds(
      variable.ProductVariable([(leftSymbol, a), (rightSymbol, b)]),
      variable.ProjectionVariable(e, relationSymbol))
