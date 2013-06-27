# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.variable import Variable
from calculus.basic import formula as basicFormula
from lib.equivalence import InDomain, EqualUnder

class Formula:
  def translate(self):
    raise Exception("Abstract superclass.")

  def __eq__(self, other):
    return isinstance(other, Formula) and self.translate() == other.translate()
  def __ne__(self, other):
    return not (self == other)

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

class Application(Formula):
  def __init__(self, endofunctor, formula):
    self.endofunctor = endofunctor
    self.formula = formula

  def translate(self):
    return self.endofunctor.translate().onObject(self.formula)

  def substituteVariable(self, a, b):
    return Application(endofunctor = self.endofunctor.substituteVariable(a, b),
        formula = self.formula.substituteVariable(a, b))

  def updateVariables(self):
    return Application(endofunctor = self.endofunctor.updateVariables(),
        formula = self.formula.updateVariables())

class Conjunction(Formula):
  def __init__(self, values):
    self.values = values
    self.basicBinop = self.basicBinop()

  def translate(self):
    return basicFormula.multiple_conjunction(conjunction = self.basicBinop,
        values = [value.translate() for value in self.values])

  def substituteVariable(self, a, b):
    return self.__class__(values = [v.substituteVariable(a, b) for v in self.values])

  def updateVariables(self):
    return self.__class__(values = [v.updateVariables() for v in self.values])

class And(Conjunction):
  def basicBinop(self):
    return basicFormula.And

class Or(Conjunction):
  def basicBinop(self):
    return basicFormula.Or

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

class Hidden(Formula):
  def __init__(self, base, name):
    self.base = base
    self.name = name

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

