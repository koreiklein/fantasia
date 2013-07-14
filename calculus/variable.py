# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from sets import Set
from calculus import symbol

from ui.render.text import primitives, colors, distances
from ui.stack import stack

class GeneralizedVariable:
  # Return an equivalent variable that is possibly simpler.
  def simplify(self):
    return self
  def render(self):
    raise Exception("Abstract superclass.")

n_variables = 0
class Variable(GeneralizedVariable):
  def __init__(self):
    self._generate_id()

  def _generate_id(self):
    global n_variables
    self._id = n_variables
    n_variables += 1

  def updateVariables(self):
    return Variable()

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self._id == other._id
  def __ne__(self, other):
    return not(self == other)
  def __hash__(self):
    return hash(self._id)

  def __repr__(self):
    return "<abstract variable %s>"%(self._id,)

  def substituteVariable(self, a, b):
    if self == a:
      return b
    else:
      return self

  def freeVariables(self):
    return Set([self])

class StringVariable(Variable):
  # infix: either None, or a pair of symbols (a, b) such that when this variable holds
  #        of a variable v, v is a product variable over symbols a and b.
  def __init__(self, name, infix = None):
    self._generate_id()
    self._name = name
    self.infix = infix

  def render(self):
    return primitives.newTextStack(colors.variableColor, repr(self))

  def name(self):
    return self._name

  def __repr__(self):
    return self.name()

  def updateVariables(self):
    return StringVariable(self.name())

def renderInfix(productVariable, infixSymbols, infixVariable):
  (firstSymbol, secondSymbol) = infixSymbols
  assert(len(productVariable.symbol_variable_pairs) == 2)
  (aSymbol, aVariable) = productVariable.symbol_variable_pairs[0]
  (bSymbol, bVariable) = productVariable.symbol_variable_pairs[1]
  if aSymbol == secondSymbol:
    assert(bSymbol == firstSymbol)
    (firstSymbol, secondSymbol) = (secondSymbol, firstSymbol)
  else:
    assert(aSymbol == firstSymbol)
    assert(bSymbol == secondSymbol)
  return stack.stackAll(0, [ aVariable.render()
                           , infixVariable.render()
                           , bVariable.render()],
                           spacing = distances.infixSpacing)

class ApplySymbolVariable(GeneralizedVariable):
  def __init__(self, variable, symbol):
    self.variable = variable
    self.symbol = symbol
  def __eq__(self, other):
    return (other.__class__ == ApplySymbolVariable
        and self.variable == other.variable
        and self.symbol == other.symbol)
  def __ne__(self, other):
    return not (self == other)
  def __repr__(self):
    return "<: " + repr(self.variable) + " :: " + repr(self.symbol) + " :>"
  def updateVariables(self):
    return ApplySymbolVariable(variable = self.variable.updateVariables(), symbol = self.symbol)
  def substituteVariable(self, a, b):
    return ApplySymbolVariable(variable = self.variable.substituteVariable(a, b), symbol = self.symbol)
  def freeVariables(self):
    return self.variable.freeVariables()

  def render(self):
    symbolBackgroundColor, variableBackgroundColor = colors_for_symbol(self.symbol)
    if isinstance(self.symbol, Variable):
      if self.symbol.infix is not None:
        return renderInfix(self.variable, self.symbol.infix, self.symbol)
      else:
        symbolStack = self.symbol.render()
        return self.variable.render().stack(0, primitives.dot).stack(0, symbolStack)
    else:
      symbolStack = renderSymbol(self.symbol)
      return self.variable.render().stack(0, primitives.dot).stack(0, symbolStack)

def colors_for_symbol(symbol):
  if isinstance(symbol, Variable):
    return (colors.callSymbolBackgroundColor, colors.callVariableBackgroundColor)
  else:
    return (colors.symbolBackgroundColor, colors.symbolForegroundColor)

# A more elaborate syntax for VARIABLES!!! These construct are under no means
# meant to be used for objects, nether have they any sort of computational manifestation.
# They are ENTIRELY FOR BOOKEEPING.
class ProductVariable(GeneralizedVariable):
  def __init__(self, symbol_variable_pairs):
    self.symbol_variable_pairs = symbol_variable_pairs

  def __eq__(self, other):
    return (other.__class__ == ProductVariable
        and self.symbol_variable_pairs == other.symbol_variable_pairs)
  def __ne__(self, other):
    return not(self == other)
  def __repr__(self):
    return "{" + ", ".join([repr(s) + ": " + repr(v) for (s,v) in self.symbol_variable_pairs]) + "}"
  def updateVariables(self):
    return ProductVariable(
        symbol_variable_pairs = [(s, v.updateVariables()) for (s,v) in self.symbol_variable_pairs])
  def substituteVariable(self, a, b):
    return ProductVariable(
        symbol_variable_pairs = [(s, v.substituteVariable(a, b))
                                 for (s,v) in self.symbol_variable_pairs])
  def freeVariables(self):
    result = Set()
    for (s, v) in self.symbol_variable_pairs:
      result.union_update(v.freeVariables())
    return result

  def render(self):
    symbolVariablePairs = []
    for i in range(len(self.symbol_variable_pairs)):
      (s,v) = self.symbol_variable_pairs[i]
      (c0, c1) = colors.productPairsColor(i)
      symbolVariablePairs.append(renderSymbolVariablePair(renderSymbol(s),
        v.render(), c0, c1))
    return stack.stackAll(0, symbolVariablePairs,
        spacing = distances.productVariableHorizontalSpacing)

def renderSymbolVariablePair(s, v, c0, c1):
  widths = [max(s.widths()[0], v.widths()[0]) , 0.0, 0.0]
  return borderStack(1
                    , colors.symbolVariablePairBorderColor
                    , renderWithBackground(s.atLeast(widths),
                        distances.symbolBackgroundBorderWidth, c0)
                    , renderWithBackground(v.atLeast(widths),
                        distances.variableBackgroundBorderWidth, c1)
                    , distances.productVariableBorder)

def borderStack(dimension, color, a, b, borderWidth):
  return renderWithBackground(a.stack(dimension, b, spacing = borderWidth), borderWidth, color)

def renderSymbol(s):
  if s.__class__ == symbol.StringSymbol:
    return renderStringSymbol(s)
  else:
    raise Exception("Unrecognized symbol %s"%(s,))

def renderStringSymbol(s):
  return primitives.newTextStack(colors.symbolColor, repr(s))

def renderWithBackground(s, border_width, color):
  if s.uses_epsilon():
    widths = [x + 2 * border_width for x in s.widths()]
    widths[2] = 0.0
    return primitives.solidSquare(color, widths).stackCentered(2, s,
        spacing = distances.epsilon )
  else:
    return s

