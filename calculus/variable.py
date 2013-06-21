# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from sets import Set

class GeneralizedVariable:
  # Return an equivalent variable that is possibly simpler.
  def simplify(self):
    return self

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

  def name(self):
    return self._name

  def __repr__(self):
    return self.name()

  def updateVariables(self):
    return StringVariable(self.name())

class InjectionVariable(GeneralizedVariable):
  def __init__(self, variable, symbol):
    self.variable = variable
    self.symbol = symbol
  def __eq__(self, other):
    return (other.__class__ == InjectionVariable
        and self.variable == other.variable
        and self.symbol == other.symbol)
  def __ne__(self, other):
    return not (self == other)
  def __repr__(self):
    return "<: " + repr(self.variable) + " :: " + repr(self.symbol) + " :>"
  def updateVariables(self):
    return InjectionVariable(variable = self.variable.updateVariables(), symbol = self.symbol)
  def substituteVariable(self, a, b):
    return InjectionVariable(variable = self.variable.substituteVariable(a, b), symbol = self.symbol)
  def freeVariables(self):
    return self.variable.freeVariables()

class ProjectionVariable(GeneralizedVariable):
  def __init__(self, variable, symbol):
    self.variable = variable
    self.symbol = symbol
  def __eq__(self, other):
    return (other.__class__ == ProjectionVariable
        and self.variable == other.variable
        and self.symbol == other.symbol)
  def __ne__(self, other):
    return not (self == other)
  def __repr__(self):
    return repr(self.variable) + "." + repr(self.symbol)
  def updateVariables(self):
    return InjectionVariable(variable = self.variable.updateVariables(), symbol = self.symbol)
  def substituteVariable(self, a, b):
    return InjectionVariable(variable = self.variable.substituteVariable(a, b), symbol = self.symbol)
  def freeVariables(self):
    return self.variable.freeVariables()
  def simplify(self):
    if self.variable.__class__ == ProductVariable:
      for (symbol, variable) in self.variable.symbol_variable_pairs:
        if symbol == self.symbol:
          return variable
      raise Exception(("Failed to simplify %s because the product variable " +
          "did not contain the component projected upon.")%(self,))
    else:
      return ProjectionVariable(variable = self.variable.simplify(), symbol = self.symbol)

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

