# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol, variable

from sets import Set

class Object:
  def updateVariables(self):
    raise Exception("Abstract superclass.")

  def substituteVariable(self, a, b):
    raise Exception("Abstract superclass.")

  def freeVariables(self):
    raise Exception("Abstract superclass.")

n_variables = 0
class Variable(Object):
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
  def __init__(self, name):
    self._generate_id()
    self._name = name

  def name(self):
    return self._name

  def __repr__(self):
    return self.name()

  def updateVariables(self):
    return StringVariable(self.name())

right_symbol = symbol.StringSymbol('')

# For And and Or.
class Conjunction(Object):
  # There is only one global right symbol.
  def __init__(self, left_symbol, left, right):
    self.left = left
    self.left_symbol = left_symbol
    self.right = right

  def __eq__(self, other):
    return (self.__class__ == other.__class__
        and self.left == other.left
        and self.left_symbol == other.left_symbol
        and self.right == other.right)
  def __ne__(self, other):
    return not(self == other)

  def updateVariables(self):
    return self.__class__(left_symbol = self.left_symbol,
        left = self.left.updateVariables(),
        right = self.right.updateVariables())

  def substituteVariable(self, a, b):
    return self.__class__(left_symbol = self.left_symbol,
        left = self.left.substituteVariable(a, b),
        right = self.right.substituteVariable(a, b))

  def freeVariables(self):
    return self.left.freeVariables().union(self.right.freeVariables())

# Multiple conjunction will be represented (a | (b | (c | 1)))
def multiple_conjunction(conjunction, symbol_value_pairs):
  result = unit_for_conjunction(conjunction)
  for (symbol, value) in symbol_value_pairs[::-1]:
    result = conjunction(left_symbol = symbol, left = value, right = result)
  return result

class Destructor(Object):
  def __init__(self, value, symbol):
    self.value = value
    self.symbol = symbol
    self.validate()

  def validate(self):
    return

  def updateVariables(self):
    return self.__class__(value = self.value.updateVariables(),
        symbol = self.symbol.updateVariables())

  def substituteVariable(self, a, b):
    return self.__class__(value = self.value.substituteVariable(a, b),
        symbol = self.symbol.substituteVariable(a, b))

  def freeVariables(self):
    return self.value.freeVariables()

class Project(Destructor):
  pass

class Inject(Destructor):
  pass

def MultiAnd(symbol_value_pairs):
  return multiple_conjunction(And, symbol_value_pairs)
def MultiOr(symbol_value_pairs):
  return multiple_conjunction(Or, symbol_value_pairs)

class Intersect(Object):
  def __init__(self, left, right):
    self.left = left
    self.right = right

  def __eq__(self, other):
    return (self.__class__ == other.__class__
       and self.left == other.left
       and self.right == other.right)

  def __ne__(self, other):
    return not(self == other)

  def updateVariables(self):
    return self.__class__(left = self.left.updateVariables(),
        right = self.right.updateVariables())

  def substituteVariable(self, a, b):
    return self.__class__(left = self.left.substituteVariable(a, b),
        right = self.right.substituteVariable(a, b))

  def freeVariables(self):
    return self.left.freeVariables().union(self.right.freeVariables())

class And(Conjunction):
  pass

class Or(Conjunction):
  pass

class Not(Object):
  def __init__(self, value, rendered = False):
    self.value = value
    self.rendered = rendered

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.value == other.value
  def __ne__(self, other):
    return not(self == other)

  def updateVariables(self):
    return self.__class__(value = self.value.updateVariables(),
        rendered = self.rendered)

  def substituteVariable(self, a, b):
    return self.__class__(value = self.value.substituteVariable(a, b),
        rendered = self.rendered)

  def freeVariables(self):
    return self.value.freeVariables()

class Always(Object):
  def __init__(self, value):
    self.value = value

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.value == other.value
  def __ne__(self, other):
    return not(self == other)

  def updateVariables(self):
    return self.__class__(value = self.value.updateVariables())

  def substituteVariable(self, a, b):
    return self.__class__(value = self.value.substituteVariable(a, b))

  def freeVariables(self):
    return self.value.freeVariables()

class Unit(Object):
  def __eq__(self, other):
    return self.__class__ == other.__class__
  def __ne__(self, other):
    return not(self == other)

  def updateVariables(self):
    return self

  def substituteVariable(self, a, b):
    return self

  def freeVariables(self):
    return Set()

class AndUnit(Unit):
  pass

class OrUnit(Unit):
  pass

true = AndUnit()
false = OrUnit(true)

def unit_for_conjunction(conjunction):
  if conjunction == And:
    return true
  else:
    assert(conjunction == Or)
    return false

class Arrow:
  def __init__(self, src, tgt):
    self.src = src
    self.tgt = tgt
    self.validate()

  # Throw an exception if self is not valid.
  # Subclasses should override to implement checking.
  def validate(self):
    return

  def invert(self):
    raise Exception("The following arrow is not invertible: %s"%(self,))

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.src == other.src and self.tgt == other.tgt
  def __ne__(self, other):
    return not(self == other)

class Isomorphism(Arrow):
  def invert(self):
    return InverseArrow(self)

class InverseArrow(Isomorphism):
  def __init__(self, arrow):
    self.arrow = arrow
    self.src = arrow.src
    self.tgt = arrow.tgt

  def invert(self):
    return self.arrow

class Commute(Isomorphism):
  def validate(self):
    assert(self.src.__class__ == self.tgt.__class__)

  def invert(self):
    return Commute(src = self.tgt, tgt = self.src)

# (A % B) % C ---> A % (B % C)
class Associate(Isomorphism):
  def validate(self):
    assert(isinstance(self.src, Conjunction))
    assert(self.tgt.__class__ == self.src.__class__)
    assert(self.a() or self.b())
    common_class == self.src.__class__
    assert (self.src.left.__class__ == common_class
        and self.tgt.right.__class__ == common_class

        and self.src.left.left = self.tgt.right
        and self.src.left.right = self.tgt.right.left
        and self.src.right = self.tgt.right.right)

# A % 1 <-- A --> 1 % A
class UnitIdentity(Isomorphism):
  def validate(self):
    unit = unit_for_conjunction(self.tgt)
    assert((self.tgt.right == unit and self.tgt.left == self.src)
        or (self.tgt.left == unit and self.tgt.right == self.src))

