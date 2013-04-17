# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol

from sets import Set

class Object:
  # Always returns a "basic" object.
  def translate(self):
    raise Exception("Abstract superclass.")

  def updateVariables(self):
    raise Exception("Abstract superclass.")

  def substituteVariable(self, a, b):
    raise Exception("Abstract superclass.")

  def freeVariables(self):
    raise Exception("Abstract superclass.")

  def forwardDoubleDual(self):
    return DoubleDual(src = self, tgt = Not(Not(self)))

  def forwardAssume(self, a):
    return self.forwardDoubleDual().forwardFollow(lambda x:
        x.forwardOnNotFollow(lambda x:
          x.backwardApply(a)))

  def forwardAndTrue(self):
    return UnitIdentity(src = self, tgt = And(left = true, right = self))

  def identity(self):
    return Id(src = self, tgt = self)

n_variables = 0
class Variable(Object):
  def __init__(self):
    self._generate_id()

  def _generate_id(self):
    global n_variables
    self._id = n_variables
    n_variables += 1

  def translate(self):
    return self

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

class Exists(Object):
  def __init__(self, variables, value):
    self.variables = variables
    self.value = value

  def __eq__(self, other):
    return (self.__class__ == other.__class__
        and self.variables == other.variables
        and self.value == other.value)

  def __ne__(self, other):
    return not(self == other)

  def __repr__(self):
    return "( Exists %s . %s )"%(self.variables, self.value)

  def translate(self):
    return Exists(variables = [variable.translate() for variable in self.variables],
        value = self.value.translate())

  def updateVariables(self):
    variables = [variable.updateVariables() for variable in self.variables]
    return self.__class__(variables = variables,
        value = self.value.substituteVariable(
          self.variable, variable).updateVariables())

  def substituteVariable(self, a, b):
    assert(a not in self.variables)
    assert(b not in self.variables)
    return self.__class__(variables = self.variables,
        value = self.value.substituteVariable(a, b))

  def freeVariables(self):
    return self.value.freeVariables().difference(Set(self.variables))

empty_symbol = symbol.StringSymbol('')
right_symbol = empty_symbol

# For And and Or.
class Conjunction(Object):
  # There is only one global right symbol.
  def __init__(self, left, right, left_symbol = empty_symbol,
      right_symbol = empty_symbol):
    self.left = left
    self.left_symbol = left_symbol
    self.right = right
    self.right_symbol = right_symbol

  def __eq__(self, other):
    return (self.__class__ == other.__class__
        and self.left == other.left
        and self.right == other.right)
  def __ne__(self, other):
    return not(self == other)

  def translate(self):
    return self.__class__(left_symbol = self.left_symbol, left = self.left.translate(),
                          right_symbol = self.right_symbol, right = self.right.translate())

  def updateVariables(self):
    return self.__class__(left_symbol = self.left_symbol,
        right_symbol = right_symbol,
        left = self.left.updateVariables(),
        right = self.right.updateVariables())

  def substituteVariable(self, a, b):
    return self.__class__(left_symbol = self.left_symbol,
        right_symbol = right_symbol,
        left = self.left.substituteVariable(a, b),
        right = self.right.substituteVariable(a, b))

  def freeVariables(self):
    return self.left.freeVariables().union(self.right.freeVariables())

class Intersect(Object):
  def __init__(self, left, right):
    self.left = left
    self.right = right

  def __repr__(self):
    return "(%s INTERSECT %s)"%(self.left, self.right)

  def __eq__(self, other):
    return (self.__class__ == other.__class__
       and self.left == other.left
       and self.right == other.right)

  def __ne__(self, other):
    return not(self == other)

  def translate(self):
    return Intersect(left = self.left.translate(), right = self.right.translate())

  def updateVariables(self):
    return self.__class__(left = self.left.updateVariables(),
        right = self.right.updateVariables())

  def substituteVariable(self, a, b):
    return self.__class__(left = self.left.substituteVariable(a, b),
        right = self.right.substituteVariable(a, b))

  def freeVariables(self):
    return self.left.freeVariables().union(self.right.freeVariables())

class And(Conjunction):
  def forwardApply(self):
    assert(self.right.__class__ == Not)
    assert(self.right.value.__class__ == And)
    return Apply(src = self, tgt = Not(self.right.value.right))

  def __repr__(self):
    return "(%s AND %s)"%(self.left, self.right)

class Or(Conjunction):
  def __repr__(self):
    return "(%s OR %s)"%(self.left, self.right)

class Not(Object):
  def __init__(self, value, rendered = False):
    self.value = value
    self.rendered = rendered

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.value == other.value
  def __ne__(self, other):
    return not(self == other)

  def __repr__(self):
    return "~(%s)"%(self.value,)

  def translate(self):
    return Not(value = self.value.translate(), rendered = self.rendered)

  def forwardOnNot(self, arrow):
    assert(arrow.tgt == self.value)
    return OnNot(arrow)
  def forwardOnNotFollow(self, f):
    return self.forwardOnNot(f(self.value))

  def backwardOnNot(self, arrow):
    assert(arrow.src == self.value)
    return OnNot(arrow)
  def backwardOnNotFollow(self, f):
    return self.backwardOnNot(f(self.value))

  def backwardDoubleDual(self):
    assert(self.value.__class__ == Not)
    return self.value.value.forwardDoubleDual()

  def backwardApply(self, a):
    return Apply(src = And(left = a, right = Not(And(left = a, right = self.value))),
                 tgt = self)

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

  def __repr__(self):
    return "!(%s)"%(self.value)

  def translate(self):
    return Always(value = self.value.translate())

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

  def translate(self):
    return self

  def updateVariables(self):
    return self

  def substituteVariable(self, a, b):
    return self

  def freeVariables(self):
    return Set()

class AndUnit(Unit):
  def __repr__(self):
    return "1"

class OrUnit(Unit):
  def __repr__(self):
    return "0"

true = AndUnit()
false = OrUnit()

def unit_for_conjunction(conjunction):
  if conjunction == And:
    return true
  else:
    assert(conjunction == Or)
    return false


class Destructor(Object):
  def __init__(self, value, symbol):
    self.value = value
    self.symbol = symbol
    self.validate()

  def validate(self):
    return

  def translate(self):
    return self.__class__(value = self.value.translate(), symbol = self.symbol)

  def __eq__(self, other):
    return (self.__class__ == other.__class__
        and self.symbol == other.symbol
        and self.value == other.value)

  def __ne__(self, other):
    return not(self == other)

  def updateVariables(self):
    return self.__class__(value = self.value.updateVariables(),
        symbol = self.symbol.updateVariables())

  def substituteVariable(self, a, b):
    return self.__class__(value = self.value.substituteVariable(a, b),
        symbol = self.symbol.substituteVariable(a, b))

  def freeVariables(self):
    return self.value.freeVariables()

class Project(Destructor):
  def __repr__(self):
    return "%s_._%s"%(self.value, self.symbol)

class Inject(Destructor):
  def __repr__(self):
    return "%s_inject_%s"%(self.value, self.symbol)

class Coinject(Destructor):
  def __repr__(self):
    return "%s_o_%s"%(self.value, self.symbol)

class Arrow:
  def __init__(self, src, tgt):
    self.src = src
    self.tgt = tgt
    self.validate()

  def translate(self):
    return self.__class__(src = self.src.translate(), tgt = self.tgt.translate())

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

  def forwardCompose(self, other):
    assert(isinstance(other, Arrow))
    return Composite(left = self, right = other)
  def backwardCompose(self, other):
    assert(isinstance(other, Arrow))
    return Composite(right = self, left = other)
  def forwardFollow(self, f):
    return self.forwardCompose(f(self.tgt))
  def backwardFollow(self, f):
    return self.backwardCompose(f(self.src))

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

  def translate(self):
    return InverseArrow(arrow = self.arrow.translate())

# A <--> A
class Id(Arrow):
  def validate(self):
    # FIXME Remove
    if not(self.src == self.tgt):
      raise Exception("Id arrow between different things \n%s\n!=\n%s"%(self.src, self.tgt))

# A --> B --> C
class Composite(Arrow):
  def __init__(self, left, right):
    self.left = left
    self.right = right
    self.src = left.src
    self.tgt = right.tgt
    self.validate()

  def translate(self):
    return Composite(left = self.left.translate(), right = self.right.translate())

  # Throw an exception if self is not valid.
  # Subclasses should override to implement checking.
  def validate(self):
    assert(self.left.tgt == self.right.src)

  # May throw an exception.
  def invert(self):
    return Composite(left = self.right.invert(), right = self.left.invert())

  def __eq__(self, other):
    return (self.__class__ == other.__class__
        and self.left == other.left
        and self.right == other.right)

  def __ne__(self, other):
    return not(self == other)


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

        and self.src.left.left == self.tgt.right
        and self.src.left.right == self.tgt.right.left
        and self.src.right == self.tgt.right.right)

# A % 1 <-- A --> 1 % A
class UnitIdentity(Isomorphism):
  def validate(self):
    unit = unit_for_conjunction(self.tgt.__class__)
    assert((self.tgt.right == unit and self.tgt.left == self.src)
        or (self.tgt.left == unit and self.tgt.right == self.src))

# A <--> ~(~A)
class DoubleDual(Isomorphism):
  def validate(self):
    assert(self.tgt.__class__ == Not)
    assert(self.tgt.value.__class__ == Not)
    assert(self.src == self.tgt.value.value)

# A | ~(A | B) --> ~B
class Apply(Arrow):
  def validate(self):
    assert(self.tgt.__class__ == Not)
    assert(self.src.__class__ == And)
    assert(self.src.right.__class__ == Not)
    assert(self.src.right.value.__class__ == And)
    assert(self.src.left == self.src.right.value.left)
    assert(self.src.right.value.right == self.tgt.value)

# For arrow built from the application of functors to other arrows.
class FunctorialArrow(Arrow):
  def translate(self):
    raise Exception("Abstract superclass.")

class OnNot(FunctorialArrow):
  def __init__(self, arrow):
    self.arrow = arrow
    self.src = Not(arrow.tgt)
    self.tgt = Not(arrow.src)

  def translate(self):
    return OnNot(arrow = self.arrow.translate())

