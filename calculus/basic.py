# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import types
# Backend objects and arrows for the basic logic category.
# Implement only the primitive objects and arrows, derived forms go in a separate enriched
# calculus.

n_vars = 0

class Var:
  def __init__(self, name):
    global n_vars
    self._id = n_vars
    n_vars += 1
    self._name = name

  def name(self):
    return self._name

  def assertEqual(self, other):
    assert(self == other)

  def __repr__(self):
    return self.name()

  def __eq__(self, other):
    return other.__class__ == Var and self._id == other._id
  def __ne__(self, other):
    return not (self == other)

  def __hash__(self):
    return hash(self._id)

# Objects

andType = "AND"
orType = "OR"

class PrimitiveObject:
  # Replace all occurences of a with b in self and return the result.
  # a must not be quantified anywhere in self.
  def substituteVar(self, a, b):
    raise Exception("Abstract superclass.")
  # Return a copy of self, but with all it's quantified variables
  # replaced with new ones.
  def updateVars(self):
    raise Exception("Abstract superclass.")
  # For debugging.  If you call this method with an unequal object, it should produce
  # a usefull stracktrace that explain HOW the objects are unequal.
  def assertEqual(self):
    raise Exception("Abstract superclass.")
  def forwardIntroduceDoubleDual(self):
    return IntroduceDoubleDual(self)
  def backwardRemoveDoubleDual(self):
    return RemoveDoubleDual(self)
  def forwardIntroduceTrue(self):
    return IntroduceTrue(value = self)
  def backwardRemoveFalse(self):
    return RemoveFalse(value = self)
  def forwardAdmit(self, b):
    return Admit(self, b)
  def backwardForget(self, b):
    return Forget(self, b)
  def backwardForgetFirst(self, b):
    return self.backwardForget(b).backwardFollow(lambda x: x.backwardCommute())
  def backwardEliminateVar(self, quantifiedVar, replacementVar):
    return Eliminate(value = self.substituteVar(replacementVar, quantifiedVar),
        quantifiedVar = quantifiedVar, replacementVar = replacementVar)
  def identity(self):
    return Identity(self)
  def forwardIdentity(self):
    return Identity(self)
  def backwardIdentity(self):
    return Identity(self)

class Holds(PrimitiveObject):
  def __init__(self, **kwargs):
    self._d = kwargs
    for (key, value) in kwargs.items():
      self.__dict__[key] = types.MethodType(lambda self: value, self)

  def __getitem__(self, x):
    return self._d[x]

  def __eq__(self, other):
    if other.__class__ != Holds:
      return False
    else:
      for (key, value) in self._d.items():
        if (not other._d.has_key(key) ) or other[key] != value:
          return False
      for (key, value) in other._d.items():
        if (not self._d.has_key(key) ) or self[key] != value:
          return False
      return True

  def assertEqual(self, other):
    assert(other.__class__ == Holds)
    for (key, value) in self._d.items():
      assert(other[key] == value)
    for (key, value) in other._d.items():
      assert(self[key] == value)

  def __ne__(self, other):
    return not (self == other)

  def updateVars(self):
    return self

  def substituteVar(self, a, b):
    _d = {}
    for (key, value) in self._d.items():
      if value == a:
        _d[key] = b
      else:
        _d[key] = value
    return Holds(**_d)

forallType = "FORALL"
existsType = "EXISTS"

def dualQuantifierType(type):
  if type == forallType:
    return existsType
  else:
    assert(type == existsType)
    return forallType

quantifierTypes = [forallType, existsType]

class Quantifier(PrimitiveObject):
  def __init__(self, var, body, type):
    assert(type in quantifierTypes)
    self._var = var
    self._body = body
    self._type = type

  def __repr__(self):
    return "< %s %s . %s >"%(self.type(), self.var(), self.body())

  def substituteVar(self, a, b):
    assert(a != self.var())
    return Quantifier(var = self.var(), type = self.type(),
        body = self.body().substituteVar(a, b))

  def assertEqual(self, other):
    assert(other.__class__ == Quantifier)
    if self.var() != other.var():
      raise Exception(("Unequal vars %s != %s,"
        + " in\n%s\n\tCOMPARED TO\n%s")%(self.var(), other.var(), self, other))
    self.body().assertEqual(other.body())

  def updateVars(self):
    a = self.var()
    b = Var(a.name())
    return Quantifier(var = b, body = body.substituteVar(a, b).updateVars())

  def var(self):
    return self._var
  def body(self):
    return self._body
  def type(self):
    return self._type

  # We use a liberal definition of equality.
  # Two claims are equal if they can be made equal through substitution of
  # variables.
  def __eq__(self, other):
    if other.__class__ != Quantifier or self.type() != other.type():
      return False
    else:
      if self.var() == other.var():
        return self.body() == other.body()
      else:
        return self.body() == other.body().substituteVar(other.var(), self.var())
  def __ne__(self, other):
    return not (self == other)

  def forwardUnusedQuantifier(self):
    # TODO Check that self.var() is not free in self.body()
    return UnusedQuantifier(variable = self.var(), type = self.type(), body = self.body())

  def backwardConjQuantifier(self):
    # (Q x . A) % B --> Q x . (A % B)
    assert(self.body().__class__ == Conj)
    if self.type() == forallType:
      assert(self.body().type() == orType)
    else:
      assert(self.type() == existsType)
      assert(self.body().type() == andType)

    return ConjQuantifier(quantifierType = self.type(), conjType = self.body().type(),
        var = self.var(), left = self.body().left(), right = self.body().right())

  def forwardQuantifierConj(self):
    # Q x . (A % B) --> (Q x . A) % (Q x . B)
    assert(self.left().__class__ == Quantifier)
    assert(self.right().__class__ == Quantifier)
    assert(self.left().var() == self.right().var())
    if self.type() == andType:
      assert(self.left().type() == existsType)
      assert(self.right().type() == existsType)
    else:
      assert(self.type() == orType)
      assert(self.left().type() == forallType)
      assert(self.right().type() == forallType)

    return QuantifierConj(quantifierType = self.type(), conjType = self.left().type(),
        var = self.left().var(), left = self.left().body(), right = self.right().body())

  def backwardNotQuant(self):
    assert(self.body().__class__ == Not)
    return NotQuant(variable = self.var(), type = dualQuantifierType(self.type()),
        value = self.body().value())

  def forwardEliminateVar(self, replacementVar):
    assert(self.type() == forallType)
    return Eliminate(value = self.body(),
        quantifiedVar = self.var(),
        replacementVar = replacementVar)

  def forwardOnBody(self, arrow):
    assert(self.body() == arrow.src())
    return OnBody(arrow = arrow, var = self.var(), type = self.type())
  def backwardOnBody(self, arrow):
    assert(self.body() == arrow.tgt())
    return OnBody(arrow = arrow, var = self.var(), type = self.type())

  # f is a function taking self.body() to an arrow other such that self.forwardOnBody(other) exists.
  def forwardOnBodyFollow(self, f):
    return self.forwardOnBody(f(self.body()))
  # f is a function taking self.body() to an arrow other such that self.backwardOnBody(other) exists.
  def backwardOnBodyFollow(self, f):
    return self.backwardOnBody(f(self.body()))

class TrueClass(PrimitiveObject):
  def __init__(self):
    pass

  def substituteVar(self, a, b):
    return self

  def assertEqual(self, other):
    assert(self.__class__ == other.__class__)

  def updateVars(self):
    return self

  def __repr__(self):
    return "1"

  def __eq__(self, other):
    return self.__class__ == other.__class__
  def __ne__(self, other):
    return not (self == other)

class Not(PrimitiveObject):
  def __init__(self, value):
    self._value = value

  def __repr__(self):
    return "~( %s )"%(self.value(),)

  def substituteVar(self, a, b):
    return Not(self.value().substituteVar(a, b))

  def updateVars(self):
    return Not(self.value().updateVars())

  def value(self):
    return self._value

  def assertEqual(self, other):
    assert(other.__class__ == Not)
    self.value().assertEqual(other.value())

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.value() == other.value()
  def __ne__(self, other):
    return not (self == other)

  def forwardRemoveDoubleDual(self):
    assert(self.value().__class__ == Not)
    return RemoveDoubleDual(self.value().value())
  def backwardIntroduceDoubleDual(self):
    assert(self.value().__class__ == Not)
    return IntroduceDoubleDual(self.value().value())

  def backwardApply(self, b):
    # | A | B  | B  --->  | A
    # *------  |          *--
    return Apply(a = self.value(), b = b)

  def forwardNotQuant(self):
    assert(self.value().__class__ == Quantifier)
    return NotQuant(variable = self.value().var(), type = self.value().type(),
        value = self.value().value())

  # src and tgt go the opposite direction since Not is contravariant.
  def forwardOnNot(self, arrow):
    assert(arrow.tgt() == self.value())
    return OnNot(arrow)
  def backwardOnNot(self, arrow):
    assert(arrow.src() == self.value())
    return OnNot(arrow)

  # f is a function taking self.value() to an arrow other such that self.forwardOnNot(other) exists.
  def forwardOnNotFollow(self, f):
    return self.forwardOnNot(f(self.value()))
  # f is a function taking self.value() to an arrow other such that self.backwardOnNot(other) exists.
  def backwardOnNotFollow(self, f):
    return self.backwardOnNot(f(self.value()))

true = TrueClass()
false = Not(true)

def unit(conjType):
  if conjType == andType:
    return true
  else:
    assert(conjType == orType)
    return false

class Conj(PrimitiveObject):
  def __init__(self, left, right, type):
    assert(type in [andType, orType])
    self._type = type
    self._left = left
    self._right = right

  def __repr__(self):
    if self.type() == andType:
      c = "|"
    else:
      assert(self.type() == orType)
      c = '-'
    return "( %s %s %s )"%(self.left(), c, self.right())

  def substituteVar(self, a, b):
    return Conj(type = self.type(),
        left = self.left().substituteVar(a, b),
        right = self.right().substituteVar(a, b))

  def assertEqual(self, other):
    assert(other.__class__ == Conj)
    assert(self.type() == other.type())
    self.left().assertEqual(other.left())
    self.right().assertEqual(other.right())

  def updateVars(self):
    return Conj(type = self.type(),
        left = self.left().updateVars(),
        right = self.right().updateVars())

  def type(self):
    return self._type
  def left(self):
    return self._left
  def right(self):
    return self._right

  def __eq__(self, other):
    return (self.__class__ == other.__class__ and self.type() == other.type()
        and self.left() == other.left() and self.right() == other.right())
  def __ne__(self, other):
    return not (self == other)

  def backwardQuantifierConj(self):
    # Q x . (A % B) --> (Q x . A) % (Q x . B)
    assert(self.left().__class__ == Quantifier)
    assert(self.right().__class__ == Quantifier)
    assert(self.left().var() == self.right().var())
    if self.type() == andType:
      assert(self.left().type() == existsType)
      assert(self.right().type() == existsType)
    else:
      assert(self.type() == orType)
      assert(self.left().type() == forallType)
      assert(self.right().type() == forallType)

    return QuantifierConj(quantifierType = self.left().type(),
        conjType = self.type(),
        var = self.left().var(),
        left = self.left().body(), right = self.right().body())

  def forwardConjQuantifier(self):
    # (Q x . A) % B --> Q x . (A % B)
    assert(self.left().__class__ == Quantifier)
    if self.type() == andType:
      assert(self.left().type() == existsType)
    else:
      assert(self.type() == orType)
      assert(self.left().type() == forallType)

    return ConjQuantifier(conjType = self.type(), quantifierType = self.left().type(),
        var = self.left().var(), left = self.left().body(), right = self.right())

  def backwardDiagonal(self):
    assert(self.type() == andType)
    assert(self.left().__class__ == Always)
    assert(self.right().__class__ == Always)
    assert(self.left().value() == self.right().value())
    return Diagonal(self.right().value())

  def forwardRemoveFalse(self):
    assert(self.right() == false)
    assert(self.type() == orType)
    return RemoveFalse(value = self.left())
  def backwardIntroduceTrue(self):
    assert(self.right() == true)
    assert(self.type() == andType)
    return IntroduceTrue(value = self.left())

  def forwardCommute(self):
    return Commute(a = self.left(), b = self.right(), type = self.type())
  def backwardCommute(self):
    return Commute(a = self.right(), b = self.left(), type = self.type())

  def forwardAssociateA(self):
    # (A % B) % C ---> A % (B % C)
    assert(self.left().__class__ == Conj)
    assert(self.left().type() == self.type())
    return AssociateA(a = self.left().left(), b = self.left().right(), c = self.right(),
        type = self.type())
  def backwardAssociateB(self):
    # A % (B % C) ---> (A % B) % C
    assert(self.left().__class__ == Conj)
    assert(self.left().type() == self.type())
    return AssociateB(a = self.left().left(), b = self.left().right(), c = self.right(),
        type = self.type())
  def backwardAssociateA(self):
    # (A % B) % C ---> A % (B % C)
    assert(self.right().__class__ == Conj)
    assert(self.right().type() == self.type())
    return AssociateA(a = self.left(), b = self.right().left(), c = self.right().right(),
        type = self.type())
  def forwardAssociateB(self):
    # A % (B % C) ---> (A % B) % C
    assert(self.right().__class__ == Conj)
    assert(self.right().type() == self.type())
    return AssociateB(a = self.left(), b = self.right().left(), c = self.right().right(),
        type = self.type())

  def forwardForget(self):
    assert(self.type() == andType)
    return Forget(self.left(), self.right())
  def forwardForgetFirst(self):
    assert(self.type() == andType)
    return self.forwardCommute().forwardFollow(lambda self: self.forwardForget())
  def backwardAdmit(self):
    assert(self.type() == orType)
    return Admit(self.left(), self.right())

  def forwardDistribute(self):
    # B  |           (B | C)
    # -- | C  --->   ------
    # A  |           (A | C)
    assert(self.type() == andType)
    assert(self.left().__class__ == Conj)
    assert(self.left().type() == orType)
    return Distribute(a = self.left().left(), b = self.left().right(), c = self.right())
  def backwardDistribute(self):
    assert(self.type() == orType)
    for child in [self.left(), self.right()]:
      assert(child.__class__ == Conj)
      assert(child.type() == andType)
    assert(self.left().right() == self.right().right())
    return Distribute(a = self.left().left(), b = self.right().left(), c = self.left().right())

  def forwardApply(self):
    # | A | B  | B  --->  | A
    # *------  |          *--
    assert(self.type() == andType)
    assert(self.left().__class__ == Not)
    assert(self.left().value().__class__ == Conj)
    assert(self.left().value().type() == andType)
    assert(self.right() == self.left().value().right())
    return Apply(a = self.left().value().left(), b = self.right())

  def forwardOnLeft(self, arrow):
    assert(arrow.src() == self.left())
    return OnLeft(arrow = arrow, right = self.right(), type = self.type())
  def forwardOnRight(self, arrow):
    assert(arrow.src() == self.right())
    return OnRight(arrow = arrow, left = self.left(), type = self.type())
  def backwardOnLeft(self, arrow):
    assert(arrow.tgt() == self.left())
    return OnLeft(arrow = arrow, right = self.right(), type = self.type())
  def backwardOnRight(self, arrow):
    assert(arrow.tgt() == self.right())
    return OnRight(arrow = arrow, left = self.left(), type = self.type())

  # f is a function taking self.left() to an arrow other such that self.forwardOnLeft(other) exists
  def forwardOnLeftFollow(self, f):
    return self.forwardOnLeft(f(self.left()))
  # f is a function taking self.right() to an arrow other such that self.forwardOnRight(other) exists
  def forwardOnRightFollow(self, f):
    return self.forwardOnRight(f(self.right()))
  # f is a function taking self.left() to an arrow other such that self.backwardOnLeft(other) exists
  def backwardOnLeftFollow(self, f):
    return self.backwardOnLeft(f(self.left()))
  # f is a function taking self.right() to an arrow other such that self.backwardOnRight(other) exists
  def backwardOnRightFollow(self, f):
    return self.backwardOnRight(f(self.right()))

def And(left, right):
  return Conj(left = left, right = right, type = andType)
def Or(left, right):
  return Conj(left = left, right = right, type = orType)
def With(left, right):
  return Not(Or(left = Not(left), right = Not(right)))
def Par(left, right):
  return Not(And(left = Not(left), right = Not(right)))

def Implies(predicate, consequent):
  return Not(And(left = predicate, right = Not(consequent)))

class Always(PrimitiveObject):
  def __init__(self, value):
    self._value = value

  def __repr__(self):
    return "!( %s )"%(self.value(),)

  def value(self):
    return self._value

  def substituteVar(self, a, b):
    return Always(self.value().substituteVar(a, b))

  def assertEqual(self, other):
    assert(other.__class__ == Always)
    self.value().assertEqual(other.value())

  def updateVars(self):
    return Always(self.value().updateVars())

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.value() == other.value()
  def __ne__(self, other):
    return not (self == other)

  def forwardDiagonal(self):
    return Diagonal(self.value())

  def forwardOnAlways(self, arrow):
    assert(arrow.src() == self.value())
    return OnAlways(arrow)
  def backwardOnAlways(self, arrow):
    assert(arrow.tgt() == self.value())
    return OnAlways(arrow)
  def forwardOnAlwaysFollow(self, f):
    return self.forwardOnAlways(f(self.value()))
  def backwardOnAlwaysFollow(self, f):
    return self.backwardOnAlways(f(self.value()))

# Arrows

# Abstract superclass of all primitive arrows between primitive objects.
class PrimitiveArrow:
  def src(self):
    raise Exception("Abstract superclass.")
  def tgt(self):
    raise Exception("Abstract superclass.")
  def __repr__(self):
    raise Exception("Abstract superclass.")

  # Return a more compact arrow than self, with the same src and tgt, but of a simpler nature.
  def compress(self):
    return self

  def asString(self, variance):
    return repr(self)


  # other is another arrow.
  def forwardCompose(self, other):
    return Composite(left = self, right = other)
  # other is another arrow.
  def backwardCompose(self, other):
    return Composite(left = other, right = self)

  # f is a function taking self.tgt() to an arrow other such that self . other exists
  # return self . other
  def forwardFollow(self, f):
    return self.forwardCompose(f(self.tgt()))
  # f is a function taking self.src() to an arrow other such that other . self exists
  # return other . self
  def backwardFollow(self, f):
    return self.backwardCompose(f(self.src()))

class FunctorialArrow(PrimitiveArrow):
  def __repr__(self):
    covariant = True
    return self.asString(covariant)

class Eliminate(PrimitiveArrow):
  def __init__(self, value, quantifiedVar, replacementVar):
    self._value = value
    self._quantifiedVar = quantifiedVar
    self._replacementVar = replacementVar

  def value(self):
    return self._value
  def quantifiedVar(self):
    return self._quantifiedVar
  def replacementVar(self):
    return self._replacementVar

  def __repr__(self):
    return "eliminate(%s --> %s)"%(self.quantifiedVar(), self.replacementVar())

  def src(self):
    return Quantifier(type = forallType, var = self.quantifiedVar(), body = self.value())
  def tgt(self):
    return self.value().substituteVar(self.quantifiedVar(), self.replacementVar())

class NotQuant(PrimitiveArrow):
  # | q(t,x)    --> q(~t, | x )
  # *-------              *--
  def __init__(self, variable, type, value):
    assert(type in quantifierTypes)
    self._type = type
    self._variable = variable
    self._value = value

  def type(self):
    return self._type
  def variable(self):
    return self._variable
  def value(self):
    return self._value

  def __repr__(self):
    return "NotQuant"

  def src(self):
    return Not(Quantifier(type = self.type(), variable = self.variable(), body = self.value()))
  def tgt(self):
    return Quantifier(type = dualQuantifierType(self.type()), variable = self.variable(),
        body = Not(self.body()))

class IntroduceDoubleDual(PrimitiveArrow):
  #              ||A
  #   A   ---->  |*-
  #              *--
  def __init__(self, value):
    self._value = value

  def __repr__(self):
    return "introduce_double_dual"

  def value(self):
    return self._value

  def src(self):
    return self.value()
  def tgt(self):
    return Not(Not(self.value()))

class RemoveDoubleDual(PrimitiveArrow):
  # ||A
  # |*-   --->   A
  # *--
  def __init__(self, value):
    self._value = value

  def __repr__(self):
    return "remove_double_dual"

  def value(self):
    return self._value

  def src(self):
    return Not(Not(self.value()))
  def tgt(self):
    return self.value()

class Diagonal(PrimitiveArrow):
  # !A   ---> !A | !A
  def __init__(self, value):
    self._value = value

  def __repr__(self):
    return "diagonal"

  def value(self):
    return self._value

  def src(self):
    return Always(self.value())
  def tgt(self):
    return And(Always(self.value()), Always(self.value().updateVars()))

class IntroduceTrue(PrimitiveArrow):
  # A ---> A | |
  def __init__(self, value):
    self._value = value

  def __repr__(self):
    return "introduce_and"

  def value(self):
    return self._value

  def src(self):
    return self.value()
  def tgt(self):
    return Conj(type = andType, left = self.value(), right = true)

class RemoveFalse(PrimitiveArrow):
  #   ||
  #   *-
  #   --   --->  A
  #   A
  def __init__(self, value):
    self._value = value

  def __repr__(self):
    return "remove_false"

  def value(self):
    return self._value

  def src(self):
    return Conj(type = orType, left = self.value(), right = false)
  def tgt(self):
    return self.value()

class Commute(PrimitiveArrow):
  # for % in {|, -}
  #   A % B --> B % A
  def __init__(self, a, b, type):
    self._a = a
    self._b = b
    self._type = type

  def __repr__(self):
    return "commute"

  def a(self):
    return self._a
  def b(self):
    return self._b
  def type(self):
    return self._type

  def src(self):
    return Conj(type = self.type(), left = self.a(), right = self.b())
  def tgt(self):
    return Conj(type = self.type(), left = self.b(), right = self.a())

class AssociateA(PrimitiveArrow):
  # (A % B) % C ---> A % (B % C)
  def __init__(self, a, b, c, type):
    self._a = a
    self._b = b
    self._c = c
    self._type = type

  def __repr__(self):
    return "associate(%s)[[--]-]->[-[--]]"%(self.type(),)

  def a(self):
    return self._a
  def b(self):
    return self._b
  def c(self):
    return self._c
  def type(self):
    return self._type

  def _conj(self, left, right):
    return Conj(type = self.type(), left = left, right = right)

  def src(self):
    return self._conj(self._conj(self.a(), self.b()), self.c())
  def tgt(self):
    return self._conj(self.a(), self._conj(self.b(), self.c()))

class AssociateB(PrimitiveArrow):
  # A % (B % C) ---> (A % B) % C
  def __init__(self, a, b, c, type):
    self._a = a
    self._b = b
    self._c = c
    self._type = type

  def __repr__(self):
    return "associate(%s)[-[--]]->[[--]-]"%(self.type(),)

  def a(self):
    return self._a
  def b(self):
    return self._b
  def c(self):
    return self._c
  def type(self):
    return self._type

  def _conj(self, left, right):
    return Conj(type = self.type(), left = left, right = right)

  def src(self):
    return self._conj(self.a(), self._conj(self.b(), self.c()))
  def tgt(self):
    return self._conj(self._conj(self.a(), self.b()), self.c())

class Forget(PrimitiveArrow):
  # A | B --> A
  def __init__(self, a, b):
    self._a = a
    self._b = b

  def __repr__(self):
    return "forget"

  def a(self):
    return self._a
  def b(self):
    return self._b

  def src(self):
    return Conj(type = andType, left = self.a(), right = self.b())
  def tgt(self):
    return self.a()

class Admit(PrimitiveArrow):
  #           B
  # A  --->  --
  #           A
  def __init__(self, a, b):
    self._a = a
    self._b = b

  def __repr__(self):
    return "admit"

  def a(self):
    return self._a
  def b(self):
    return self._b

  def src(self):
    return self.a()
  def tgt(self):
    return Conj(type = orType, left = self.a(), right = self.b())

class QuantifierConj(PrimitiveArrow):
  # Q x . (A % B) --> (Q x . A) % (Q x . B)
  def __init__(self, quantifierType, conjType, var, left, right):
    if quantifierType == forallType:
      assert(conjType == orType)
    else:
      assert(quantifierType == existsType)
      assert(conjType == andType)

    self._quantifierType = quantifierType
    self._conjType = conjType
    self._var = var
    self._left = left
    self._right = right

  def __repr__(self):
    return "quantConj"

  def src(self):
    return Quantifier(var = self._var, type = self._quantifierType,
        body = Conj(type = self._conjType, left = self._left, right = self._right))
  def tgt(self):
    return Conj(type = self._conjType,
        left = Quantifier(var = self._var, type = self._quantifierType, body = self._left),
        right = Quantifier(var = self._var, type = self._quantifierType, body = self._right))

class ConjQuantifier(PrimitiveArrow):
  # (Q x . A) % B --> Q x . (A % B)
  def __init__(self, quantifierType, conjType, var, left, right):
    if quantifierType == forallType:
      assert(conjType == orType)
    else:
      assert(quantifierType == existsType)
      assert(conjType == andType)

    self._quantifierType = quantifierType
    self._conjType = conjType
    self._var = var
    self._left = left
    self._right = right

  def __repr__(self):
    return "conjQuant"

  def src(self):
    return Conj(type = self._conjType, right = self._right,
        left = Quantifier(var = self._var, type = self._quantifierType, body = self._left))
  def tgt(self):
    return Quantifier(var = self._var, type = self._quantifierType,
        body = Conj(type = self._conjType, left = self._left, right = self._right))

class Distribute(PrimitiveArrow):
  # B  |           (B | C)
  # -- | C         ------
  # A  |    --->   (A | C)
  def __init__(self, a, b, c):
    self._a = a
    self._b = b
    self._c = c

  def __repr__(self):
    return "distribute"

  def a(self):
    return self._a
  def b(self):
    return self._b
  def c(self):
    return self._c

  def src(self):
    return And(Or(self.a(), self.b()), self.c())
  def tgt(self):
    return Or(And(self.a(), self.c()), And(self.b(), self.c()))

class Apply(PrimitiveArrow):
  # | A | B  | B  --->  | A
  # *------  |          *--
  def __init__(self, a, b):
    self._a = a
    self._b = b

  def __repr__(self):
    return "apply(%s)"%(self.b(),)

  def a(self):
    return self._a
  def b(self):
    return self._b

  def src(self):
    return And(Not(And(self.a(), self.b())), self.b())
  def tgt(self):
    return Not(self.a())

class UnusedQuantifier(PrimitiveArrow):
  def __init__(self, type, variable, body):
    self._variable = variable
    self._type = type
    self._body = body

  def variable(self):
    return self._variable
  def body(self):
    return self._body

  def __repr__(self):
    return "unused_existial(%s)"%(self.variable(),)

  def src(self):
    return Quantifier(var = self.variable(), type = self._type, body = self.body())
  def tgt(self):
    return self.body()

# Functorial Arrows

def shiftRight(s, variance):
  if variance:
    return "\n".join(["  " + line for line in s.splitlines()])
  else:
    return "\n".join(["||" + line for line in s.splitlines()])

# All functors can be converted to strings in essentially the same way.
#title{
#  innerline0
#  innerline1
#  innerline2
#  .
#  .
#  innerlinen
#}title
# Where innerline0 ... innerlinen are the result of converting innerArrow to a string.
def functorToString(title, innerArrow, variance):
  return "%s{\n%s\n}%s"%(title, shiftRight(innerArrow.asString(variance), variance), title)

class OnBody(FunctorialArrow):
  def __init__(self, arrow, var, type):
    self._arrow = arrow
    self._var = var
    self._type = type

  def asString(self, variance):
    return functorToString("onBody", self.arrow(), variance)

  def compress(self):
    return OnBody( arrow = self._arrow.compress(), var = self.var(), type = self.type())

  def arrow(self):
    return self._arrow
  def var(self):
    return self._var
  def type(self):
    return self._type

  def src(self):
    return Quantifier(var = self.var(), type = self.type(), body = self.arrow().src())
  def tgt(self):
    return Quantifier(var = self.var(), type = self.type(), body = self.arrow().tgt())

class OnLeft(FunctorialArrow):
  def __init__(self, right, arrow, type):
    self._right = right
    self._arrow = arrow
    self._type = type

  def asString(self, variance):
    return functorToString("onLeft(%s)"%(self.type(),), self.arrow(), variance)

  def compress(self):
    return OnLeft(right = self.right(), arrow = self.arrow().compress(), type = self.type())

  def right(self):
    return self._right
  def arrow(self):
    return self._arrow
  def type(self):
    return self._type

  def src(self):
    return Conj(type = self.type(), left = self.arrow().src(), right = self.right())
  def tgt(self):
    return Conj(type = self.type(), left = self.arrow().tgt(), right = self.right())

class OnRight(FunctorialArrow):
  def __init__(self, left, arrow, type):
    self._left = left
    self._arrow = arrow
    self._type = type

  def asString(self, variance):
    return functorToString("onRight(%s)"%(self.type(),), self.arrow(), variance)

  def compress(self):
    return OnRight(left = self.left(), arrow = self.arrow().compress(), type = self.type())

  def left(self):
    return self._left
  def arrow(self):
    return self._arrow
  def type(self):
    return self._type

  def src(self):
    return Conj(type = self.type(), right = self.arrow().src(), left = self.left())
  def tgt(self):
    return Conj(type = self.type(), right = self.arrow().tgt(), left = self.left())

class OnConj:
  def __init__(self, type, leftArrow, rightArrow):
    self._type = type
    self._leftArrow = leftArrow
    self._rightArrow = rightArrow

  def type(self):
    return self._type
  def leftArrow(self):
    return self._leftArrow
  def rightArrow(self):
    return self._rightArrow

  def src(self):
    return Conj(type = self.type(), left = self.leftArrow().src(), right = self.rightArrow().src())
  def tgt(self):
    return Conj(type = self.type(), left = self.leftArrow().tgt(), right = self.rightArrow().tgt())

class OnAlways(FunctorialArrow):
  def __init__(self, arrow):
    self._arrow = arrow

  def asString(self, variance):
    return functorToString("onAlways", self.arrow(), variance)

  def arrow(self):
    return self._arrow

  def compress(self):
    return OnAlways(self.arrow().compress())

  def src(self):
    return Always(self.arrow().src())
  def tgt(self):
    return Always(self.arrow().tgt())

class OnNot(FunctorialArrow):
  def __init__(self, arrow):
    self._arrow = arrow

  def asString(self, variance):
    return functorToString("onNot", self.arrow(), not variance)

  def compress(self):
    return OnNot(self.arrow().compress())

  def arrow(self):
    return self._arrow

  # src and tgt go the opposite direction since Not is contravariant.
  def src(self):
    return Not(self.arrow().tgt())
  def tgt(self):
    return Not(self.arrow().src())

# Composite Arrows

class Identity(PrimitiveArrow):
  def __init__(self, value):
    self._value = value

  def asString(self, variance):
    return "identity"

  def __repr__(self):
    return self.asString(True)

  def value(self):
    return self._value

  def src(self):
    return self.value()
  def tgt(self):
    return self.value()

class Composite(PrimitiveArrow):
  # left and right are arrows such that left.src() == right.tgt()
  # construct their composite arrow.
  def __init__(self, left, right):
    left.tgt().assertEqual(right.src())
    if left.tgt() != right.src():
      raise Exception(("Failed to compose arrows since src and tgt are"
        + " unequal\n\n\nsrc = %s\n\ntgt= %s\n")%(left.tgt(), right.src()))
    self._left = left
    self._right = right

  def asString(self, variance):
    leftString, rightString = self.left().asString(variance), self.right().asString(variance)
    if variance:
      return "%s\n%s"%(leftString, rightString)
    else:
      return "%s\n%s"%(rightString, leftString)

  def compress(self):
    left = self.left().compress()
    right = self.right().compress()
    if left.__class__ == Identity:
      return right
    elif right.__class__ == Identity:
      return left
    elif left.__class__ == Composite:
      return left.left().forwardCompose(Composite(left.right(), right).compress())
    elif right.__class__ == Composite:
      return Composite(left, right.left()).compress().forwardCompose(right.right())
    else:
      if left.__class__ == OnConj and right.__class__ == OnConj:
        return OnConj(left.type()
                     , left.leftArrow().forwardCompose(right.leftArrow()).compress()
                     , left.rightArrow().forwardCompose(right.rightArrow()).compress())
      elif left.__class__ == OnConj and right.__class == OnLeft:
        return OnConj( left.type()
                     , left.leftArrow().forwardCompose(right.arrow()).compress()
                     , left.rightArrow())
      elif left.__class__ == OnConj and right.__class == OnRight:
        return OnConj( left.type()
                     , left.leftArrow()
                     , left.rightArrow().forwardCompose(right.arrow()).compress())
      elif left.__class__ == OnLeft and right.__class__ == OnConj:
        return OnConj( left.type()
                     , left.arrow().forwardCompose(right.leftArrow()).compress()
                     , right.rightArrow())
      elif left.__class__ == OnRight and right.__class__ == OnConj:
        return OnConj( left.type()
                     , right.leftArrow()
                     , left.arrow().forwardCompose(right.rightArrow()).compress())
      elif left.__class__ == OnLeft and right.__class__ == OnLeft:
        assert(left.right() == right.right())
        return OnLeft( type = left.type(),
            right = left.right(),
            arrow = left.arrow().forwardCompose(right.arrow()))
      elif left.__class__ == OnRight and right.__class__ == OnRight:
        assert(left.left() == right.left())
        return OnRight( type = left.type(),
            left = left.left(),
            arrow = left.arrow().forwardCompose(right.arrow()))
      elif left.__class__ == OnBody and right.__class__ == OnBody:
        assert(left.type() == right.type())
        assert(left.var() == right.var())
        return OnBody(type = left.type(), var = left.var(),
            arrow = left.arrow().forwardCompose(right.arrow()).compress())
      elif left.__class__ == OnNot and right.__class__ == OnNot:
        return OnNot(left.arrow().backwardCompose(right.arrow()).compress())
      elif left.__class__ == OnAlways and right.__class__ == OnAlways:
        return OnAlways(left.arrow().forwardCompose(right.arrow()).compress())
      else:
        return self

  def __repr__(self):
    return self.asString(True)

  def left(self):
    return self._left
  def right(self):
    return self._right

  def src(self):
    return self.left().src()
  def tgt(self):
    return self.right().tgt()

# return an arrow with opposite src and tgt as arrow provided arrow is in fact an isomorphism.
# otherwise return None
def reverse(arrow):
  if arrow.__class__ == Identity:
    return arrow
  elif arrow.__class__ == Composite:
    a = reverse(arrow.left())
    b = reverse(arrow.right())
    if a is None or b is None:
      return None
    else:
      return Composite(b, a)
  elif arrow.__class__ == OnNot:
    a = reverse(arrow.arrow())
    if a is None:
      return None
    else:
      return OnNot(a)
  elif arrow.__class__ == OnAlways:
    a = reverse(arrow.arrow())
    if a is None:
      return None
    else:
      return OnAlways(a)
  elif arrow.__class__ == OnRight:
    a = reverse(arrow.arrow())
    if a is None:
      return None
    else:
      return OnRight(type = arrow.type(), left = arrow.left(), arrow = a)
  elif arrow.__class__ == OnLeft:
    a = reverse(arrow.arrow())
    if a is None:
      return None
    else:
      return OnLeft(type = arrow.type(), right = arrow.right(), arrow = a)
  elif arrow.__class__ == OnBody:
    a = reverse(arrow.arrow())
    if a is None:
      return None
    else:
      return OnBody(type = arrow.type(), var = arrow.var(), arrow = a)
  elif arrow.__class__ == Apply:
    return None
  elif arrow.__class__ == Distribute:
    return None
  elif arrow.__class__ == Admit:
    if arrow.b() == false:
      return arrow.tgt().forwardRemoveFalse()
    else:
      return None
  elif arrow.__class__ == Forget:
    if arrow.b() == true:
      return arrow.tgt().forwardIntroduceTrue()
    else:
      return None
  elif arrow.__class__ == AssociateA:
    return arrow.tgt().forwardAssociateB()
  elif arrow.__class__ == AssociateB:
    return arrow.tgt().forwardAssociateA()
  elif arrow.__class__ == Commute:
    return arrow.tgt().forwardCommute()
  elif arrow.__class__ == RemoveFalse:
    return arrow.tgt().forwardAdmit(false)
  elif arrow.__class__ == IntroduceTrue:
    return arrow.tgt().forwardForget()
  elif arrow.__class__ == Diagonal:
    return arrow.tgt().forwardForget()
  elif arrow.__class__ == IntroduceDoubleDual:
    return arrow.tgt().forwardRemoveDoubleDual()
  elif arrow.__class__ == RemoveDoubleDual:
    return arrow.tgt().forwardIntroduceDoubleDual()
  else:
    raise Exception("Unrecognized arrow.")

