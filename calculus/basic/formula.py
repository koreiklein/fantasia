# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol
from calculus.variable import Variable
from lib import common_symbols

from sets import Set

class Formula:
  def simplify(self):
    return self.identity()

  # f is a function taking each object B to a list ys
  # return a list of all pairs (a, X) such that
  #   a is an arrow self -> B|self
  #   X is in f(B)
  #   B == Always(C) for some C
  def produceFiltered(self, f):
    return []

  # Replace all bound variables with new variables.
  def updateVariables(self):
    raise Exception("Abstract superclass.")

  # a, b: variables.
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

  def backwardUnalways(self):
    return Unalways(tgt = self, src = Always(self))

  def forwardAdmitLeft(self, x):
    return Admit(src = self, tgt = Or(self, x))
  def forwardAdmitRight(self, x):
    return Admit(src = self, tgt = Or(x, self))

  def backwardForgetLeft(self, x):
    return Forget(tgt = self, src = And(x, self))
  def backwardForgetRight(self, x):
    return Forget(tgt = self, src = And(self, x))

  def forwardIntroExists(self, variable, oldVariable):
    return IntroExists(src = self,
        tgt = Exists(variable = variable, value = self.substituteVariable(oldVariable, variable)))
  def backwardRemoveExists(self, variable):
    assert(variable not in self.freeVariables())
    return RemoveExists(src = Exists(variable = variable, value = self), tgt = self)

  def forwardHide(self, name):
    return Hide(src = self, tgt = Hidden(self, name))

  def identity(self):
    return Id(src = self, tgt = self)

class Holds(Formula):
  def __init__(self, held, holding):
    self.held = held
    self.holding = holding

  def __eq__(self, other):
    return (self.__class__ == other.__class__
        and self.holding == other.holding
        and self.held == other.held)

  def __ne__(self, other):
    return not (self == other)
  def __repr__(self):
    return repr(self.held) + " : " + repr(self.holding)
  def updateVariables(self):
    return self
  def substituteVariable(self, a, b):
    return Holds(held = self.held.substituteVariable(a, b),
        holding = self.holding.substituteVariable(a, b))
  def freeVariables(self):
    result = Set()
    result.union_update(self.holding.freeVariables())
    result.union_update(self.held.freeVariables())
    return result

def isExistentialOfLength(n, existential):
  for i in range(n):
    if existential.__class__ != Exists:
      return False
    existential = existential.value
  return True

class Exists(Formula):
  def __init__(self, variable, value):
    assert(isinstance(variable, Variable))
    self.variable = variable
    self.value = value

  def simplify(self):
    return OnBody(self.variable, self.value.simplify())

  def __eq__(self, other):
    if self.__class__ != other.__class__:
      return False
    else:
      if self.variable == other.variable:
        return self.value == other.value
      else:
        return (self.variable not in other.value.freeVariables()
            and self.value == other.value.substituteVariable(other.variable, self.variable))

  def __ne__(self, other):
    return not(self == other)

  def __repr__(self):
    return "( Exists %s . %s )"%(self.variable, self.value)

  # f is a function taking each object B to a list ys
  # return a list of all pairs (a, X) such that
  #   a is an arrow self -> B|self
  #   X is in f(B)
  #   B == Always(C) for some C
  def produceFiltered(self, f):
    # Exists xs. X --> Exists xs. (B|X) --> (B|Exists xs.X)
    return [(self.forwardOnBody(a).forwardFollow(lambda x, B=B:
                                   AndPastExists(src = And(B, self), tgt = x).invert()), X)
            for a, X in self.value.produceFiltered(f)
            for B in [a.tgt.left]
            if self.variable not in B.freeVariables]

  def forwardOnBody(self, arrow):
    assert(isinstance(arrow, Arrow))
    assert(arrow.src == self.value)
    return OnBody(variable = self.variable, arrow = arrow)
  def backwardOnBody(self, arrow):
    assert(arrow.tgt == self.value)
    return OnBody(variable = self.variable, arrow = arrow)
  def forwardOnBodyFollow(self, f):
    return self.forwardOnBody(f(self.value))
  def backwardOnBodyFollow(self, f):
    return self.backwardOnBody(f(self.value))

  def forwardRemoveExists(self):
    assert(self.variable not in self.value.freeVariables())
    return RemoveExists(src = self, tgt = self.value)
  def backwardIntroExists(self, newVariable):
    return IntroExists(src = self.value.substituteVariable(self.variable, newVariable), tgt = self)

  def forwardCommuteExists(self):
    assert(self.value.__class__ == Exists)
    return self.forwardOnBodyFollow(lambda x:
        x.forwardOnBodyFollow(lambda x:
          x.forwardIntroExists(self.variable, self.variable))).forwardFollow(lambda x:
              x.forwardRemoveExists())

  def forwardExistsPastAnd(self):
    return self.forwardOnBodyFollow(lambda x:
        x.forwardOnRightFollow(lambda x:
          x.forwardIntroExists(self.variable, self.variable))).forwardFollow(lambda x:
              x.forwardRemoveExists())

  def updateVariables(self):
    variable = self.variable.updateVariables()
    return Exists(variable = variable,
        value = self.value.substituteVariable(
          self.variable, variable).updateVariables())

  def substituteVariable(self, a, b):
    assert(self.variable not in a.freeVariables())
    assert(self.variable not in b.freeVariables())
    return Exists(variable = self.variable,
        value = self.value.substituteVariable(a, b))

  def freeVariables(self):
    return self.value.freeVariables().difference(Set([self.variable]))

def MultiExists(variables, value):
  for variable in variables[::-1]:
    value = Exists(variable, value)
  return value

def MultiBoundedExists(variable_domain_pairs, value):
  values = []
  variables = []
  for (variable, domain) in variable_domain_pairs:
    variables.append(variable)
    values.append(Always(Holds(variable, domain)))
  values.append(value)
  return MultiExists(variables, MultiAnd(values))

def MultiForall(variables, value):
  return Always(Not(MultiExists(variables, Not(value))))

def MultiBoundedForall(variable_domain_pairs, value):
  return Always(Not(MultiBoundedExists(variable_domain_pairs, Not(value))))

# For And and Or.
class Conjunction(Formula):
  # There is only one global right symbol.
  def __init__(self, left, right):
    self.left = left
    self.right = right

  def simplify(self):
    return self.forwardOnConjunction(self.left.simplify(), self.right.simplify())

  def __eq__(self, other):
    return (self.__class__ == other.__class__
        and self.left == other.left
        and self.right == other.right)
  def __ne__(self, other):
    return not(self == other)

  def forwardOnConjunction(self, leftArrow, rightArrow):
    assert(isinstance(leftArrow, Arrow))
    assert(isinstance(rightArrow, Arrow))
    assert(leftArrow.src == self.left)
    assert(rightArrow.src == self.right)
    return OnConjunction(leftArrow = leftArrow, rightArrow = rightArrow,
        src = self,
        tgt = self.__class__(left = leftArrow.tgt,
                             right = rightArrow.tgt))
  def backwardOnConjunction(self, leftArrow, rightArrow):
    return OnConjunction(leftArrow = leftArrow, rightArrow = rightArrow,
        tgt = self,
        src = self.__class__(left = leftArrow.src,
                             right = rightArrow.src))
  def forwardOnLeft(self, arrow):
    assert(isinstance(arrow, Arrow))
    assert(arrow.src == self.left)
    return self.forwardOnConjunction(leftArrow = arrow, rightArrow = self.right.identity())
  def forwardOnRight(self, arrow):
    assert(isinstance(arrow, Arrow))
    return self.forwardOnConjunction(rightArrow = arrow, leftArrow = self.left.identity())
  def backwardOnLeft(self, arrow):
    assert(isinstance(arrow, Arrow))
    return self.backwardOnConjunction(leftArrow = arrow, rightArrow = self.right.identity())
  def backwardOnRight(self, arrow):
    assert(isinstance(arrow, Arrow))
    return self.backwardOnConjunction(rightArrow = arrow, leftArrow = self.left.identity())

  def forwardOnLeftFollow(self, f):
    return self.forwardOnLeft(f(self.left))
  def forwardOnRightFollow(self, f):
    return self.forwardOnRight(f(self.right))
  def backwardOnLeftFollow(self, f):
    return self.backwardOnLeft(f(self.left))
  def backwardOnRightFollow(self, f):
    return self.backwardOnRight(f(self.right))

  def updateVariables(self):
    return self.__class__(
        left = self.left.updateVariables(),
        right = self.right.updateVariables())

  def substituteVariable(self, a, b):
    return self.__class__(
        left = self.left.substituteVariable(a, b),
        right = self.right.substituteVariable(a, b))

  def freeVariables(self):
    return self.left.freeVariables().union(self.right.freeVariables())

  def forwardCommute(self):
    return Commute(
        src = self,
        tgt = self.__class__(
          left = self.right,
          right = self.left))

  def backwardCommute(self):
    return Commute(
        tgt = self,
        src = self.__class__(
          left = self.right,
          right = self.left))

  def forwardAssociate(self):
    # (A % B) % C ---> A % (B % C)
    assert(self.__class__ == self.left.__class__)
    return Associate(src = self,
        tgt = self.__class__(
          left = self.left.left,
          right = self.__class__(
            left = self.left.right,
            right = self.right)))

  def backwardAssociate(self):
    # (A % B) % C ---> A % (B % C)
    assert(self.__class__ == self.right.__class__)
    return Associate(tgt = self,
        src = self.__class__(
          right = self.right.right,
          left = self.__class__(
            right = self.right.left,
            left = self.left)))

  def forwardAssociateOther(self):
    # A % (B % C) ---> (A % B) % C
    return self.backwardAssociate().invert()

  def backwardAssociateOther(self):
    # A % (B % C) ---> (A % B) % C
    return self.forwardAssociate().invert()

class And(Conjunction):
  # f is a function taking each object B to a list ys
  # return a list of all pairs (a, X) such that
  #   a is an arrow self -> B|self
  #   X is in f(B)
  #   B == Always(C) for some C
  def produceFiltered(self, f):
    result = []
    # (X|Y) --> (X|(B|Y)) --> (X|(Y|B)) --> ((X|Y)|B) --> (B|(X|Y))
    result.extend([(self.forwardOnRight(a.forwardFollow(lambda x:
      x.forwardCommute())).forwardFollow(lambda x:
        x.forwardAssociateOther().forwardFollow(lambda x:
          x.forwardCommute())), X) for a, X in self.right.produceFiltered(f)])
    # (X|Y) --> ((B|X)|Y) --> (B|(X|Y))
    result.extend([(self.forwardOnLeft(a).forwardFollow(lambda x:
          x.forwardAssociate()), X) for a, X in self.left.produceFiltered(f)])
    return result

  def simplifyOnce(self):
    if self.left == unit_for_conjunction(And):
      return UnitIdentity(tgt = self, src = self.right).invert()
    elif self.right == unit_for_conjunction(And):
      return UnitIdentity(tgt = self, src = self.left).invert()
    else:
      raise Exception("Can't simplify once.")

  def simplify(self):
    if self.left == unit_for_conjunction(And):
      return UnitIdentity(tgt = self, src = self.right).invert().forwardFollow(lambda x:
          x.simplify())
    elif self.right == unit_for_conjunction(And):
      return UnitIdentity(tgt = self, src = self.left).invert().forwardFollow(lambda x:
          x.simplify())
    else:
      return self.forwardOnConjunction(self.left.simplify(), self.right.simplify())

  def forwardSubstituteIdentical(self, a, b):
    I = self.left
    assert(I.__class__ == Identical)
    assert((I.left == a and I.right == b) or (I.left == b and I.left == a))
    return SubstituteArrow(src = self, tgt = self.right.substituteVariable(a, b))

  def forwardApply(self):
    assert(self.right.__class__ == Not)
    assert(self.right.value.__class__ == And)
    return Apply(src = self, tgt = Not(self.right.value.right))

  def forwardZip(self):
    # !A | !B --> !(A|B)
    assert(self.left.__class__ == Always)
    assert(self.right.__class__ == Always)
    return Zip(src = self, tgt = Always(And(left = self.left.value, right = self.right.value)))

  def forwardAndPastExists(self):
    # (A|Exists xs. B) --> Exists xs. (A|B)
    assert(self.right.__class__ == Exists)
    return AndPastExists(src = self,
        tgt = Exists(variable = self.right.variable,
          value = And(left = self.left, right = self.right.value)))

  def forwardAndPastExistsOther(self):
    # (Exists xs. A|B) --> Exists xs. (A|B)
    return self.forwardCommute().forwardFollow(lambda x:
        x.forwardAndPastExists().forwardFollow(lambda x:
          x.forwardOnBodyFollow(lambda x:
            x.forwardCommute())))

  def forwardDistibute(self):
    # A | (B - C) --> (A | B) - (A | C)
    assert(self.right.__class__ == Or)
    def pairWith(x):
      return And(
          left = self.left,
          right = x)
    return Distribute(src = self,
        tgt = Or(
          left = pairWith(self.right.left),
          right = pairWith(self.right.right)))

  def forwardDistributeLeft(self):
    # A | (B - C) --> (A | B) - (A | C) --> (A | B) - C
    return self.forwardDistibute().forwardFollow(lambda x:
        x.forwardOnRightFollow(lambda x:
          x.forwardForgetLeft()))

  def forwardDistributeRight(self):
    # A | (B - C) --> (A | B) - (A | C) --> B - (A | C)
    return self.forwardDistibute().forwardFollow(lambda x:
        x.forwardOnLeftFollow(lambda x:
          x.forwardForgetLeft()))

  def backwardCopy(self):
    return Copy(tgt = self, src = self.left)

  def forwardForgetLeft(self):
    return Forget(src = self, tgt = self.right)
  def forwardForgetRight(self):
    return Forget(src = self, tgt = self.left)

  def __repr__(self):
    return "(%s AND %s)"%(self.left, self.right)

class Or(Conjunction):
  def __repr__(self):
    return "(%s OR %s)"%(self.left, self.right)

  def simplifyOnce(self):
    if self.left == unit_for_conjunction(Or):
      return UnitIdentity(src = self, tgt = self.right)
    elif self.right == unit_for_conjunction(Or):
      return UnitIdentity(src = self, tgt = self.left)
    else:
      raise Exception("Can't simplify once.")

  def simplify(self):
    if self.left == unit_for_conjunction(Or):
      return UnitIdentity(src = self, tgt = self.right).forwardFollow(lambda x:
          x.simplify())
    elif self.right == unit_for_conjunction(Or):
      return UnitIdentity(src = self, tgt = self.left).forwardFollow(lambda x:
          x.simplify())
    else:
      return self.forwardOnConjunction(self.left.simplify(), self.right.simplify())

  def backwardAdmitLeft(self):
    return Admit(tgt = self, src = self.right)
  def backwardAdmitRight(self):
    return Admit(tgt = self, src = self.left)

# Multiple conjunction will be represented (a | (b | (c | 1)))
def multiple_conjunction(conjunction, values):
  if len(values) == 0:
    return unit_for_conjunction(conjunction)
  else:
    result = values[-1]
    for value in values[::-1][1:]:
      result = conjunction(left = value, right = result)
    return result

def MultiAnd(values):
  return multiple_conjunction(And, values)
def MultiOr(values):
  return multiple_conjunction(Or, values)

# There are two reasonable ways to implement this function.
def Implies(predicate, consequent):
  return Always(Not(
    value = And(left = predicate,
                right = Not(consequent))))

def ExpandIff(left, right):
  return And(Implies(left, right), Implies(right, left))

class Not(Formula):
  def __init__(self, value, rendered = False):
    self.value = value
    self.rendered = rendered

  def simplify(self):
    return self.forwardOnNot(self.value.simplify().invert())

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.value == other.value
  def __ne__(self, other):
    return not(self == other)

  def __repr__(self):
    return "~(%s)"%(self.value,)

  def forwardOnNot(self, arrow):
    assert(isinstance(arrow, Arrow))
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

  def forwardUndoubleDual(self):
    assert(self.value.__class__ == Not)
    return self.backwardDoubleDual().invert()

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

class Always(Formula):
  def __init__(self, value):
    self.value = value

  def simplify(self):
    return self.forwardOnAlways(self.value.simplify())

  # f is a function taking each object B to a list ys
  # return a list of all pairs (a, X) such that
  #   a is an arrow self -> B|self
  #   X is in f(B)
  #   B == Always(C) for some C
  def produceFiltered(self, f):
    result = []
    result.extend([(self.forwardOnAlways(a).forwardFollow(lambda x:
      x.forwardDistributeAlways().forwardFollow(lambda x:
        x.forwardOnLeftFollow(lambda x:
          x.forwardUnalways()))), X) for a, X in self.value.produceFiltered(f)])
    result.extend([(self.forwardCopy(), X) for X in f(self)])
    return result

  def forwardCopy(self):
    return Copy(src = self, tgt = And(self.updateVariables(), self))

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self.value == other.value
  def __ne__(self, other):
    return not(self == other)

  def __repr__(self):
    return "!(%s)"%(self.value)

  def forwardUnalways(self):
    return Unalways(src = self, tgt = self.value)

  def forwardOnAlways(self, arrow):
    assert(isinstance(arrow, Arrow))
    assert(arrow.src == self.value)
    return OnAlways(arrow)
  def backwardOnAlways(self, arrow):
    assert(arrow.tgt == self.value)
    return OnAlways(arrow)
  def forwardOnAlwaysFollow(self, f):
    return self.forwardOnAlways(f(self.value))
  def backwardOnAlwaysFollow(self, f):
    return self.backwardOnAlways(f(self.value))

  def forwardAlwaysPastExists(self):
    # !(Exists x . B) --> Exists x . !B
    assert(self.value.__class__ == Exists)
    return AlwaysPastExists(src = self, tgt = Exists(self.value.variable, Always(self.value.value)))

  # !(A|B) --> !A | !B
  def forwardDistributeAlways(self):
    # !(A|B) --> !(A|B) | !(A|B) --> !A | !(A|B) --> !A | !B
    return self.forwardCopy().forwardFollow(lambda x:
        x.forwardOnLeftFollow(lambda x: x.forwardForgetRight()).forwardFollow(lambda x:
          x.forwardOnRightFollow(lambda x: x.forwardForgetLeft())))

  def forwardCojoin(self):
    return Cojoin(src = self, tgt = Always(self))

  def updateVariables(self):
    return self.__class__(value = self.value.updateVariables())

  def substituteVariable(self, a, b):
    return self.__class__(value = self.value.substituteVariable(a, b))

  def freeVariables(self):
    return self.value.freeVariables()

class Unit(Formula):
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
  def __repr__(self):
    return "1"

  def __eq__(self, other):
    return other.__class__ == AndUnit
  def __ne__(self, other):
    return not(self == other)

class OrUnit(Unit):
  def __repr__(self):
    return "0"

  def __eq__(self, other):
    return other.__class__ == OrUnit
  def __ne__(self, other):
    return not(self == other)

true = AndUnit()
false = OrUnit()

# In contexts where Identical(a, b) or Identical(b, a) can be concluded, it must be the case
# that each formula F involving a has the EXACT same set of representations as
# the formula F.substituteVariable(a, b)
class Identical(Formula):
  def __init__(self, left, right):
    self.left = left
    self.right = right
  def __eq__(self, other):
    return other.__class__ == Identical and self.left == other.left and self.right == other.right
  def __ne__(self, other):
    return not(self == other)
  def updateVariables(self):
    return self
  def substituteVariable(self, a, b):
    return Identical(left = self.left.substituteVariable(a, b),
        right = self.right.substituteVariable(a, b))
  def freeVariables(self):
    result = Set()
    result.union_update(self.left.freeVariables())
    result.union_update(self.right.freeVariables())
    return result

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

  def substituteVariable(self, a, b):
    return self.__class__(src = self.src.substituteVariable(a, b),
        tgt = self.tgt.substituteVariable(a, b))

  def leftAssociate(self):
    return self
  def _leftAssociate(self, f):
    return f(self)
  def rightAssociate(self):
    return self
  def _rightAssociate(self, f):
    return f(self)

  def compress(self):
    return self

  def __repr__(self):
    return "%s"%(self.arrowTitle())

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
    self.src = arrow.tgt
    self.tgt = arrow.src

  def substituteVariable(self, a, b):
    return InverseArrow(arrow = self.arrow.substituteVariable(a, b))

  def __repr__(self):
    return "%s inverse"%(self.arrow,)

  def invert(self):
    return self.arrow

# A <--> A
class Id(Isomorphism):
  def arrowTitle(self):
    return "Id"
  def validate(self):
    assert(self.src == self.tgt)
  def compose(self, other):
    return other

# left, right: noncomposite arrows
# compress the composite of arrows left o right
def _compress2(left, right):
  assert(left.__class__ != Composite)
  assert(right.__class__ != Composite)
  if left.__class__ == OnAlways and right.__class__ == OnAlways:
    return OnAlways(left.arrow.forwardCompose(right.arrow)).compress()
  elif left.__class__ == OnNot and right.__class__ == OnNot:
    return OnNot(right.arrow.forwardCompose(left.arrow)).compress()
  elif left.__class__ == OnBody and right.__class__ == OnBody and left.variable == right.variable:
    return OnBody(variable = left.variable,
        arrow = left.arrow.forwardCompose(right.arrow)).compress()
  elif (left.__class__ == OnConjunction and right.__class__ == OnConjunction
      and left.src.__class__ == right.src.__class__):
    return OnConjunction(src = left.src, tgt = right.tgt,
        leftArrow = left.leftArrow.forwardCompose(right.leftArrow),
        rightArrow = left.rightArrow.forwardCompose(right.rightArrow)).compress()
  elif left.__class__ == Id:
    return right
  elif right.__class__ == Id:
    return left
  elif _commutingArrow(left) and _commutingArrow(right):
    return left.src.identity()
  else:
    # TODO Improve compression.
    # There are many special cases of compressions.
    # For example: compress copy arrows with forget arrows.
    return Composite(left, right)

def _commutingArrow(arrow):
  return (arrow.__class__ == Commute or
    (arrow.__class__ == InverseArrow and arrow.arrow.__class__ == Commute))

# A --> B --> C
class Composite(Arrow):
  def __init__(self, left, right):
    self.left = left
    self.right = right
    self.src = left.src
    self.tgt = right.tgt
    self.validate()

  def substituteVariable(self, a, b):
    return Composite(left = self.left.substituteVariable(a, b),
        right =self.right.substituteVariable(a, b))

  def compress(self):
    return self.rightAssociate()._compress_rightAssocitaed()

  # self must be right associated
  # return a right associated, compressed arrow equivalent to self.
  def _compress_rightAssocitaed(self):
    assert(self.left.__class__ != Composite)
    if self.right.__class__ == Composite:
      return Composite(self.left.compress(),
          self.right._compress_rightAssocitaed())._compress_rightAssociatedCompressed()
    else:
      return _compress2(self.left, self.right)

  # self must be right associated
  # self.left must be compressed
  # self.right must be compressed.
  # return a right associated, compressed arrow equivalent to self.
  def _compress_rightAssociatedCompressed(self):
    if self.right.__class__ == Composite:
      x = _compress2(self.left, self.right.left)
      if x.__class__ == Composite:
        # Can't compress further
        return self
      else:
        return Composite(x, self.right.right)._compress_rightAssociatedCompressed()
    else:
      return _compress2(self.left, self.right)

  def leftAssociate(self):
    return self._leftAssociate(lambda x: x)
  def _leftAssociate(self, f):
    # (((f(x)*x)*x)*x)
    return self.right._leftAssociate(lambda x: Composite(self.left._leftAssociate(f), x))

  def rightAssociate(self):
    return self._rightAssociate(lambda x: x)
  def _rightAssociate(self, f):
    # (x*(x*(x*f(x))))
    return self.left._rightAssociate(lambda x: Composite(x, self.right._rightAssociate(f)))

  def __repr__(self):
    return "%s o\n%s"%(self.left, self.right)

  # Throw an exception if self is not valid.
  # Subclasses should override to implement checking.
  def validate(self):
    if not(self.left.tgt == self.right.src):
      raise Exception(("Invalid composite.\n"
        "left %s\nright %s\nleft.src = %s\n"
        "left.tgt =%s\nright.src =%s\nright.tgt = %s\n"
          )%(self.left, self.right, self.left.src, self.left.tgt, self.right.src, self.right.tgt))

  # May throw an exception.
  def invert(self):
    return Composite(left = self.right.invert(), right = self.left.invert())

  def __eq__(self, other):
    return (self.__class__ == other.__class__
        and self.left == other.left
        and self.right == other.right)

  def __ne__(self, other):
    return not(self == other)

# A | (B - C) --> (A | B) - (A | C)
class Distribute(Arrow):
  def arrowTitle(self):
    return "Distribute"
  def validate(self):
    assert(self.src.__class__ == And)
    assert(self.src.right.__class__ == Or)
    assert(self.tgt.__class__ == Or)
    assert(self.tgt.left.__class__ == And)
    assert(self.tgt.right.__class__ == And)
    assert(self.src.left == self.tgt.left.left)
    assert(self.src.left == self.tgt.right.left)
    assert(self.src.right.left == self.tgt.left.right)
    assert(self.src.right.right == self.tgt.right.right)

# And(base, step) --> claim
class Induction(Arrow):
  def arrowTitle(self):
    return "Induction"
  def validate(self):
    #TODO Check induction arrows more carefully.
    pass

# A | B --> A,  A | B --> B
class Forget(Arrow):
  def arrowTitle(self):
    return "Forget"
  def validate(self):
    assert(self.src.__class__ == And)
    assert(self.tgt in [self.src.left, self.src.right])

# A - B <-- A,  A - B <-- B
class Admit(Arrow):
  def arrowTitle(self):
    return "Admit"
  def validate(self):
    assert(self.src.__class__ == Or)
    assert(self.src in [self.tgt.left, self.tgt.right])

class Commute(Isomorphism):
  def arrowTitle(self):
    return "Commute"
  def validate(self):
    assert(self.src.__class__ == self.tgt.__class__)

  def invert(self):
    return Commute(src = self.tgt, tgt = self.src)

# (A % B) % C ---> A % (B % C)
class Associate(Isomorphism):
  def arrowTitle(self):
    return "Associate[[..].]-->[.[..]]"
  def validate(self):
    assert(isinstance(self.src, Conjunction))
    assert(self.tgt.__class__ == self.src.__class__)
    common_class = self.src.__class__
    assert(self.src.left.__class__ == common_class
        and self.tgt.right.__class__ == common_class

        and self.src.left.left == self.tgt.left
        and self.src.left.right == self.tgt.right.left
        and self.src.right == self.tgt.right.right)

# A % 1 <-- A --> 1 % A
class UnitIdentity(Isomorphism):
  def arrowTitle(self):
    return "UnitIdentity"
  def validate(self):
    unit = unit_for_conjunction(self.tgt.__class__)
    assert((self.tgt.right == unit and self.tgt.left == self.src)
        or (self.tgt.left == unit and self.tgt.right == self.src))

# A <--> ~(~A)
class DoubleDual(Isomorphism):
  def arrowTitle(self):
    return "DoubleDual"
  def validate(self):
    assert(self.tgt.__class__ == Not)
    assert(self.tgt.value.__class__ == Not)
    assert(self.src == self.tgt.value.value)

# A | ~(A | B) --> ~B
class Apply(Arrow):
  def arrowTitle(self):
    return "Apply"
  def validate(self):
    assert(self.tgt.__class__ == Not)
    assert(self.src.__class__ == And)
    assert(self.src.right.__class__ == Not)
    assert(self.src.right.value.__class__ == And)
    assert(self.src.left == self.src.right.value.left)
    assert(self.src.right.value.right == self.tgt.value)

# !A --> !!A
class Cojoin(Arrow):
  def arrowTitle(self):
    return "Cojoin"
  def validate(self):
    assert(self.src.__class__ == Always)
    assert(self.tgt.__class__ == Always)
    assert(self.src == self.tgt.value)

# !A --> (!A).updateVariables() | !A
class Copy(Arrow):
  def arrowTitle(self):
    return "Copy"
  def validate(self):
    assert(self.src.__class__ == Always)
    assert(self.tgt.__class__ == And)
    # There's no easy way to check that self.tgt.left is like self.src but with variables
    # updated.
    # assert(self.tgt.left == self.src)
    assert(self.tgt.right == self.src)

# !A | !B --> !(A|B)
class Zip(Arrow):
  def arrowTitle(self):
    return "Zip"
  def validate(self):
    assert(self.src.__class__ == And)
    assert(self.src.left.__class__ == Always)
    assert(self.src.right.__class__ == Always)
    assert(self.tgt.__class__ == Always)
    assert(self.tgt.value.__class__ == And)
    assert(self.src.left.value == self.tgt.value.left)
    assert(self.src.right.value == self.tgt.value.right)

# !A --> A
class Unalways(Arrow):
  def arrowTitle(self):
    return "Unalways"
  def validate(self):
    assert(self.src.__class__ == Always)
    assert(self.src.value == self.tgt)

# A --> Exists x . A[v->x]
class IntroExists(Arrow):
  def arrowTitle(self):
    return "IntroExists"
  def validate(self):
    assert(self.tgt.__class__ == Exists)
    # There's no easy way to check that self.tgt.value.substituteVariable(v,x) == self.src
    # because we don't know v.

# The existence of this arrow may follow from the fact that right adjoints (B|.) preserve
# colimits (Exists x).  We just need a precise sense in which (Exists x) is a colimit.
# (A|Exists x. B) --> Exists x. (A|B)
class AndPastExists(Isomorphism):
  def arrowTitle(self):
    return "AndPastExists"
  def validate(self):
    assert(self.src.__class__ == And)
    assert(self.src.right.__class__ == Exists)
    assert(self.tgt.__class__ == Exists)
    assert(self.tgt.value.__class__ == And)
    assert(self.src.left == self.tgt.value.left)
    assert(self.src.right.variable == self.tgt.variable)

# !(Exists x . B) --> Exists x . !B
class AlwaysPastExists(Isomorphism):
  def arrowTitle(self):
    return "AlwaysPastExists"
  def validate(self):
    assert(self.src.__class__ == Always)
    assert(self.src.value.__class__ == Exists)
    assert(self.tgt.__class__ == Exists)
    assert(self.tgt.value.__class__ == Always)
    assert(self.src.value.value == self.tgt.value.value)

# Exists x . A --> A
class RemoveExists(Arrow):
  def arrowTitle(self):
    return "RemoveExists"
  def validate(self):
    assert(self.src.__class__ == Exists)
    assert(self.tgt == self.src.value)
    assert(self.src.variable not in self.tgt.freeVariables())

# a === b | A --> A.substituteVariable(a, b)
# a === b | A --> A.substituteVariable(b, a)
class SubstituteArrow(Arrow):
  def arrowTitle(self):
    return "Substitute(%s->%s)"%(self.src.left.left, self.src.left.right)
  def validate(self):
    assert(self.src.__class__ == Identical)
    a = self.src.left.left
    b = self.src.left.right
    A = self.src.right
    assert(A.substituteVariable(a, b) == self.tgt or
        A.substituteVariable(b, a) == self.tgt)

# For arrow built from the application of functors to other arrows.
class FunctorialArrow(Arrow):
  def __repr__(self):
    return self.reprAround('\n'.join(['  ' + l for l in repr(self.arrow).split('\n')]))

  def substituteVariable(self, a, b):
    return self.__class__(arrow = self.arrow.substituteVariable(a, b))

  def compress(self):
    arrow = self.arrow.compress()
    if arrow.__class__ == Id:
      return self.src.identity()
    else:
      return self.__class__(arrow = arrow)

  def reprAround(self, middle):
    return "%s {\n%s\n} %s"%(self.arrowTitle(), middle, self.arrowTitle())

def OnAnd(leftArrow, rightArrow):
  return OnConjunction(leftArrow = leftArrow, rightArrow = rightArrow,
      src = And(leftArrow.src, rightArrow.src),
      tgt = And(leftArrow.tgt, rightArrow.tgt))

def OnOr(leftArrow, rightArrow):
  return OnConjunction(leftArrow = leftArrow, rightArrow = rightArrow,
      src = Or(leftArrow.src, rightArrow.src),
      tgt = Or(leftArrow.tgt, rightArrow.tgt))

class OnConjunction(FunctorialArrow):
  def __init__(self, leftArrow, rightArrow, src, tgt):
    assert(src.__class__ in [And, Or])
    assert(src.__class__ == tgt.__class__)
    assert(leftArrow.src == src.left)
    assert(leftArrow.tgt == tgt.left)
    assert(rightArrow.src == src.right)
    assert(rightArrow.tgt == tgt.right)
    self.leftArrow = leftArrow
    self.rightArrow = rightArrow
    self.src = src
    self.tgt = tgt

  def substituteVariable(self, a, b):
    return self.__class__(
        leftArrow = self.leftArrow.substituteVariable(a, b),
        rightArrow = self.rightArrow.substituteVariable(a, b),
        src = self.src.substituteVariable(a, b),
        tgt = self.tgt.substituteVariable(a, b))

  def invert(self):
    return OnConjunction(src = self.tgt, tgt = self.src,
        leftArrow = self.leftArrow.invert(), rightArrow = self.rightArrow.invert())


  def compress(self):
    left = self.leftArrow.compress()
    right = self.rightArrow.compress()
    if left.__class__ == Id and right.__class__ == Id:
      return self.src.identity()
    else:
      return self.__class__(leftArrow = left, rightArrow = right, src = self.src, tgt = self.tgt)

  def __repr__(self):
    return self.reprAround(_hconcat(repr(self.leftArrow), repr(self.rightArrow)))

  def arrowTitle(self):
    if self.src.__class__ == And:
      return "OnAnd"
    else:
      assert(self.src.__class__ == Or)
      return "OnOr"

class OnAlways(FunctorialArrow):
  def __init__(self, arrow):
    self.arrow = arrow
    self.src = Always(arrow.src)
    self.tgt = Always(arrow.tgt)

  def invert(self):
    return OnAlways(self.arrow.invert())

  def arrowTitle(self):
    return "OnAlways"

class OnBody(FunctorialArrow):
  def __init__(self, variable, arrow):
    self.arrow = arrow
    self.variable = variable
    self.src = Exists(variable, arrow.src)
    self.tgt = Exists(variable, arrow.tgt)

  def invert(self):
    return OnBody(self.variable, self.arrow.invert())

  def compress(self):
    arrow = self.arrow.compress()
    if arrow.__class__ == Id:
      return self.src.identity()
    else:
      return OnBody(variable = self.variable, arrow = arrow)

  def arrowTitle(self):
    return "OnBody"

class OnNot(FunctorialArrow):
  def __init__(self, arrow):
    self.arrow = arrow
    self.src = Not(arrow.tgt)
    self.tgt = Not(arrow.src)

  def invert(self):
    return OnNot(self.arrow.invert())

  def arrowTitle(self):
    return "OnNot"

# The horizontal concatenation of two strings
def _hconcat(left, right):
  if len(left) == 0:
    return right
  elif len(right) == 0:
    return left
  else:
    left = left.split('\n')
    right = right.split('\n')
    lHeight = len(left)
    rHeight = len(right)
    resultHeight = max(lHeight, rHeight)
    lWidth = len(left[0])
    for line in left:
      lWidth = max(lWidth, len(line))
    result = []
    for i in range(resultHeight):
      if i < len(left):
        l = left[i]
      else:
        l = ''
      while len(l) < lWidth:
        l += ' '
      if i < len(right):
        r = right[i]
      else:
        r = ''
      result.append('  ' + l + ' | ' + r)
    return '\n'.join(result)

class Assumption:
  # return: the corresponding formula.
  def as_formula(self):
    raise Exception("Abstract superclass.")

  # an arrow self.as_formula() --> Always(self.as_formula())
  def add_always(self):
    raise Exception("Abstract superclass.")

  # return a natural transform: endofunctor -> (self.as_formula()|.) o endofunctor
  # throw an UnimportableException if the import in not possible.
  def import_assumption(self, endofunctor):
    raise Exception("Abstract superclass.")

class SingleAssumption:
  def __init__(self, formula):
    assert(formula.__class__ == Always)
    self.formula
  def as_formula(self):
    return self.formula

  def add_always(self):
    return self.as_formula().forwardCojoin()

  def import_assumption(self, endofunctor):
    return endofunctor.importExactly(self)

class CombinedAssumption(Assumption):
  def __init__(self, left, right):
    self.left = left
    self.right = right

  def as_formula(self):
    return And(self.left.as_formula(), self.right.as_formula())

  def add_always(self):
    return self.as_formula().forwardOnConjunction(
        leftArrow = self.left.add_always(),
        rightArrow = self.right.add_always()).forwardFollow(lambda x:
            x.forwardZip())

  def import_assumption(self, endofunctor):
    nt_left = self.left.import_assumption(endofunctor)
    nt_right = self.right.import_assumption(endofunctor)
    right_as_formula = self.right.as_formula()
    left_as_formula = self.left.as_formula()
    return (lambda x:
        nt_right(x).forwardCompose(nt_left(And(right_as_formula, x))).forwardCompose(
          endofunctor.onArrow(
            And( left_as_formula
               , And(right_as_formula, x)).forwardAssociateOther())))

def identity_dependent_arrow(formula):
  return DependentArrow(src = formula, tgt = formula,
      assumption = SingleAssumption(Always(true)),
      arrow = And(Always(true), formula).forwardForgetLeft())

class DependentArrow:
  # src, tgt: formulas
  # assumption: an Assumption instance.
  # arrow: an arrow: And(assumption.as_formula(), src) -> tgt
  def __init__(self, src, tgt, assumption, arrow):
    self.src = src
    self.tgt = tgt
    self.assumption = assumption
    self.arrow = arrow

  def dependent_arrow_not(self):
    src = Not(self.tgt)
    return DependentArrow(src = src, tgt = Not(self.src), assumption = self.assumption,
        arrow = And(self.assumption.as_formula(), src).forwardOnRightFollow(lambda x:
          x.forwardOnNot(self.arrow)).forwardApply())

  def always(self):
    src = Always(self.src)
    return DependentArrow(src = self.src, tgt = Not(self.tgt), assumption = self.assumption,
        arrow = And(self.assumption.as_formula(), src).forwardOnLeft(
          self.assumption.add_always()).forwardFollow(lambda x:
            x.forwardZip().forwardFollow(lambda x:
              x.forwardOnAlways(self.arrow))))

  def exists(self, variable):
    src = Exists(variable, self.src)
    return DependentArrow(src = src, tgt = Exists(variable, self.tgt), assumption = self.assumption,
        arrow = And(self.assumption.as_formula(), src).forwardAndPastExists().forwardFollow(lambda x:
          x.forwardOnBody(self.arrow)))

  def compose(self, other):
    # TODO Find formulas that appear in both self.assumption and other.assumption.
    #      and be sure not to assume them twice.
    assert(self.tgt == other.src)
    assumption = CombinedAssumption(other.assumption, self.assumption)
    return DependentArrow(src = self.src, tgt = other.tgt,
        assumption = assumption,
        arrow = And(assumption.as_formula(), self.src).forwardAssociate().forwardFollow(lambda x:
          x.forwardOnRight(self.arrow).forwardCompose(other.arrow)))

  def dependent_arrow_and(self, other):
    # TODO Find formulas that appear in both self.assumption and other.assumption.
    #      and be sure not to assume them twice.
    assumption = CombinedAssumption(other.assumption, self.assumption)
    src = And(self.src, other.src)
    return DependentArrow(src = src, tgt = And(self.tgt, other.tgt),
        assumption = assumption,
        arrow = And(assumption.as_formula(), src).forwardAssociate().forwardFollow(lambda x:
          x.forwardOnRightFollow(lambda x:
            x.forwardAssociateOther().forwardFollow(lambda x:
              x.forwardOnLeft(self.arrow).forwardFollow(lambda x:
                x.forwardCommute())))).forwardFollow(lambda x:
                  x.forwardAssociateOther().forwardFollow(lambda x:
                    x.forwardOnLeft(other.arrow).forwardFollow(lambda x:
                      x.forwardCommute()))))

  def dependent_arrow_or(self, other):
    # TODO Find formulas that appear in both self.assumption and other.assumption.
    #      and be sure not to assume them twice.
    assumption = CombinedAssumption(other.assumption, self.assumption)
    src = Or(self.src, other.src)
    return DependentArrow(src = src, tgt = Or(self.tgt, other.tgt),
        assumption = assumption,
        arrow = And(assumption.as_formula(), src).forwardAssociate().forwardFollow(lambda x:
          x.forwardOnRightFollow(lambda x:
            x.forwardDistributeLeft().forwardFollow(lambda x:
              x.forwardOnLeft(self.arrow)))).forwardFollow(lambda x:
                x.forwardDistributeRight().forwardFollow(lambda x:
                  x.forwardOnRight(other.arrow))))

