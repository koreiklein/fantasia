# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol

from sets import Set

class Object:
  # Always returns a "basic" object.
  def translate(self):
    raise Exception("Abstract superclass.")

  # return a list of arrows self --> B|self such that f(B), and for some C, B == Always(C)
  def produceFiltered(self, f):
    return []

  # Replace all bound variables with new variables.
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

  def backwardUnalways(self):
    return Unalways(tgt = self, src = Always(self))

  def forwardAdmitLeft(self, x):
    return Admit(src = self, tgt = Or(self, x))
  def forwardAdmitRight(self, x):
    return Admit(src = self, tgt = Or(x, self))

  def backwardForgetLeft(self, x):
    return Forget(tgt = self, src = And(self, x))
  def backwardForgetRight(self, x):
    return Forget(tgt = self, src = And(x, self))

  def forwardIntroExists(self, variables):
    return IntroExists(src = self, tgt = Exists(variables = variables, value = self))
  def backwardRemoveExists(self, variables):
    return RemoveExists(src = Exists(variables = variables, value = self), tgt = self)

  def identity(self):
    return Id(src = self, tgt = self)

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

class Holds(Object):
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
  def translate(self):
    return self
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

  def produceFiltered(self, f):
    result = []
    for a in self.value.produceFiltered(f):
      B = a.tgt.left
      free = B.freeVariables()
      if all([variable not in free for variable in self.variables]):
        # Exists xs. X --> Exists xs. (B|X) --> (B|Exists xs.X)
        result.append(self.forwardOnBody(a).forwardFollow(lambda x:
          AndPastExists(src = And(left = B, right = self), tgt = x).invert()))
    return result

  def forwardOnBody(self, arrow):
    assert(isinstance(arrow, Arrow))
    assert(arrow.src == self.value)
    return OnBody(variables = self.variables, arrow = arrow)
  def backwardOnBody(self, arrow):
    assert(arrow.tgt == self.value)
    return OnBody(variables = self.variables, arrow = arrow)
  def forwardOnBodyFollow(self, f):
    return self.forwardOnBody(f(self.value))
  def backwardOnBodyFollow(self, f):
    return self.backwardOnBody(f(self.value))

  def forwardRemoveExists(self):
    return RemoveExists(src = self, tgt = self.value)
  def backwardIntroExists(self):
    return IntroExists(src = self.value, tgt = self)

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

# For And and Or.
class Conjunction(Object):
  # There is only one global right symbol.
  def __init__(self, left, right):
    self.left = left
    self.right = right

  def __eq__(self, other):
    return (self.__class__ == other.__class__
        and self.left == other.left
        and self.right == other.right)
  def __ne__(self, other):
    return not(self == other)

  def translate(self):
    return self.__class__(left = self.left.translate(),
                          right = self.right.translate())

  def forwardOnConjunction(self, leftArrow, rightArrow):
    assert(isinstance(leftArrow, Arrow))
    assert(isinstance(rightArrow, Arrow))
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
  def produceFiltered(self, f):
    result = []
    # (X|Y) --> (X|(B|Y)) --> (X|(Y|B)) --> ((X|Y)|B) --> (B|(X|Y))
    result.extend([self.forwardOnRight(a.forwardFollow(lambda x:
      x.forwardCommute())).forwardFollow(lambda x:
        x.forwardAssociateOther().forwardFollow(lambda x:
          x.forwardCommute())) for a in self.right.produceFiltered(f)])
    # (X|Y) --> ((B|X)|Y) --> (B|(X|Y))
    result.extend([self.forwardOnLeft(a).forwardFollow(lambda x:
          x.forwardAssociate()) for a in self.left.produceFiltered(f)])
    return result

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
        tgt = Exists(variables = self.right.variables,
          value = And(left = self.left, right = self.right.value)))

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

  def backwardAdmitLeft(self):
    return Admit(tgt = self, src = self.right)
  def backwardAdmitRight(self):
    return Admit(tgt = self, src = self.left)

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

  def produceFiltered(self, f):
    result = []
    result.extend([self.forwardOnAlways(a).forwardFollow(lambda x:
      x.forwardDistributeAlways().forwardFollow(lambda x:
        x.forwardOnLeftFollow(lambda x:
          x.forwardUnalways()))) for a in self.value.produceFiltered(f)])
    if f(self):
      result.append(self.forwardCopy())
    return result

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

  def forwardCopy(self):
    return Copy(src = self, tgt = And(self, self))

  # !(A|B) --> !A | !B
  def forwardDistributeAlways(self):
    # !(A|B) --> !(A|B) | !(A|B) --> !A | !(A|B) --> !A | !B
    return self.forwardCopy().forwardFollow(lambda x:
        x.forwardOnLeftFollow(lambda x: x.forwardForgetRight()).forwardFollow(lambda x:
          x.forwardOnRightFollow(lambda x: x.forwardForgetLeft())))

  def forwardCojoin(self):
    return Cojoin(src = self, tgt = Always(self))

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
    self.src = arrow.tgt
    self.tgt = arrow.src

  def invert(self):
    return self.arrow

  def translate(self):
    return InverseArrow(arrow = self.arrow.translate())

# A <--> A
class Id(Arrow):
  def validate(self):
    assert(self.src == self.tgt)

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
    if not(self.left.tgt == self.right.src):
      raise Exception(("Invalid composite."
          "left.tgt (%s) != right.src (%s)\nleft.tgt =\n%s\nright.src =\n%s"
          )%(self.left.__class__, self.right.__class__, self.left.tgt, self.right.src))

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

# A | B --> A,  A | B --> B
class Forget(Arrow):
  def validate(self):
    assert(self.src.__class__ == And)
    assert(self.tgt in [self.src.left, self.src.right])

# A - B <-- A,  A - B <-- B
class Admit(Arrow):
  def validate(self):
    assert(self.src.__class__ == Or)
    assert(self.src in [self.tgt.left, self.tgt.right])

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
    common_class = self.src.__class__
    assert(self.src.left.__class__ == common_class
        and self.tgt.right.__class__ == common_class

        and self.src.left.left == self.tgt.left
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

# !A --> !!A
class Cojoin(Arrow):
  def validate(self):
    assert(self.src.__class__ == Always)
    assert(self.tgt.__class__ == Always)
    assert(self.src == self.tgt.value)

# !A --> !A | !A
class Copy(Arrow):
  def validate(self):
    assert(self.src.__class__ == Always)
    assert(self.tgt.__class__ == And)
    assert(self.tgt.left == self.src)
    assert(self.tgt.right == self.src)

# !A | !B --> !(A|B)
class Zip(Arrow):
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
  def validate(self):
    assert(self.src.__class__ == Always)
    assert(self.src.value == self.tgt)

# A --> Exists x . A
class IntroExists(Arrow):
  def validate(self):
    assert(self.tgt.__class__ == Exists)
    assert(self.src == self.tgt.value)

# (A|Exists xs. B) --> Exists xs. (A|B)
class AndPastExists(Isomorphism):
  def validate(self):
    assert(self.src.__class__ == And)
    assert(self.tgt.right.__class__ == Exists)
    assert(self.tgt.__class__ == Exists)
    assert(self.tgt.value.__class__ == And)
    assert(self.src.left == self.tgt.value.left)
    assert(self.src.right.variables == self.tgt.variables)

# Exists x . A --> A
class RemoveExists(Arrow):
  def validate(self):
    assert(self.src.__class__ == Exists)
    assert(self.tgt == self.src.value)
    free = self.tgt.freeVariables()
    for variable in self.src.variables:
      assert(variable not in free)

# For arrow built from the application of functors to other arrows.
class FunctorialArrow(Arrow):
  def translate(self):
    raise Exception("Abstract superclass.")

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

  def translate(self):
    return OnConjunction(leftArrow = self.leftArrow.translate(),
        rightArrow = self.rightArrow.translate(),
        src = self.src.translate(),
        tgt = self.tgt.translate())

class OnAlways(FunctorialArrow):
  def __init__(self, arrow):
    self.arrow = arrow
    self.src = Always(arrow.src)
    self.tgt = Always(arrow.tgt)

  def translate(self):
    return OnAlways(self.arrow.translate())

class OnBody(FunctorialArrow):
  def __init__(self, variables, arrow):
    self.arrow = arrow
    self.variables = variables
    self.src = Exists(variables, arrow.src)
    self.tgt = Exists(variables, arrow.tgt)

  def translate(self):
    return OnBody([variable.translate() for variable in self.variables],
        self.arrow.translate())

class OnNot(FunctorialArrow):
  def __init__(self, arrow):
    self.arrow = arrow
    self.src = Not(arrow.tgt)
    self.tgt = Not(arrow.src)

  def translate(self):
    return OnNot(arrow = self.arrow.translate())

