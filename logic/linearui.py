# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import markable
from logic import linear

# This module contains objects and arrows in much the same was as linear.
# This module defines a functor F.
# F assigns to every object in this module, an object in linear.
# F also assigns to every arrow in this module an arrow in linear.
# F satifies all the appropriate properties for a functor
#     (it respects src, tgt, identity, and composition)
# We use x.translate() to implement F.

class Var(markable.Markable):
  def __init__(self, name):
    self._base = linear.Var(name)
    self.initMarkable([])

  def translate(self):
    return self._base

  def name(self):
    return self.translate().name()

  def __eq__(self, other):
    return other.__class__ == Var and self._base == other._base
  def __ne__(self, other):
    return not (self == other)

#Objects

class Logic(markable.Markable):
  # return F(self)
  def translate(self):
    raise Exception("Abstract Superclass")

  # Note: There is an isomorphism:
  #   linear.Not(self.translate()) <--> self.transpose().translate()
  # notToTranspose implements the forward direction of this isomorphism.
  # transposeToNot implements the reverse direction of this isomorphism.
  def notToTranspose(self):
    raise Exception("Abstract Superclass")
  def transposeToNot(self):
    raise Exception("Abstract Superclass")

  # return a claim dual to self.
  # note: self.transpose().transpose() must be equal to self.
  def transpose(self):
    raise Exception("Abstract Superclass")
  # Return a Logic object like this one, but with the variable b substituted in
  # place of a.
  # a must not be quantified in self.
  def substituteVar(self, a, b):
    raise Exception("Abstract Superclass")

  def backwardRemoveQuantifier(self, quantifierType):
    return RemoveQuantifier(value = self, quantifierType = quantifierType)

  def identity(self):
    return Identity(self)

forallType = linear.forallType
existsType = linear.existsType

# Possible types of a Conj
andType = 'AND'
orType = 'OR'
withType = 'WITH'
parType = 'PAR'

forallType = linear.forallType
existsType = linear.existsType

conjTypes = [andType, orType, withType, parType]
concreteConjTypes = [andType, orType]
demorganedConjTypes = [withType, parType]

def dualQuantifierType(type):
  if type == forallType:
    return existsType
  else:
    assert(type == existsType)
    return forallType

def dualConjType(type):
  if type == andType:
    return parType
  elif type == parType:
    return andType
  elif type == orType:
    return withType
  else:
    assert(type == withType)
    return orType

# type: the type of a Conj c
# return: the type of a linear.Conj that can be used to represent c.
def correspondingConcreteTypeInLinear(type):
  if type == andType:
    return linear.andType
  elif type == orType:
    return linear.orType
  elif type == withType:
    return linear.orType
  else:
    assert(type == parType)
    return linear.andType

# For stylistic reasons, try to use Not sparingly.
# Ideally, self.value() should never be a Conj, Quantifier, Maybe or Always.
class Not(Logic):
  def __init__(self, value):
    self._value = value
    self.initMarkable(['value'])

  def value(self):
    return self._value

  def substituteVar(self, a, b):
    return Not(self.value().substituteVar(a, b))

  def translate(self):
    return linear.Not(self.value().translate())

  def notToTranspose(self):
    return linear.Not(self.translate()).forwardRemoveDoubleDual().forwardCompose(
        self.value().transpose().transposeToNot())
  def transposeToNot(self):
    return self.transpose().translate().forwardOnNot(self.value().notToTranspose())
  def transpose(self):
    return self.value()

# This one class will is used to represent
# n-ary AND, OR, WITH and PAR
class Conj(Logic):
  # type in ['AND', 'OR', 'WITH', 'PAR']
  def __init__(self, type, values):
    if type in concreteConjTypes:
      self._demorganed = False
    else:
      # F uses demorgan's laws to translate a demorganed Conj into an object in linear.
      # See Conj.translate()
      assert(type in demorganedConjTypes)
      self._demorganed = True
    self._type = type
    self._values = values
    self.initMarkable(self.generateMethodNamesForList('value', values))

  def forwardForget(self, index):
    assert(self.type() in [andType, withType])
    return Forget(self, index)
  def backwardForget(self, index, value):
    values = list(self.values())
    values.insert(index, value)
    return Forget(Conj(type = self.type(), values = values), index)

  def forwardApply(self, i, j):
    assert(self.type() == andType)
    return Apply(values = self.values(), i = i, j = j)

  def forwardShift(self, index, amount):
    return Shift(conj = self, index = index, amount = amount)
  def backwardShift(self, index, amount):
    # Clever.
    res = self.forwardShift(index = index, amount = amount).tgt().forwardShift(
        index = index + amount, amount = -amount)
    res.translate()
    return res

  def forwardAssociateIn(self, index):
    # [A, [B, C], D] --> [A, B, C, D]
    return AssociateIn(self, index)

  def forwardOnIthFollow(self, index, f):
    return self.forwardOnIth(index, f(self.values()[index]))

  def forwardOnIth(self, index, t):
    return OnIth(self, index, t)

  def forwardConjQuantifier(self, index):
    return ConjQuantifier(conj = self, index = index)

  def forwardImportToPar(self, i, j, k):
    assert(self.type() == andType)
    return ImportToPar(self.values(), i, j, k)

  def substituteVar(self, a, b):
    return Conj(type = self.type(),
        values = [value.substituteVar(a, b) for value in self.values()])

  def notToTranspose(self):
    if not self.demorganed():
      return linear.Not(self.translate()).forwardOnNotFollow(lambda values:
          _valuesToTransposeNot(self.type(), values, self.values()))
    else:
      return linear.Not(self.translate()).forwardRemoveDoubleDual()

  def transposeToNot(self):
    if not self.demorganed():
      return self.transpose().translate().forwardOnNotFollow(lambda values:
          _transposeNotToValues(self.type(), values, self.values()))
    else:
      return self.transpose.translate().forwardIntroduceDoubleDual()

  def transpose(self):
    return Conj(type = dualConjType(self.type()),
      values = [value.transpose() for value in self.values()])

  def demorganed(self):
    return self._demorganed
  def type(self):
    return self._type
  def values(self):
    return self._values

  def translate(self):
    if self.demorganed():
      return self.translateDemorganed()
    else:
      return self.translateUndemorganed()

  def translateDemorganed(self):
    linearType = correspondingConcreteTypeInLinear(self.type())
    res = linear.unit(linearType)
    for value in self.values():
      res = linear.Conj(type = linearType, left = res, right = linear.Not(value.translate()))
    return linear.Not(res)

  def translateUndemorganed(self):
    linearType = correspondingConcreteTypeInLinear(self.type())
    res = linear.unit(linearType)
    for value in self.values():
      res = linear.Conj(type = linearType, left = res, right = value.translate())
    return res

# e.g.
# (1 | B.translate()) | C.translate(), [B, C]
#      -->
# (1 | ~B.transpose().translate()) | ~C.transpose().translate()
def _valuesToTransposeNot(type, linearConjOrUnit, linearUiValues):
  if linearConjOrUnit == linear.unit(type):
    assert(len(linearUiValues) == 0)
    return linearConjOrUnit.identitiy()
  else:
    conj = linearConjOrUnit
    assert(conj.__class__ == linear.Conj)
    assert(conj.type() == type)
    last = linearUiValues[-1]
    return conj.forwardOnRight(last.transpose().transposeToNot()).forwardFollow(lambda conj:
        conj.forwardOnLeftFollow(lambda rest:
          _valuesToTransposeNot(type, rest, linearUiValues[:-1])))
# e.g.
# (1 | B.translate()) | C.translate() <-- (1 | ~B.transpose().translate()) | ~C.transpose().translate()
def _transposeNotToValues(type, linearConjOrUnit, linearUiValues):
  if linearConjOrUnit == linear.unit(type):
    assert(len(linearUiValues) == 0)
    return linearConjOrUnit.identitiy()
  else:
    conj = linearConjOrUnit
    assert(conj.__class__ == linear.Conj)
    assert(conj.type() == type)
    last = linearUiValues[-1]
    return conj.forwardOnRight(last.transpose().notToTranspose()).forwardFollow(lambda conj:
        conj.forwardOnLeftFollow(lambda rest:
          _transposeNotToValues(type, rest, linearUiValues[:-1])))

true = Conj(type = andType, values = [])
false = Conj(type = orType, values = [])

class Quantifier(Logic):
  def __init__(self, type, variables, body):
    assert(type in linear.quantifierTypes)
    self._type = type
    self._variables = variables
    self._body = body
    l = self.generateMethodNamesForList('variables', variables)
    l.append('body')
    self.initMarkable(l)

  def notToTranspose(self):
    return _forwardPushNotFollow(len(self.variables()), linear.Not(self.translate()), lambda notBody:
        self.body().notToTranspose())
  def transposeToNot(self):
    return self.transpose().translate().forwardIntroduceDoubleDual().forwardFollow(lambda notNotQ:
        notNotQ.forwardOnNotFollow(lambda notQ:
          _backwardPullNotFollow(len(self.variables()), notQ, lambda bodyTranspose:
          self.body().transpose().transposeToNot())))

  def transpose(self):
    return Quantifier(type = dualQuantifierType(self.type()),
        variables = self.variables(),
        body = self.body().transpose())

  def forwardRemoveQuantifier(self):
    assert(len(self.variables()) == 0)
    return RemoveQuantifier(value = self.body(), quantifierType = self.type())

  def forwardEliminate(self, index, replacementVar):
    assert(self.type() == forallType)
    return Eliminate(quantifier = self, index = index, replacementVar = replacementVar)

  def backwardEliminate(self, index, quantifiedVar, replacementVar):
    assert(self.type() == forallType)
    variables = list(self.variables())
    variables.insert(index, quantifiedVar)
    return Eliminate(quantifier = Quantifier(type = forallType, variables = variables,
      body = self.body().substituteVar(replacementVar, quantifiedVar)),
      index = index,
      replacementVar = replacementVar)

  def forwardOnBodyFollow(self, f):
    return self.forwardOnBody(f(self.body()))

  def forwardOnBody(self, t):
    return OnBody(self.type(), self.variables(), t)

  def substituteVar(self, a, b):
    assert(a not in self.variables())
    return Quantifier(type = self.type(),
        variables = self.variables(),
        body = self.body().substituteVar(a, b))

  def type(self):
    return self._type
  def variables(self):
    return self._variables
  def body(self):
    return self._body

  def translate(self):
    res = self.body().translate()
    for variable in self.variables():
      res = linear.Quantifier(type = self.type(), var = variable.translate(), body = res)
    return res

# e.g.
# | q(t, a, q(t, b, x))  -->  q(~t, a, q(~t, b, f(~x).tgt()))
# *--------------------
def _forwardPushNotFollow(n, linearObject, f):
  if n == 0:
    return f(linearObject)
  else:
    assert(n > 0)
    assert(linearObject.__class__ == linear.Not)
    return linearObject.forwardNotQuant().forwardFollow(lambda quant:
        quant.onBody(_forwardPushNotFollow(n - 1, quant.body(), f)))

# e.g.
# | q(t, a, q(t, b, x))  <--  q(~t, a, q(~t, b, f(x).src()))
# *--------------------
def _backwardPullNotFollow(n, linearObject, f):
  if n == 0:
    res = f(linearObject)
    assert(res.tgt().__class__ == linear.Not)
    return res
  else:
    assert(linearObject.__class__ == linear.Not)
    return linearObject.backwardNotQuant().backwardFollow(lambda quant:
      _backwardPullNotFollow(n - 1, quant, f))

class Always(Logic):
  def __init__(self, value):
    self._value = value
    self.initMarkable(['value'])

  def notToTranspose(self):
    return linear.Not(self.translate()).forwardOnNotFollow(lambda alwaysValue:
        alwaysValue.backwardOnAlwaysFollow(lambda value:
          self.value().transpose().notToTranspose()))
  def transposeToNot(self):
    return self.transpose().translate().forwardOnNotFollow(lambda alwaysNotValueTranspose:
        alwaysNotValueTranspose.backwardOnAlwaysFollow(lambda notValueTranspose:
          self.value().transpose().transposeToNot()))

  def transpose(self):
    return Maybe(self.value().transpose())

  def substituteVar(self, a, b):
    return Always(self.value().substituteVar(a, b))

  def value(self):
    return self._value

  def translate(self):
    return linear.Always(self.value().translate())

class Maybe(Logic):
  def __init__(self, value):
    self._value = value
    self.initMarkable(['value'])

  def notToTranspose(self):
    return linear.Not(self.translate()).forwardRemoveDoubleDual().forwardFollow(lambda alwaysNotValue:
        alwaysNotValue.forwardOnAlwaysFollow(lambda notValue:
          self.value().notToTranspose()))
  def transposeToNot(self):
    return self.transpose().translate().forwardOnAlways(
        self.value().transposeToNot()).forwardFollow(lambda x: x.forwardIntroduceDoubleDual())

  def substituteVar(self, a, b):
    return Maybe(self.value().substituteVar(a, b))

  def transpose(self):
    return Always(self.value().transpose())

  def value(self):
    return self._value

  def translate(self):
    return linear.Not(linear.Always(linear.Not(self.value().translate())))

# Utilities for contstructing linearui objects.
def And(values):
  return Conj(type = andType, values = values)
def Or(values):
  return Conj(type = orType, values = values)
def With(values):
  return Conj(type = withType, values = values)
def Par(values):
  return Conj(type = parType, values = values)

def Forall(variables, body):
  return Quantifier(type = forallType, variables = variables, body = body)
def Exists(variables, body):
  return Quantifier(type = existsType, variables = variables, body = body)

def Implies(predicate, consequent):
  if predicate.__class__ == Conj and predicate.type() == andType:
    values = [value.transpose() for value in predicate.values()]
    values.append(consequent)
    return Par(values)
  else:
    return Par([predicate.transpose(), consequent])

# Arrows

# Abstract superclass of all nonfunctorial arrows between linear logic ui objects.
class LinearLogicUiPrimitiveArrow:
  def src(self):
    raise Exception("Abstract superclass.")
  def tgt(self):
    raise Exception("Abstract superclass.")
  def __repr__(self):
    raise Exception("Abstract superclass.")

  # other is another arrow.
  def forwardCompose(self, other):
    return compose(left = self, right = other)
  # other is another arrow.
  def backwardCompose(self, other):
    return compose(left = other, right = self)

  # f is a function taking self.tgt() to an arrow other such that self . other exists
  # return self . other
  def forwardFollow(self, f):
    return self.forwardCompose(f(self.tgt()))
  # f is a function taking self.src() to an arrow other such that other . self exists
  # return other . self
  def backwardFollow(self, f):
    return self.backwardCompose(f(self.src()))

class LinearLogicUiFunctorialArrow(LinearLogicUiPrimitiveArrow):
  pass

class Identity(LinearLogicUiPrimitiveArrow):
  def __init__(self, value):
    self._value = value

  def src(self):
    return self._value
  def tgt(self):
    return self._value
  def translate(self):
    return self._value.translate().identity()

class Distribute(LinearLogicUiPrimitiveArrow):
  # Import claim i of the list into each clause of the OR at spot j.
  # If the disjunction is par, values[i] must be exponential.
  # e.g.  [A, B, C, D0 - D1 - D2, E], 1, 3
  #   [A | B | C | D0 - D1 - D2 | E] ---> [A | C | ((D0 | B) - (D1 | B) - (D2 | B)) | E]
  def __init__(self, values, i, j):
    assert(i != j)
    assert(values[j].__class__ == Conj)
    assert(values[j].type() == orType)
    assert(0 <= i and i < len(values))
    assert(0 <= j and j < len(values))
    self._values = values
    self._i = i
    self._j = j

  def src(self):
    return Conj(type = andType, values = self._values)
  def tgt(self):
    values = list(self._values)
    values[j] = Or([ And([v, values[i]]) for v in values[j].values() ])
    values.pop(i)
    return Conj(type = andType, values = values)

  def translate(self):
    J = j
    if i < j:
      J -= 1
    values = [v for v in self.tgt().values()]
    tmp = values[J]
    values[J] = values[0]
    values[0] = tmp

    return _onJandI(self.src(), j, i, _distribute).forwardCompose(
        Shift(conj = And(values), index = 0, amount = J).translate())

# conj is a linear disjunctive list and a claim of the form (((- - a) - b) - c) | claim
# return a linear arrow: (((- - a) - b) - c) | claim --> (((- - (a|claim)) - (b|claim)) - (c|claim))
def _distribute(conj):
  assert(conj.__class__ == linear.Conj)
  assert(conj.type() == linear.andType)
  if conj.left() == linear.false:
    return conj.forwardForget()
  else:
    assert(conj.left().__class__ == linear.Conj)
    assert(conj.left().type() == linear.orType)
    return conj.forwardDistribute().forwardFollow(lambda x:
          x.onLeft(_distribute(x.left())))

class ImportToPar(LinearLogicUiPrimitiveArrow):
  # Import claim i of the list into the kth clause of the PAR at spot j.
  # If the disjunction is par, values[i] must be exponential.
  # e.g.  [A, B, C, D0 - D1 - D2, E], 1, 3, 0
  #   [A | B | C | D0 - D1 - D2 | E] ---> [A | C | ((D0 | B) - D1 - D2) | E]
  def __init__(self, values, i, j, k):
    assert(values[j].__class__ == Conj)
    assert(values[j].type() == parType)
    assert(i != j)
    assert(0 <= i and i < len(values))
    assert(0 <= j and j < len(values))
    assert(0 <= k and k < len(values[j].values()))
    self._values = values
    self._i = i
    self._j = j
    self._k = k

  def src(self):
    return And(self._values)
  def tgt(self):
    kidValues = list(self._values[self._j].values())
    kidValues[self._k] = And([kidValues[self._k], self._values[self._i]])
    values = list(self._values)
    values[self._j] = Par(kidValues)
    values.pop(self._i)
    return And(values)

  def translate(self):
    if self._i < self._j:
      T = self._j - 1
    else:
      T = self._j

    def f(parAndClaim):
      return parAndClaim.forwardOnLeftFollow(lambda par:
          par.forwardOnNotFollow(lambda conj:
            _backwardBringToRight(conj, len(self._values[self._j].values()) - self._k - 1, lambda x:
              x.backwardOnRightFollow(lambda kClaim:
                kClaim.backwardOnNotFollow(lambda x:
                  x.forwardIntroduceTrue().forwardFollow(lambda x:
                  x.forwardCommute())).backwardFollow(lambda oneAndKClaim:
                oneAndKClaim.backwardApply(parAndClaim.right()))).backwardFollow(lambda x:
                  x.backwardAssociateA())))).forwardFollow(lambda x: x.forwardApply())
    return _onJandI(self.src(), j = self._j, i = self._i, linearTransitionF = f).forwardCompose(
        self.tgt().backwardShift(index = T, amount = -T).translate())

# conjOrUnit: a linear conj of the form (((1 | A) | B) | C) | D
# outer: an integer
# f: a function from a linear conj to a linear conj
# return: a linear transition from a  conj like conjOrUnit,
#         but in which f was applied to the outerth claim,
#         and the right side of the result was commuted and associated all the way to the right.
# e.g.
# _backwardBringToRight(  ((1 | A) | B) | C, 1, f ) == ( Z | C) | K
#       where f( (1 | A) | B ) = Z | K
def _backwardBringToRight(conjOrUnit, outer, f):
  if outer == 0:
    return f(conjOrUnit)
  else:
    assert(outer > 0)
    return conjOrUnit.backwardOnLeftFollow(lambda left:
        _backwardBringToRight(left, outer - 1, f)).backwardFollow(lambda x:
            x.backwardAssociateB().backwardFollow(lambda x:
              x.backwardOnRightFollow(lambda right:
                right.backwardCommute())).backwardFollow(lambda x:
                  x.backwardAssociateA()))

# conj: a linearui.Conj
# i, j: i != j, are indices into the values of conj
# linearTransitionF: a function generating a linear transition from:
#     (conj.values()[j].translate() | conj.values()[i].translate())
#   to any linear object L.
# return: a transition with src conj.translate() which removes the ith and jth elements and leaves
#         L at the front.
def _onJandI(conj, j, i, linearTransitionF):
  assert(conj.__class__ == Conj)
  assert(i != j)
  assert(0 <= i and i < len(conj.values()))
  assert(0 <= j and j < len(conj.values()))
  if i < j:
    b = 1
  else:
    b = 0
  return Shift(conj = conj, index = j, amount = -j).forwardFollow(lambda conj:
      Shift(conj = conj, index = i + b, amount = 1 - (i + b))).translate().forwardFollow(lambda x:
        _forwardWithin(x, len(conj.values()) - 2, lambda x:
        # x = (% % values[j]) % values[i]
        x.forwardAssociateA().forwardFollow(lambda x:
        # x = % % (values[j] % values[i])
        x.forwardOnRightFollow(linearTransitionF))))

class RemoveQuantifier(LinearLogicUiPrimitiveArrow):
  def __init__(self, value, quantifierType):
    self._value = value
    self._quantifierType = quantifierType

  def src(self):
    return Quantifier(type = self._quantifierType, variables = [], body = self._value)
  def tgt(self):
    return self._value

  def translate(self):
    return self.src().translate().identity()

class ConjQuantifier(LinearLogicUiPrimitiveArrow):
  # move the quantifier at the given index in conj to just outside the conj
  def __init__(self, conj, index):
    assert(conj.values()[index].__class__ == Quantifier)
    if conj.type() == andType:
      assert(conj.values()[index].type() == existsType)
    elif conj.type() == orType:
      assert(conj.values()[index].type() == forallType)
    else:
      raise Exception("Not yet implemented: move a quantifier outside from within a" +
          " demorganed Conj.")
    self._conj = conj
    self._index = index

  def conj(self):
    return self._conj
  def index(self):
    return self._index

  def quantifier(self):
    return self.conj().values()[self.index()]

  def src(self):
    return self.conj()
  def tgt(self):
    values = list(self.conj().values())
    values[self.index()] = self.quantifier().body()
    return Quantifier(type = self.quantifier().type(), variables = self.quantifier().variables(),
        body = Conj(type = self.conj().type(), values = values))

  # Note: Though this method generates a linear transition of quadratic size,
  #       extraction can safely convert the entire linear transition into the identity
  #       program transformation.  Therefore, there is no performance penalty.
  def translate(self):
    return _conjQuantifierWithin(linearConj = self.src().translate(),
        m = len(self.quantifier().variables()),
        n = len(self.conj().values()) - (self.index() + 1))

# linearConj: a linear Conj object containing a linear quantifier object
# m: an integer, the number of nested quantifiers.
# n: an integer, the number of nested conjs.
#   e.g. m = 2, n = 2, linearConj = ((((1|a)|b) | (exists x. exists y. c)) | d) | e
# return: a linearConj where the quantifiers have been moved to the outside
#   e.g. exists x. exists y.  ((((1|a)|b)|c)|d)|e
def _conjQuantifierWithin(linearConj, m, n):
  if n == 0:
    return linearConj.forwardCommute().forwardFollow(lambda claim:
        _conjQuantifier(claim, m)).forwardFollow(lambda claim:
            _quantifierWithin(claim, m, lambda claim:
              claim.forwardCommute()))
  else:
    return linearConj.forwardOnLeftFollow(lambda left:
        _conjQuantifierWithin(left, m, n - 1)).forwardFollow(lambda claim:
            _conjQuantifier(claim, m))

# m: an integer
# linearConj: a linear conj with m nested quantifiers as its left argument.
#  e.g. m = 2, linearConj = (  exists x. exists y. a )  | b
def _conjQuantifier(linearConj, m):
  if m == 0:
    return linearConj.identity()
  else:
    return linearConj.forwardConjQuantifier().forwardFollow(lambda claim:
        claim.forwardOnBodyFollow(lambda claim:
          _conjQuantifier(claim, m - 1)))

class Eliminate(LinearLogicUiPrimitiveArrow):
  # Replace one quantified variable with a variable in scope
  def __init__(self, quantifier, index, replacementVar):
    assert(quantifier.type() == forallType)
    assert(0 <= index)
    assert(index < len(quantifier.variables()))
    self._quantifier = quantifier
    self._index = index
    self._replacementVar = replacementVar

  def quantifier(self):
    return self._quantifier
  def index(self):
    return self._index
  def replacementVar(self):
    return self._replacementVar

  def src(self):
    return self.quantifier()
  def tgt(self):
    variables = list(self.quantifier().variables())
    quantifiedVar = variables.pop(self.index())
    return Quantifier(type = forallType, variables = variables,
        body = self.quantifier().body().substituteVar(quantifiedVar, self.replacementVar()))

  def translate(self):
    return _quantifierWithin(self.src().translate(), self.index(), lambda linearBody:
        linearBody.forwardEliminteVar(replacementVar = self.replacementVar().translate()))

class Unsingleton(LinearLogicUiPrimitiveArrow):
  # clever: we cheat by reversing the translated Singleton transition.
  def __init__(self, a, type):
    self._singleton = Singleton(a, type)

  def src(self):
    return self._singleton.tgt()
  def tgt(self):
    return self._singleton.src()
  def translate(self):
    res = linear.reverse(self._singleton.translate())
    assert(res is not None)
    return res

class Singleton(LinearLogicUiPrimitiveArrow):
  # type in conjTypes
  # a ---> [ a ]
  def __init__(self, a, type):
    assert(type in conjTypes)
    self._type = type
    self._a = a

  def type(self):
    return self._type
  def a(self):
    return self._a

  def src(self):
    return self.a()
  def tgt(self):
    return Conj(type = self.type(), values = [self.a()])

  def translate(self):
    if self.type() == andType:
      return self.src().translate().forwardIntroduceTrue().forwardFollow(lambda l:
          l.forwardCommute())
    elif self.type() == orType:
      return self.tgt().translate().backwardCommute().backwardFollow(lambda l:
          l.backwardRemoveFalse())
    elif self.type() == withType:
      return self.src().translate().forwardIntroduceDoubleDual().forwardFollow(lambda l:
          l.forwardOnNotFollow(lambda l:
            l.backwardRemoveFalse().backwardFollow(lambda l:
              l.backwardCommute())))
    elif self.type() == parType:
      return self.tgt().translate.backwardRemoveDoubleDual().backwardFollow(lambda l:
          l.backwardOnNotFollow(lambda l:
            l.forwardCommute().forwardFollow(lambda l:
              l.forwardIntroduceTrue())))
    else:
      raise Exception("Unrecognized self.type()")

class AssociateOut(LinearLogicUiPrimitiveArrow):
  # e.g. index = 1
  # [A, B, C, D] --> [A, [B, C], D]
  # We are clever, we cheat by reversing the translated associateIn transition.
  # conj: the tgt conj
  # index: the index of the first thing associated out
  def __init__(self, conj, index):
    self._associateIn = AssociateIn(conj, index)

  def src(self):
    return self._associateIn.tgt()
  def tgt(self):
    return self._associateIn.src()

  def translate(self):
    res = linear.reverse(self._associateIn.translate())
    assert(res is not None)
    return res

class AssociateIn(LinearLogicUiPrimitiveArrow):
  # e.g. index = 1
  # [A, [B, C], D] --> [A, B, C, D]
  def __init__(self, conj, index):
    assert(conj.__class__ == Conj)
    assert(0 <= index and index < len(conj.values()))
    assert(conj.values()[index].__class__ == Conj)
    assert(conj.values()[index].type() == conj.type())
    self._src = conj
    self._index = index

  def index(self):
    return self._index

  def src(self):
    return self._src
  def tgt(self):
    values = []
    for i in range(self.index()):
      values.append(self.src().values()[i])
    values.extend(self.src().values()[self.index()].values())
    for i in range(self.index() + 1, len(self.src().values())):
      values.append(self.src().values()[i])
    return Conj(type = self.src().type(), values = values)

  def translate(self):
    stationary = len(self.src().values()) - (self.index() + 1)
    if self.src().demorganed():
      linearObject = self.src().translate()
      assert(linearObject.__class__ == linear.Not)
      return linearObject.forwardOnNot(
          _backwardWithin(linearObject.value(), stationary, _backwardAssociate))
    else:
      return _forwardWithin(self.src().translate(), stationary, _forwardAssociate)

def _forwardAssociate(linearObject):
  if linearObject.right().__class__ != linear.Conj:
    if linearObject.right() == linear.true:
      assert(linearObject.type() == linear.andType)
      return linearObject.forwardForget()
    else:
      assert(linearObject.right() == linear.false)
      assert(linearObject.type() == linear.orType)
      return linearObject.forwardRemoveFalse()
  else:
    return linearObject.forwardAssociateB().forwardFollow(lambda linearObject:
        linearObject.forwardOnLeft(_forwardAssociate(linearObject.left())))

def _backwardAssociate(linearObject):
  if linearObject.right().__class__ != linear.Conj:
    if linearObject.right() == linear.true:
      assert(linearObject.type() == linear.andType)
      return linearObject.backwardIntroduceTrue()
    else:
      assert(linearObject.right() == linear.false)
      assert(linearObject.type() == linear.orType)
      return linearObject.backwardAdmit()
  else:
    return linearObject.backwardAssociateA().backwardFollow(lambda linearObject:
        linearObject.backwardOnLeft(_backwardAssociate(linearObject.left())))

class Apply(LinearLogicUiPrimitiveArrow):
  # Apply claim at spot i to the claim within the Not at spot j to get false.
  def __init__(self, values, i, j):
    assert(i != j)
    assert(values[j].__class__ == Not)
    assert(values[j].value() == values[i])
    self._values = values
    self._i = i
    self._j = j

  def values(self):
    return self._values
  def i(self):
    return self._i
  def j(self):
    return self._j

  def src(self):
    return Conj(type = andType, values = self.values())
  def tgt(self):
    return false

  def translate(self):
    # first, forget everything else:
    a = min(self.i(), self.j())
    b = max(self.i(), self.j())
    t = self.src().identity()
    for i in range(0, a):
      t = t.forwardFollow(lambda claim: claim.forwardForget(0))
    for i in range(a + 1, b):
      t = t.forwardForget(lambda claim: claim.forwardForget(1))
    for i in range(b + 1, len(self.values())):
      t = t.forwardForget(lambda claim: claim.forwardForget(2))

    # next, insure that claim j comes first
    if self.i() < self.j():
      t = t.forwardShift(index = 0, amount = 1)

    return t.translate().forwardFollow(lambda claim:
        claim.forwardOnLeftFollow(lambda claim:
          claim.forwardForgetFirst().forwardFollow(lambda claim:
            claim.forwardOnNotFollow(lambda claim:
              claim.backwardForgetFirst(linear.true))))).forwardFollow(lambda claim:
        claim.forwardApply())

class Forget(LinearLogicUiPrimitiveArrow):
  def __init__(self, conj, index):
    assert(self._conj.type() in [andType, withType])
    self._conj = conj
    self._index = index

  def conj(self):
    return self._conj
  def index(self):
    return self._index

  def src(self):
    return self.conj()
  def tgt(self):
    values = list(self.conj().values())
    values.pop(self.index())
    return Conj(type = self.conj().type(), values = values)

  def translate(self):
    if self.conj().type() == andType:
      return _forwardWithin(self.src().translate(),
          len(self.conj().values()) - (self.index() + 1), lambda claim:
            claim.forwardForget())
    else:
      assert(self.conj().type() == withType)
      return self.src().translate().forwardOnNotFollow(lambda conj:
          _backwardWithin(conj, len(self.conj().values()) - (self.index() + 1), lambda claim:
            claim.backwardAdmit()))

# An arrow that moves the indexth element of values forward amount places in the list of values.
# amount may be negative or 0.
class Shift(LinearLogicUiPrimitiveArrow):
  # e.g. index = 1, amount = 2
  # [A, B, C, D, E] ---> [A, C, D, B, E]
  # e.g. index = 1, amount = -1
  # [A, B, C, D, E] ---> [B, A, C, D, E]
  # conj: the src Conj of this arrow.
  def __init__(self, conj, index, amount):
    assert(conj.__class__ == Conj)
    assert(0 <= index and index < len(conj.values()))
    assert(0 <= index + amount)
    assert(index + amount < len(conj.values()))
    self._src = conj
    self._index = index
    self._amount = amount

  def index(self):
    return self._index
  def amount(self):
    return self._amount

  def src(self):
    return self._src
  def tgt(self):
    values = list(self._src.values())
    index = self.index()
    amount = self.amount()
    while abs(amount) > 0:
      direction = amount / abs(amount) # 1 or -1
      tmp = values[index]
      values[index] = values[index + direction]
      values[index + direction] = tmp
      index += direction
      amount -= direction
    return Conj(type = self.src().type(), values = values)

  def translate(self):
    if self.amount() == 0:
      return self.src().translate().identity()
    elif abs(self.amount()) == 1:
      return self.translate1()
    else:
      direction = self.amount() / abs(self.amount())
      return Shift(conj = self.src(), index = self.index(),
          amount = direction).forwardFollow(lambda conj:
              Shift(conj = conj,
                index = self.index() + direction,
                amount = self.amount() - direction)).translate()

  # exactly like self.translate, but with the additional requirement that abs(self.amount() == 1)
  def translate1(self):
    # Be careful analysing this code, these sequenced ifs cover 4 cases which you'll need to
    # reason about.
    # In all 4 cases, we will swap the order to two adjancent elements of self.src().translate().
    # The first if determines how many values are to the right of the swapped elements.
    # The second if deals with demorganed Conjs and contravariance.
    if self.amount() == 1:
      stationary = len(self.src().values()) - (self.index() + self.amount() + 1)
    else:
      assert(self.amount() == -1)
      stationary = len(self.src().values()) - (self.index() + 1)

    if self.src().demorganed():
      linearObject = self.src().translate()
      assert(linearObject.__class__ == linear.Not)
      return linearObject.forwardOnNot(
          _backwardWithin(linearObject.value(), stationary, _backwardSwap))
    else:
      return _forwardWithin(self.src().translate(), stationary, _forwardSwap)

def _forwardWithin(linearObject, stationary, f):
  if stationary > 0:
    return linearObject.forwardOnLeftFollow(lambda left:
        _forwardWithin(left, stationary - 1, f))
  else:
    return f(linearObject)

def _backwardWithin(linearObject, stationary, f):
  if stationary > 0:
    return linearObject.backwardOnLeftFollow(lambda left:
        _backwardWithin(left, stationary - 1, f))
  else:
    return f(linearObject)

def _forwardSwap(linearObject):
  return linearObject.forwardAssociateA().forwardFollow(lambda linearObject:
      linearObject.forwardOnRightFollow(lambda linearObject:
        linearObject.forwardCommute()).forwardFollow(lambda linearObject:
          linearObject.forwardAssociateB()))

def _backwardSwap(linearObject):
  return linearObject.backwardAssociateB().backwardFollow(lambda linearObject:
      linearObject.backwardOnRightFollow(lambda linearObject:
        linearObject.backwardCommute()).backwardFollow(lambda linearObject:
          linearObject.backwardAssociateA()))

# This Arrow is used to introduce a new claim
class Begin(LinearLogicUiFunctorialArrow):
  def __init__(self, claim):
    self._claim = claim

  def claim(self):
    return self._claim

  def src(self):
    return true
  def tgt(self):
    return Conj(type = parType, values = [claim.transpose(), claim])

  # FIXME(koreiklein) Something here is broken.  Write tests and fix.
  def translate(self):
    return linear.IntroduceDoubleDual(true).forwardFollow(lambda notNotTrue:
          notNotTrue.forwardOnNotFollow(lambda value:
            value.backwardApply(self.claim().translate()).backwardFollow(lambda x:
              x.backwardCommute().backwardFollow(lambda x:
                x.backwardOnRightFollow(lambda notOneAndClaim:
                  notOneAndClaim.backwardOnNotFollow(lambda oneAndClaim:
                    oneAndClaim.forwardForgetFirst()))).backwardFollow(lambda x:
                x.backwardOnLeftFollow(lambda claim:
                  self.claim().transpose().notToTranspose())))))

# Functorial Arrows

class OnIth(LinearLogicUiFunctorialArrow):
  def __init__(self, conj, index, arrow):
    assert(conj.__class__ == Conj)
    self._src = conj
    self._arrow = arrow
    self._index = index

  def arrow(self):
    return self._arrow
  def index(self):
    return self._index

  def src(self):
    return self._src
  def tgt(self):
    values = list(self.src().values())
    values[self.index()] = self.arrow().tgt()
    return Conj(type = self.src().type(), values = values)

  def translate(self):
    stationary = len(self.src().values()) - (self.index() + 1)
    if self.src().demorganed():
      linearObject = self.src().translate()
      assert(linearObject.__class__ == linear.Not)
      return linearObject.forwardOnNotFollow(lambda claim:
          _backwardWithin(
            claim,
            stationary,
            lambda linearObject: linearObject.backwardOnRightFollow(lambda linearObject:
              linearObject.backwardOnNot(self.arrow().translate()))))
    else:
      return _forwardWithin(self.src().translate(), stationary,
          lambda linearObject: linearObject.forwardOnRight(self.arrow().translate()))

class OnBody(LinearLogicUiFunctorialArrow):
  def __init__(self, type, variables, arrow):
    assert(type in linear.quantifierTypes)
    self._type = type
    self._variables = variables
    self._arrow = arrow

  def type(self):
    return self._type
  def variables(self):
    return self._variables
  def arrow(self):
    return self._arrow

  def src(self):
    return Quantifier(type = self.type(), variables = self.variables(), body = self.arrow().src())
  def tgt(self):
    return Quantifier(type = self.type(), variables = self.variables(), body = self.arrow().tgt())

  def translate(self):
    return _quantifierWithin(self.src().translate(), len(self.variables()), lambda body:
        self.arrow().translate())

# n: an integer >= 0
# linearQuantifier: a linear quantifier.  It must consist of at least n of the same quantifier
#                   type applied in sequence
#         e.g. (n == 3)  forall a. forall b. forall c. forall d. <body>
# f: a function between linear objects
# return: the transition that applies f within the body of the first n quantifiers
#         e.g. (n == 3)  forall a. forall b. forall c. f(forall d. <body>)
def _quantifierWithin(linearQuantifier, n, f):
  if n == 0:
    return f(linearQuantifier)
  else:
    return linearQuantifier.forwardOnBodyFollow(lambda body:
        _quantifierWithin(body, n - 1, f))

# Compose any two arrows between linearui objects.
def compose(left, right):
  values = []
  if left.__class__ == Composite:
    values.extend(left.values())
  else:
    values.append(left)

  if right.__class__ == Composite:
    values.extend(right.values())
  else:
    values.append(right)

  return Composite(values)

class Composite(LinearLogicUiPrimitiveArrow):
  def __init__(self, values):
    assert(len(values) > 0)
    self._values = values

  def values(self):
    return self._values

  def translate(self):
    res = self.values()[0].translate()
    for a in self.values()[1:]:
      res = res.forwardCompose(a.translate())
    return res

  def src(self):
    return self.values()[0].src()
  def tgt(self):
    return self.values()[-1].tgt()

