# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from mark import markable
from calculus import basic
from sets import Set

# This module contains objects and arrows in much the same was as basic.
# This module defines a functor F.
# F assigns to every object in this module, an object in basic.
# F also assigns to every arrow in this module an arrow in basic.
# F satifies all the appropriate properties for a functor
#     (it respects src, tgt, identity, and composition)
# We use x.translate() to implement F.

class Var(markable.Markable):
  def __init__(self, name):
    self._base = basic.Var(name)
    self.initMarkable([])

  def translate(self):
    return self._base

  def name(self):
    return self.translate().name()

  def __repr__(self):
    return self.name()

  def __eq__(self, other):
    return other.__class__ == Var and self._base == other._base
  def __ne__(self, other):
    return not (self == other)

  def __hash__(self):
    return hash(self._base)

#Objects

class Logic(markable.Markable):
  # return F(self)
  def translate(self):
    raise Exception("Abstract Superclass")

  # Note: There is an isomorphism:
  #   basic.Not(self.translate()) <--> self.transpose().translate()
  # notToTranspose implements the forward direction of this isomorphism.
  # transposeToNot implements the reverse direction of this isomorphism.
  def notToTranspose(self):
    raise Exception("Abstract Superclass")
  def transposeToNot(self):
    raise Exception("Abstract Superclass")

  # return an arrow that does no real work but makes the formula a bit "cleaner".
  # subclasses are welcome to override this method in reasonable ways.
  def forwardClean(self):
    return self.identity()

  # return an arrow may aggresively try to make the formula "cleaner".
  # subclasses are welcome to override this method in reasonable ways.
  def forwardHeavyClean(self):
    return self.identity()

  # return a claim dual to self.
  # note: self.transpose().transpose() must be equal to self.
  def transpose(self):
    raise Exception("Abstract Superclass")
  # Return a Logic object like this one, but with the variable b substituted in
  # place of a.
  # a must not be quantified in self.
  def substituteVar(self, a, b):
    raise Exception("Abstract Superclass")

  # return a set of the free variables in self.
  def freeVariables(self):
    raise Exception("Abstract Superclass")

  def backwardRemoveQuantifier(self, quantifierType):
    return RemoveQuantifier(value = self, quantifierType = quantifierType)

  def forwardSingleton(self, conjType):
    return Singleton(self, conjType)
  def backwardUnsingleton(self, conjType):
    return Unsingleton(self, conjType)

  def identity(self):
    return Identity(self)

  def backwardPushPairExport(self):
    def res(claim):
      assert(claim.translate() == self.translate())
      return And([true, self]).forwardForget(0).forwardFollow(lambda x:
        x.forwardUnsingleton())
    return res

forallType = basic.forallType
existsType = basic.existsType

# Possible types of a Conj
andType = 'AND'
orType = 'OR'
withType = 'WITH'
parType = 'PAR'

forallType = basic.forallType
existsType = basic.existsType

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
# return: the type of a basic.Conj that can be used to represent c.
def correspondingConcreteBasicType(type):
  if type == andType:
    return basic.andType
  elif type == orType:
    return basic.orType
  elif type == withType:
    return basic.orType
  else:
    assert(type == parType)
    return basic.andType

# For stylistic reasons, try to use Not sparingly.
# Ideally, self.value() should never be a Conj, Quantifier, Maybe or Always.
class Not(Logic):
  def __init__(self, value):
    self._value = value
    self.initMarkable(['value'])

  def __repr__(self):
    return "~( " + repr(self.value()) + " )"

  def value(self):
    return self._value

  def substituteVar(self, a, b):
    return Not(self.value().substituteVar(a, b))

  def translate(self):
    return basic.Not(self.value().translate())

  def notToTranspose(self):
    return basic.Not(self.translate()).forwardRemoveDoubleDual().forwardCompose(
        self.value().transpose().transposeToNot())
  def transposeToNot(self):
    return self.transpose().translate().forwardOnNot(self.value().notToTranspose())
  def transpose(self):
    assert(False)
    return self.value()

  def freeVariables(self):
    return self.value().freeVariables()

  def forwardOnNot(self, t):
    return OnNot(t)

  def forwardOnNotFollow(self, f):
    return self.forwardOnNot(f(self.value()))

  def backwardOnNot(self, t):
    return OnNot(t)

  def backwardOnNotFollow(self, f):
    return self.backwardOnNot(f(self.value()))

  def backwardPushPairNot(self, f = lambda x: x.identity()):
    def res(claim):
      t = f(And([self.value(), claim]))
      return And([Not(t.tgt()), claim]).forwardOnIthFollow(0, lambda x:
          x.forwardOnNot(t)).forwardApplyPartial(1, 0, 1).forwardFollow(lambda x:
              x.forwardUnsingleton().forwardFollow(lambda x:
                x.forwardOnNotFollow(lambda x:
                  x.backwardSingleton())))
    return res

# This one class will is used to represent
# n-ary AND, OR, WITH and PAR
class Conj(Logic):
  # type in ['AND', 'OR', 'WITH', 'PAR']
  def __init__(self, type, values):
    if type in concreteConjTypes:
      self._demorganed = False
    else:
      # F uses demorgan's laws to translate a demorganed Conj into an object in basic.
      # See Conj.translate()
      assert(type in demorganedConjTypes)
      self._demorganed = True
    self._type = type
    self._values = values
    self.initMarkable(self.generateMethodNamesForList('value', values))

  def __repr__(self):
    return "( %s %s )"%(self.type(), self.values())

  def forwardClean(self):
    t = self.identity()
    def g(x):
      if self.type() == parType:
        if x.__class__ == Conj and x.type() == andType:
          values = x.values()
          n = len(values)
          for j in range(n):
            notClaim = values[j]
            if notClaim.__class__ == Not:
              for i in range(n):
                if i != j:
                  claim = values[i]
                  if claim.translate() == notClaim.value().translate():
                    return x.forwardApply(i, j)
      return x.identity()
    for i in range(len(self.values()))[::-1]:
      t = t.forwardFollow(lambda x:
          x.forwardOnIthFollow(i, lambda x:
            x.forwardClean().forwardFollow(g)).forwardFollow(lambda x:
              _maybeRemoveUnit(x, i)))
    def _tryFalse(x):
      assert(x.__class__ == Conj)
      if x.type() in [andType, withType]:
        for i in range(len(x.values())):
          if isEnrichedFalse(x.values()[i]):
            return x.forwardForgetAllBut(i)
      return x.identity()
    return t.forwardFollow(_tryFalse)

  def forwardHeavyClean(self):
    t = self.identity()
    for i in range(len(self.values()))[::-1]:
      def _maybeAssociateIn(i, x):
        if x.values()[i].__class__ == Conj and x.values()[i].type() == self.type():
          return x.forwardAssociateIn(i)
        else:
          return x.identity()
      t = t.forwardFollow(lambda x:
          x.forwardOnIthFollow(i, lambda x:
            x.forwardHeavyClean())).forwardFollow(lambda x:
                _maybeAssociateIn(i, x))
    def _maybeUnsingleton(x):
      if len(x.values()) == 1:
        return x.forwardUnsingleton()
      else:
        return x.identity()
    return t.forwardFollow(_maybeUnsingleton).forwardFollow(lambda x:
        x.forwardClean())


  def forwardForgetAllBut(self, i):
    assert(isEnrichedFalse(self.values()[i]))
    assert(0 <= i)
    assert(i < len(self.values()))
    t = self.identity()
    for j in range(i + 1, len(self.values())):
      t = t.forwardFollow(lambda x:
          x.forwardForget(j))
    for j in range(0, i):
      t = t.forwardFollow(lambda x:
          x.forwardForget(j))
    return t.forwardFollow(lambda x:
        x.forwardUnsingleton())

  def forwardUnsingleton(self):
    assert(len(self.values()) == 1)
    return Unsingleton(self.values()[0], type = self.type())
  def backwardSingleton(self):
    assert(len(self.values()) == 1)
    return Singleton(self.values()[0], type = self.type())

  def forwardForget(self, index):
    assert(self.type() in [andType, withType])
    return Forget(self, index)
  def backwardForget(self, index, value):
    values = list(self.values())
    values.insert(index, value)
    return Forget(Conj(type = self.type(), values = values), index)

  def forwardRemoveUnit(self, index):
    return RemoveUnit(self, index)

  def forwardApply(self, i, j):
    assert(self.type() == andType)
    return Apply(values = self.values(), i = i, j = j)

  def forwardApplyPartial(self, i, j, k):
    assert(self.type() == andType)
    return ApplyPartial(values = self.values(), i = i, j = j, k = k)

  def forwardImportToContainedConj(self, i, j, k):
    assert(self.type() == andType)
    assert(self.values()[j].__class__ == Conj)
    t = self.values()[j].type()
    if t in [andType, parType]:
      return self.forwardImportToClause(i, j, k)
    else:
      assert(t in [orType, withType])
      return self.forwardDistributeToOne(i, j, k)

  def forwardStartPushingPair(self, i, j, f):
    assert(self.type() == andType)
    if i < j:
      c = 0
    else:
      c = 1
    values = list(self.values())
    values[j] = And([values[j], values[i]])
    values.pop(i)
    return self.forwardShift(i, j - i + c).forwardFollow(lambda x:
        AssociateOut(Conj(type = andType, values = values), j + (c - 1))).forwardFollow(lambda x:
            x.forwardOnIthFollow(j + (c - 1), f))

  def backwardPushPairConj(self, i, f):
    def res(claim):
      t = f(self.values()[i])(claim)
      def g(x):
        values = list(x.values())
        values[i] = x.values()[i].values()[0]
        return And([ Conj(type = x.type(), values = values)
                   , x.values()[i].values()[1] ]).forwardImportToContainedConj(1, 0, i)
      return self.backwardOnIth(i, t).backwardFollow(g)
    return res

  def forwardPushPairQuantifier(self, f = lambda x: x.identity()):
    assert(self.type() == andType)
    assert(len(self.values()) == 2)
    return self.forwardConjQuantifier(0).forwardFollow(lambda x:
        x.forwardOnBodyFollow(f))
  def forwardPushPairConj(self, i, f = lambda x: x.identity()):
    assert(self.type() == andType)
    assert(len(self.values()) == 2)
    return self.forwardImportToContainedConj(1, 0, i).forwardFollow(lambda x:
        x.forwardUnsingleton().forwardFollow(lambda x:
          x.forwardOnIthFollow(i, f)))
  def forwardPushPairNot(self, f):
    assert(self.type() == andType)
    assert(len(self.values()) == 2)
    return self.forwardOnIthFollow(0, lambda x:
        x.forwardOnNotFollow(lambda x:
          f(x)(self.values()[1]))).forwardFollow(lambda x:
              x.forwardApplyPartial(1, 0, 1).forwardFollow(lambda x:
                x.forwardUnsingleton().forwardFollow(lambda x:
                  x.forwardOnNotFollow(lambda x:
                    x.backwardSingleton()))))

  def forwardImportToPath(self, i, j, path):
    return self.forwardImportToPathFollow(i, j, path, lambda x: x.identity())

  # Note: This definition of the behavior of this function is sophisticated.
  # self.type() must be andType
  # i: an index into self.values()
  # path: a path from self to some child.  It must not go through index i.
  # f: a function.
  #
  # forwardImportToPathFollow may be called with a covariant or contravariant path.
  #   It's code is largely the same in both cases, yet the only known way to define its
  #   behavior breaks this situation down into cases:
  #   A) If path is covariant, return a transition that brings clause i to the end of
  #      path, constructing an AND of length 2, and follow by calling f on the result.
  #   B) If path is contravariant, f must produce a transition to self from x when applied
  #      to x where x is the clause at i paired with the end of path.  Return a transition
  #      to self from whatever f produces, but with that residual claim i exported.
  # TODO(koreiklein) The only reason I'm writing this function without any idea how to describe
  #                  it succinctly is because of a HUGE intuitivie sense that I'm right anyway.
  #                  Surely there must be a simpler description of how this function works.
  #                  Figure it out, write it down here, and spare everyone a headache.
  # TODO(koreiklein) Wow! This function seems to work.  Test it more to make sure.
  def forwardImportToPathFollow(self, i, j, path, f):
    assert(self.type() == andType)
    if path.path_singleton():
      if i < j:
        J = j - 1
      else:
        J = j
      def e(x):
        values = list(x.values())
        a = values.pop(J)
        b = values.pop(J)
        values.insert(J, And([a, b]))
        return AssociateOut(And(values), J).forwardFollow(lambda x:
            x.forwardOnIthFollow(J, f))
      return self.forwardShift(i, (J - i) + 1).forwardFollow(e)
    else:
      def g(pair):
        assert(pair.__class__ == Conj)
        assert(pair.type() == andType)
        symbol = path.path_symbol()
        if symbol.__class__ == tuple:
          (name, index) = symbol
          return pair.forwardImportToContainedConj(1, 0, index).forwardFollow(lambda x:
              x.forwardUnsingleton()).forwardFollow(lambda x:
                  x.forwardOnIthFollow(index, f))
        elif symbol == "value":
          assert(pair.values()[0].__class__ == Not)
          t = f(And([pair.values()[0].value(), pair.values()[1]]))
          return pair.forwardOnIthFollow(0, lambda x:
              x.forwardOnNot(t)).forwardFollow(lambda x:
                  x.forwardApplyPartial(1, 0, 1).forwardFollow(lambda x:
                    x.forwardUnsingleton()).forwardFollow(lambda x:
                      x.forwardOnNotFollow(lambda x:
                        x.backwardSingleton())))
        elif symbol == "body":
          assert(pair.values()[0].__class__ == Quantifier)
          return pair.forwardConjQuantifier(0).forwardFollow(lambda x:
              x.forwardOnBodyFollow(f))
        else:
          raise Exception("Unrecognized path symbol %s"%(symbol,))
      return self.forwardImportToPathFollow(i, j, path.path_rest(), g)

  def forwardShift(self, index, amount):
    return Shift(conj = self, index = index, amount = amount)
  def backwardShift(self, index, amount):
    # Clever.
    res = self.forwardShift(index = index, amount = amount).tgt().forwardShift(
        index = index + amount, amount = -amount)
    res.translate()
    return res

  def forwardAssociateOut(self, i, j):
    # e.g. [A, B, C, D], 1, 3 --> [A, [B, C], D]
    assert(i <= j)
    values = list(self.values())
    kidValues = []
    while i < j:
      j -= 1
      kidValues.append(values.pop(i))
    values.insert(i, Conj(type = self.type(), values = kidValues))
    return AssociateOut(Conj(type = self.type(), values = values), i)

  def forwardAssociateIn(self, index):
    # [A, [B, C], D] --> [A, B, C, D]
    return AssociateIn(self, index)

  def forwardOnIthFollow(self, index, f):
    return self.forwardOnIth(index, f(self.values()[index]))

  def forwardOnIth(self, index, t):
    return OnIth(self, index, t)

  def backwardOnIthFollow(self, index, f):
    return self.backwardOnIth(index, f(self.values()[index]))

  def backwardOnIth(self, index, t):
    return OnIth(self, index, t)

  def forwardConjQuantifier(self, index):
    return ConjQuantifier(conj = self, index = index)

  # forwardDistribute* functions should work on ORs within ANDs and on WITHs within ANDs.
  def forwardDistributeToAll(self, i, j):
    assert(self.type() == andType)
    return Distribute(values = self.values(), i = i, j = j)
  def forwardDistributeToOne(self, i, j, k):
    assert(self.type() == andType)
    if i < j:
      J = j - 1
    else:
      J = j
    def f(orClause):
      t = orClause.identity()
      for n in range(len(orClause.values())):
        if n != k:
          t = t.forwardFollow(lambda y:
              y.forwardOnIthFollow(n, lambda twoValueAndClause:
                twoValueAndClause.forwardForget(1).forwardFollow(lambda oneValueAndClause:
                  oneValueAndClause.forwardUnsingleton())))
        else:
          continue
    return Distribute(values = self.values(), i = i, j = j).forwardFollow(lambda x:
        x.forwardOnIthFollow(J, f))

  def forwardImportToClause(self, i, j, k):
    assert(self.type() == andType)
    return ImportToClause(self.values(), i, j, k)

  # Remove a clause from a par by importing a contradicting claim.
  # TODO(koreiklein) This function will become superfluous once the PushPair functions work well.
  #                  Once that happens, remove this function.
  def forwardRemoveFromPar(self, i, j, k):
    assert( Not(self.values()[i]).translate() == self.values()[j].values()[k].translate() )
    if i < j:
      b = j - 1
    else:
      b = j
    return self.forwardImportToClause(i, j, k).forwardFollow(lambda x:
        x.forwardOnIthFollow(b, lambda par:
          par.forwardOnIthFollow(k, lambda x:
            x.forwardApply(1, 0)).forwardFollow(lambda par:
          par.forwardRemoveUnit(k))))

  def substituteVar(self, a, b):
    return Conj(type = self.type(),
        values = [value.substituteVar(a, b) for value in self.values()])

  def notToTranspose(self):
    if not self.demorganed():
      return basic.Not(self.translate()).forwardOnNotFollow(lambda values:
          _valuesToTransposeNot(self.type(), values, self.values()))
    else:
      return basic.Not(self.translate()).forwardRemoveDoubleDual()

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

  def freeVariables(self):
    res = Set()
    for value in self.values():
      res = res.union(value.freeVariables())
    return res

  def translate(self):
    if self.demorganed():
      return self.translateDemorganed()
    else:
      return self.translateUndemorganed()

  def translateDemorganed(self):
    basicType = correspondingConcreteBasicType(self.type())
    res = basic.unit(basicType)
    for value in self.values():
      res = basic.Conj(type = basicType, left = res, right = basic.Not(value.translate()))
    return basic.Not(res)

  def translateUndemorganed(self):
    basicType = correspondingConcreteBasicType(self.type())
    res = basic.unit(basicType)
    for value in self.values():
      res = basic.Conj(type = basicType, left = res, right = value.translate())
    return res

def changePathFirst(path, f):
  if path.path_singleton():
    return f(path.first())
  else:
    (topSymbol, restOfPath, topElement) = path.path_split()
    if topSymbol == 'body':
      assert(topElement.__class__ == Quantifier)
      return Quantifier(variables = topElement.variables(), type = topElement.type(),
          body = changePathFirst(restOfPath, f))
    elif topSymbol == 'value':
      if topElement.__class__ == Always:
        return Always(value = changePathFirst(restOfPath, f))
      elif topElement.__class__== Maybe:
        return Maybe(value = changePathFirst(restOfPath, f))
      else:
        assert(topElement.__class__== Not)
        return Not(value = changePathFirst(restOfPath, f))
    else:
      (topSymbol, index) = topSymbol
      assert(topElement.__class__ == Conj)
      values = list(topElement.values())
      values[index] = changePathFirst(restOfPath, f)
      return Conj(type = topElement.type(), values = values)

# e.g.
# (1 | B.translate()) | C.translate(), [B, C]
#      -->
# (1 | ~B.transpose().translate()) | ~C.transpose().translate()
def _valuesToTransposeNot(type, basicConjOrUnit, basicUiValues):
  if basicConjOrUnit == basic.unit(type):
    assert(len(basicUiValues) == 0)
    return basicConjOrUnit.identity()
  else:
    conj = basicConjOrUnit
    assert(conj.__class__ == basic.Conj)
    assert(conj.type() == type)
    last = basicUiValues[-1]
    return conj.forwardOnRight(last.transpose().transposeToNot()).forwardFollow(lambda conj:
        conj.forwardOnLeftFollow(lambda rest:
          _valuesToTransposeNot(type, rest, basicUiValues[:-1])))
# e.g.
# (1 | B.translate()) | C.translate() <-- (1 | ~B.transpose().translate()) | ~C.transpose().translate()
def _transposeNotToValues(type, basicConjOrUnit, basicUiValues):
  if basicConjOrUnit == basic.unit(type):
    assert(len(basicUiValues) == 0)
    return basicConjOrUnit.identity()
  else:
    conj = basicConjOrUnit
    assert(conj.__class__ == basic.Conj)
    assert(conj.type() == type)
    last = basicUiValues[-1]
    return conj.forwardOnRight(last.transpose().notToTranspose()).forwardFollow(lambda conj:
        conj.forwardOnLeftFollow(lambda rest:
          _transposeNotToValues(type, rest, basicUiValues[:-1])))

true = Conj(type = andType, values = [])
false = Conj(type = orType, values = [])

# return an arrow with src conj which either:
#    removes index i                 if it is a unit of conj
#    leaves everything the same      otherwise
def _maybeRemoveUnit(conj, i):
  value = conj.values()[i]
  if value.__class__ == Conj and len(value.values()) == 0:
    if value.type() == conj.type():
      return conj.forwardAssociateIn(i)
    elif conj.type() == parType and isEnrichedFalse(value):
      return conj.forwardRemoveUnit(i)
  return conj.identity()


class Quantifier(Logic):
  def __init__(self, type, variables, body):
    assert(type in basic.quantifierTypes)
    self._type = type
    self._variables = variables
    self._body = body
    l = self.generateMethodNamesForList('variables', variables)
    l.append('body')
    self.initMarkable(l)

  def forwardClean(self):
    def f(x):
      if isEnrichedFalse(x.body()):
        return x.forwardTotallyUnusedQuantifier()
      else:
        return x.identity()
    return self.forwardOnBodyFollow(lambda x:
        x.forwardClean()).forwardFollow(f)

  def forwardHeavyClean(self):
    t = self.forwardOnBodyFollow(lambda x:
        x.forwardHeavyClean())
    body = t.tgt().body()
    joined = 0
    if body.__class__ == Conj and body.type() == andType:
      for i in range(len(body.values()))[::-1]:
        if body.values()[i].__class__ == Quantifier and body.values()[i].type() == self.type():
          joined += 1
          t = t.forwardFollow(lambda x:
              x.forwardOnBodyFollow(lambda x:
                x.forwardConjQuantifier(i)).forwardFollow(lambda x:
                  x.forwardJoin()))
    def _maybeRemoveQuantifier(x):
      if len(x.variables()) == 0:
        return x.forwardRemoveQuantifier()
      else:
        return x.identity()
    if joined > 0:
      t = t.forwardFollow(lambda x:
          x.forwardOnBodyFollow(lambda x:
            x.forwardHeavyClean()))
    return t.forwardFollow(_maybeRemoveQuantifier)


  def forwardTotallyUnusedQuantifier(self):
    t = self.identity()
    for i in range(len(self.variables())):
      t = t.forwardFollow(lambda x:
          x.forwardUnusedQuantifier(0))
    return t.forwardFollow(lambda x:
        x.forwardRemoveQuantifier())

  def freeVariables(self):
    res = self.body().freeVariables()
    for variable in self.variables():
      res = res.difference(Set([variable]))
    return res

  def notToTranspose(self):
    return _forwardPushNotFollow(len(self.variables()), basic.Not(self.translate()), lambda notBody:
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

  def backwardPushPairQuantifier(self, f):
    return (lambda claim: self.backwardOnBodyFollow(f)(claim).backwardFollow(lambda x:
      x.backwardConjQuantifier(0)))

  def backwardConjQuantifier(self, index):
    values = list(self.body().values())
    values[index] = Quantifier(type = self.type(), variables = self.variables(),
        body = values[index])
    return ConjQuantifier(conj = Conj(type = self.body().type(), values = values), index = index)

  def forwardUnusedQuantifier(self, index):
    return UnusedQuantifier(self, index)

  def forwardJoin(self):
    return QuantifierJoin(self)

  def forwardRemoveQuantifier(self):
    assert(len(self.variables()) == 0)
    return RemoveQuantifier(value = self.body(), quantifierType = self.type())

  def forwardEliminate(self, index, replacementVar):
    assert(self.type() == forallType)
    return Eliminate(quantifier = self, index = index, replacementVar = replacementVar)

  def forwardEliminateMultiple(self, replacementVars):
    assert(self.type() == forallType)
    res = self.identity()
    for replacementVar in replacementVars:
      res = res.forwardFollow(lambda x:
          Eliminate(quantifier = x, index = 0, replacementVar = replacementVar))
    return res

  def forwardEliminateAll(self, replacementVars):
    return self.forwardEliminateMultiple(replacementVars).forwardFollow(lambda x:
        x.forwardRemoveQuantifier())

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

  def backwardOnBodyFollow(self, f):
    return self.backwardOnBody(f(self.body()))

  def backwardOnBody(self, t):
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
    for variable in self.variables()[::-1]:
      res = basic.Quantifier(type = self.type(), var = variable.translate(), body = res)
    return res

# e.g.
# | q(t, a, q(t, b, x))  -->  q(~t, a, q(~t, b, f(~x).tgt()))
# *--------------------
def _forwardPushNotFollow(n, basicObject, f):
  if n == 0:
    return f(basicObject)
  else:
    assert(n > 0)
    assert(basicObject.__class__ == basic.Not)
    return basicObject.forwardNotQuant().forwardFollow(lambda quant:
        quant.onBody(_forwardPushNotFollow(n - 1, quant.body(), f)))

# e.g.
# | q(t, a, q(t, b, x))  <--  q(~t, a, q(~t, b, f(x).src()))
# *--------------------
def _backwardPullNotFollow(n, basicObject, f):
  if n == 0:
    res = f(basicObject)
    assert(res.tgt().__class__ == basic.Not)
    return res
  else:
    assert(basicObject.__class__ == basic.Not)
    return basicObject.backwardNotQuant().backwardFollow(lambda quant:
      _backwardPullNotFollow(n - 1, quant, f))

class Always(Logic):
  def __init__(self, value):
    self._value = value
    self.initMarkable(['value'])

  def freeVariables(self):
    return self.value().freeVariables()

  def notToTranspose(self):
    return basic.Not(self.translate()).forwardOnNotFollow(lambda alwaysValue:
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
    return basic.Always(self.value().translate())

class Maybe(Logic):
  def __init__(self, value):
    self._value = value
    self.initMarkable(['value'])

  def freeVariables(self):
    return self.value().freeVariables()

  def notToTranspose(self):
    return basic.Not(self.translate()).forwardRemoveDoubleDual().forwardFollow(lambda alwaysNotValue:
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
    return basic.Not(basic.Always(basic.Not(self.value().translate())))

# Utilities for contstructing enriched objects.
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
  else:
    values = [predicate.transpose()]
  values.append(consequent)
  return Par(values)

# Arrows

# Abstract superclass of all nonfunctorial arrows between enriched objects.
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

class FunctorialArrow(PrimitiveArrow):
  pass

class Identity(PrimitiveArrow):
  def __init__(self, value):
    self._value = value

  def src(self):
    return self._value
  def tgt(self):
    return self._value
  def translate(self):
    return self._value.translate().identity()

  def forwardFollow(self, f):
    return f(self.src())
  def backwardFollow(self, f):
    return f(self.tgt())

class Distribute(PrimitiveArrow):
  # Import claim i of the list into each clause of the OR at spot j.
  # If the disjunction is par, values[i] must be exponential.
  # e.g.  [A, B, C, D0 - D1 - D2, E], 1, 3
  #   [A | B | C | D0 - D1 - D2 | E] ---> [A | C | ((D0 | B) - (D1 | B) - (D2 | B)) | E]
  def __init__(self, values, i, j):
    assert(i != j)
    assert(values[j].__class__ == Conj)
    assert(values[j].type() in [orType, withType])
    assert(0 <= i and i < len(values))
    assert(0 <= j and j < len(values))
    self._values = values
    self._i = i
    self._j = j

  def demorganed(self):
    return self._values[j].type() == withType

  def src(self):
    return Conj(type = andType, values = self._values)
  def tgt(self):
    values = list(self._values)
    values[j] = Conj(type = self._values[j].type(),
        values = [ And([v, values[i]]) for v in values[j].values() ])
    values.pop(i)
    return Conj(type = andType, values = values)

  def translate(self):
    if self._i < self._j:
      J = self._j - 1
    else:
      J = self._j
    if not self.demorganed():
      return _onJandI(self.src(), self._j, self._i, lambda jAndi:
          jAndi.forwardOnLeftFollow(lambda x:
            _forwardOnAll(x, lambda x:
              x.forwardIntroduceTrue().forwardFollow(lambda x:
                x.forwardCommute()))).forwardFollow(lambda x:
          _distribute(x))).forwardCompose(
              self.tgt().backwardShift(index = J, amount = -J).translate())
    else:
      return _onJandI(self.src(), self._j, self._i, lambda jAndi:
          jAndi.forwardOnLeftFollow(lambda x:
            x.forwardOnNotFollow(lambda x:
              _backwardOnAll(x, lambda x:
                x.backwardOnNotFollow(lambda x:
                  x.forwardIntroduceTrue().forwardFollow(lambda x:
                    x.forwardCommute())).backwardFollow(lambda x:
                x.backwardApply(self._values[self._i].translate())))).backwardCompose(
                  _distribute(basic.And(self.tgt().values()[J].translate().value(),
                    jAndi.right())))).forwardFollow(lambda x: x.forwardApply()))

# basicObject: a basic object of the form ((unit % A) % B) % C for % in {|,-}
# f: a function basic objects -> transitions leaving said objects
# return: a basic transition to ((unit % f(A)) % f(B)) % f(C)
def _forwardOnAll(basicObject, f):
  if basicObject.__class__ == basic.Conj:
    return basicObject.forwardOnLeftFollow(lambda x:
        _forwardOnAll(x, f)).forwardFollow(lambda y:
            y.forwardOnRightFollow(lambda z:
              f(z)))
  else:
    return basicObject.identity()

# basicObject: a basic object of the form ((unit % A) % B) % C for % in {|,-}
# f: a function basic objects -> transitions to said objects
# return: a basic transition from ((unit % f(A)) % f(B)) % f(C)
def _backwardOnAll(basicObject, f):
  if basicObject.__class__ == basic.Conj:
    return basicObject.backwardOnLeftFollow(lambda x:
        _backwardOnAll(x, f)).backwardFollow(lambda y:
            y.backwardOnRightFollow(lambda z:
              f(z)))
  else:
    return basicObject.identity()

# conj is a basic conjunctive list and a claim of the form e.g. (((1 | a) | b) | c) | claim
# stationary: an integer index less than the length of the list e.g. 1
# return: ((1 | a) | (b | claim)) | c
def _toAnd(conj, k):
  if k == 0:
    return conj.forwardAssociateA()
  else:
    return conj.forwardCommute().forwardFollow(lambda x:
        x.forwardAssociateB().forwardFollow(lambda x:
          x.forwardOnLeftFollow(lambda x:
            x.forwardCommute().forwardFollow(lambda x:
              _toAnd(x, k - 1)))))

# conj is a basic disjunctive list and a claim of the form (((- - a) - b) - c) | claim
# return a basic arrow: (((- - a) - b) - c) | claim --> (((- - (a|claim)) - (b|claim)) - (c|claim))
def _distribute(conj):
  assert(conj.__class__ == basic.Conj)
  assert(conj.type() == basic.andType)
  if conj.left() == basic.false:
    return conj.forwardForget()
  else:
    assert(conj.left().__class__ == basic.Conj)
    assert(conj.left().type() == basic.orType)
    return conj.forwardDistribute().forwardFollow(lambda x:
          x.onLeft(_distribute(x.left())))

class ImportToClause(PrimitiveArrow):
  # Import claim i of the list into the kth clause of the PAR or AND at spot j.
  # e.g.  [A, B, C, D0 - D1 - D2, E], 1, 3, 0
  #   [A | B | C | D0 - D1 - D2 | E] ---> [A | C | ((D0 | B) - D1 - D2) | E]
  def __init__(self, values, i, j, k):
    assert(values[j].__class__ == Conj)
    assert(values[j].type() in [andType, parType])
    assert(i != j)
    assert(0 <= i and i < len(values))
    assert(0 <= j and j < len(values))
    assert(0 <= k and k < len(values[j].values()))
    self._values = values
    self._i = i
    self._j = j
    self._k = k

  def demorganed(self):
    return self._values[self._j].type() == parType

  def src(self):
    return And(self._values)
  def tgt(self):
    kidValues = list(self._values[self._j].values())
    kidValues[self._k] = And([kidValues[self._k], self._values[self._i]])
    values = list(self._values)
    values[self._j] = Conj(type = self._values[self._j].type(), values = kidValues)
    values.pop(self._i)
    return And(values)

  def translate(self):
    if self._i < self._j:
      J = self._j - 1
    else:
      J = self._j

    if not self.demorganed():
      return _onJandI(self.src(), self._j, self._i, lambda jAndi:
          jAndi.forwardOnLeftFollow(lambda x:
            _forwardWithin(x, len(self._values[self._j].values()) - (self._k + 1), lambda x:
              x.forwardOnRightFollow(lambda x:
                x.forwardIntroduceTrue().forwardFollow(lambda x:
                  x.forwardCommute())))).forwardFollow(lambda x:
          _toAnd(x, len(self._values[self._j].values()) - (self._k + 1)))).forwardCompose(
              self.tgt().backwardShift(index = J, amount = -J).translate())
    else:
      return _onJandI(self.src(), self._j, self._i, lambda jAndi:
        jAndi.forwardOnLeftFollow(lambda x:
          x.forwardOnNotFollow(lambda x:
            _backwardWithin(x, len(self._values[self._j].values()) - (self._k + 1), lambda x:
              x.backwardOnRightFollow(lambda x:
                x.backwardOnNotFollow(lambda x:
                  x.forwardIntroduceTrue().forwardFollow(lambda x:
                    x.forwardCommute())).backwardFollow(lambda x:
                x.backwardApply(jAndi.right())))).backwardCompose(
                  _toAnd(basic.And(self.tgt().values()[J].translate().value(), jAndi.right()),
                    len(self.tgt().values()[J].values()) - (self._k + 1))))).forwardFollow(lambda x:
                      x.forwardApply())).forwardCompose(
                          self.tgt().backwardShift(index = J, amount = -J).translate())

# conjOrUnit: a basic conj of the form (((1 | A) | B) | C) | D
# outer: an integer
# f: a function from a basic conj to a basic conj
# return: a basic transition from a  conj like conjOrUnit,
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

# conj: an enriched.Conj
# i, j: i != j, are indices into the values of conj
# basicTransitionF: a function generating a basic transition from:
#     (conj.values()[j].translate() | conj.values()[i].translate())
#   to any basic object L.
# return: a transition with src conj.translate() which removes the ith and jth elements and leaves
#         L at the front.
def _onJandI(conj, j, i, basicTransitionF):
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
        x.forwardOnRightFollow(basicTransitionF))))

class RemoveQuantifier(PrimitiveArrow):
  def __init__(self, value, quantifierType):
    self._value = value
    self._quantifierType = quantifierType

  def src(self):
    return Quantifier(type = self._quantifierType, variables = [], body = self._value)
  def tgt(self):
    return self._value

  def translate(self):
    return self.src().translate().identity()

class ConjQuantifier(PrimitiveArrow):
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

  # Note: Though this method generates a basic transition of quadratic size,
  #       extraction can safely convert the entire basic transition into the identity
  #       program transformation.  Therefore, there is no performance penalty.
  def translate(self):
    return _conjQuantifierWithin(basicConj = self.src().translate(),
        m = len(self.quantifier().variables()),
        n = len(self.conj().values()) - (self.index() + 1))

# basicConj: a basic Conj object containing a basic quantifier object
# m: an integer, the number of nested quantifiers.
# n: an integer, the number of nested conjs.
#   e.g. m = 2, n = 2, basicConj = ((((1|a)|b) | (exists x. exists y. c)) | d) | e
# return: a basicConj where the quantifiers have been moved to the outside
#   e.g. exists x. exists y.  ((((1|a)|b)|c)|d)|e
def _conjQuantifierWithin(basicConj, m, n):
  if n == 0:
    return basicConj.forwardCommute().forwardFollow(lambda claim:
        _conjQuantifier(claim, m)).forwardFollow(lambda claim:
            _quantifierWithin(claim, m, lambda claim:
              claim.forwardCommute()))
  else:
    return basicConj.forwardOnLeftFollow(lambda left:
        _conjQuantifierWithin(left, m, n - 1)).forwardFollow(lambda claim:
            _conjQuantifier(claim, m))

# m: an integer
# basicConj: a basic conj with m nested quantifiers as its left argument.
#  e.g. m = 2, basicConj = (  exists x. exists y. a )  | b
def _conjQuantifier(basicConj, m):
  if m == 0:
    return basicConj.identity()
  else:
    return basicConj.forwardConjQuantifier().forwardFollow(lambda claim:
        claim.forwardOnBodyFollow(lambda claim:
          _conjQuantifier(claim, m - 1)))

class Eliminate(PrimitiveArrow):
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
    return _quantifierWithin(self.src().translate(), self.index(), lambda basicBody:
        basicBody.forwardEliminateVar(replacementVar = self.replacementVar().translate()))

class Unsingleton(PrimitiveArrow):
  # clever: we cheat by reversing the translated Singleton transition.
  def __init__(self, a, type):
    self._singleton = Singleton(a, type)

  def src(self):
    return self._singleton.tgt()
  def tgt(self):
    return self._singleton.src()
  def translate(self):
    res = basic.reverse(self._singleton.translate())
    assert(res is not None)
    return res

class Singleton(PrimitiveArrow):
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
      return self.src().translate().forwardIntroduceDoubleDual().forwardFollow(lambda claim:
          claim.forwardOnNotFollow(lambda claim:
            claim.backwardForgetFirst(basic.false)))
    elif self.type() == parType:
      return self.src().translate().forwardIntroduceDoubleDual().forwardFollow(lambda claim:
          claim.forwardOnNotFollow(lambda claim:
            claim.backwardForgetFirst(basic.true)))
    else:
      raise Exception("Unrecognized self.type()")

class UnusedQuantifier(PrimitiveArrow):
  def __init__(self, quantifier, index):
    assert(quantifier.__class__ == Quantifier)
    assert(quantifier.type() == existsType)
    assert(quantifier.variables()[index] not in quantifier.body().freeVariables())
    self._quantifier = quantifier
    self._index = index

  def quantifier(self):
    return self._quantifier
  def index(self):
    return self._index

  def src(self):
    return self.quantifier()
  def tgt(self):
    variables = list(self.quantifier().variables())
    variables.pop(self.index())
    return Quantifier(type = existsType, variables = variables, body = self.quantifier().body())

  def translate(self):
    return _quantifierWithin(self.src().translate(), self.index(), lambda x:
        x.forwardUnusedQuantifier())

class QuantifierJoin(PrimitiveArrow):
  def __init__(self, quantifier):
    assert(quantifier.__class__ == Quantifier)
    assert(quantifier.body().__class__ == Quantifier)
    assert(quantifier.type() == quantifier.body().type())
    self._quantifier = quantifier

  def quantifier(self):
    return self._quantifier

  def src(self):
    return self.quantifier()
  def tgt(self):
    variables = list(self.quantifier().variables())
    variables.extend(self.quantifier().body().variables())
    return Quantifier(type = self.quantifier().type(), variables = variables,
        body = self.quantifier().body().body())

  def translate(self):
    return self.src().translate().identity()

class AssociateOut(PrimitiveArrow):
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
    res = basic.reverse(self._associateIn.translate())
    assert(res is not None)
    return res

class AssociateIn(PrimitiveArrow):
  # e.g. index = 1
  # [A, [B, C], D] --> [A, B, C, D]
  def __init__(self, conj, index):
    assert(conj.__class__ == Conj)
    assert(0 <= index and index < len(conj.values()))
    assert(conj.values()[index].__class__ == Conj)
    assert(conj.values()[index].type() == conj.type())
    self._src = conj
    self._index = index
    assert(self.src().translate() == self.translate().src())
    assert(self.tgt().translate() == self.translate().tgt())

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
      basicObject = self.src().translate()
      assert(basicObject.__class__ == basic.Not)
      return basicObject.forwardOnNot(
          _backwardWithin(basicObject.value(), stationary, lambda x:
            x.backwardOnRightFollow(lambda x:
              x.backwardIntroduceDoubleDual()).backwardFollow(lambda x:
            _backwardAssociate(x))))
    else:
      return _forwardWithin(self.src().translate(), stationary, _forwardAssociate)

def _forwardAssociate(basicObject):
  if basicObject.right().__class__ != basic.Conj:
    if basicObject.right() == basic.true:
      assert(basicObject.type() == basic.andType)
      return basicObject.forwardForget()
    else:
      assert(basicObject.right() == basic.false)
      assert(basicObject.type() == basic.orType)
      return basicObject.forwardRemoveFalse()
  else:
    return basicObject.forwardAssociateB().forwardFollow(lambda basicObject:
        basicObject.forwardOnLeft(_forwardAssociate(basicObject.left())))

def _backwardAssociate(basicObject):
  if basicObject.right().__class__ != basic.Conj:
    if basicObject.right() == basic.true:
      assert(basicObject.type() == basic.andType)
      return basicObject.backwardIntroduceTrue()
    else:
      assert(basicObject.right() == basic.false)
      assert(basicObject.type() == basic.orType)
      return basicObject.backwardAdmit()
  else:
    return basicObject.backwardAssociateA().backwardFollow(lambda basicObject:
        basicObject.backwardOnLeft(_backwardAssociate(basicObject.left())))

def isEnrichedTrue(x):
  return (x.__class__ == Conj and len(x.values()) == 0 and x.type() == andType
      or x.__class__ == Not and isEnrichedTrue(x.value()))
def isEnrichedFalse(x):
  return (x.__class__ == Conj and len(x.values()) == 0 and x.type() in [orType, parType]
      or x.__class__ == Not and isEnrichedTrue(x.value()))

# Use this class only for conj with type in [orType, parType]
#   the andType and withType units should be removed using forget.
class RemoveUnit(PrimitiveArrow):
  def __init__(self, conj, index):
    assert(conj.__class__ == Conj)
    assert(conj.type() in [orType, parType])
    assert(isEnrichedFalse(conj.values()[index]))
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
    removed = values.pop(self.index())
    return Conj(type = self.conj().type(), values = values)

  def translate(self):
    if self.conj().type() == orType:
      return _forwardWithin(self.src().translate(),
          len(self.conj().values()) - (self.index() + 1), lambda claim:
            claim.forwardRemoveFalse())
    else:
      assert(self.conj().type() == parType)
      return self.src().translate().forwardOnNotFollow(lambda claim:
          _backwardWithin(claim, len(self.conj().values()) - (self.index() + 1), lambda claim:
            claim.backwardOnRightFollow(lambda claim:
              claim.backwardIntroduceDoubleDual()).backwardFollow(lambda claim:
            claim.backwardIntroduceTrue())))

class ApplyPartial(PrimitiveArrow):
  # Apply claim at spot i to the kth claim within the Not at spot j to remove it.
  def __init__(self, values, i, j, k):
    assert(i != j)
    assert(values[j].__class__ == Not)
    assert(values[j].value().__class__ == Conj)
    assert(values[j].value().type() == andType)
    assert(values[j].value().values()[k] == values[i])
    assert(values[j].value().values()[k].translate() == values[i].translate())
    self._values = values
    self._i = i
    self._j = j
    self._k = k

  def values(self):
    return self._values
  def i(self):
    return self._i
  def j(self):
    return self._j
  def k(self):
    return self._k

  def src(self):
    return Conj(type = andType, values = self.values())
  def tgt(self):
    newValues = list(self.values())
    jValues = list(self.values()[self.j()].value().values())
    jValues.pop(self.k())
    newValues[self.j()] = Not(Conj(type = andType, values = jValues))
    newValues.pop(self.i())
    return Conj(type = andType, values = newValues)

  def translate(self):
    bodyOfNot = self.values()[self.j()].value()
    if self.i() < self.j():
      J = self.j() - 1
    else:
      J = self.j()
    return _onJandI(self.src(), self.j(), self.i(), lambda basicJandI:
        basicJandI.forwardOnLeftFollow(lambda notClaim:
          notClaim.forwardOnNot(
            bodyOfNot.backwardShift(self.k(),
              len(bodyOfNot.values()) - (self.k() + 1)).translate())).forwardFollow(lambda x:
        x.forwardApply())).forwardCompose(self.tgt().backwardShift(J, J).translate())

class Apply(PrimitiveArrow):
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
              claim.backwardForgetFirst(basic.true))))).forwardFollow(lambda claim:
        claim.forwardApply())

class Forget(PrimitiveArrow):
  def __init__(self, conj, index):
    assert(conj.type() in [andType, withType])
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
class Shift(PrimitiveArrow):
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
      basicObject = self.src().translate()
      assert(basicObject.__class__ == basic.Not)
      return basicObject.forwardOnNot(
          _backwardWithin(basicObject.value(), stationary, _backwardSwap))
    else:
      return _forwardWithin(self.src().translate(), stationary, _forwardSwap)

def _forwardWithin(basicObject, stationary, f):
  if stationary > 0:
    return basicObject.forwardOnLeftFollow(lambda left:
        _forwardWithin(left, stationary - 1, f))
  else:
    return f(basicObject)

def _backwardWithin(basicObject, stationary, f):
  if stationary > 0:
    return basicObject.backwardOnLeftFollow(lambda left:
        _backwardWithin(left, stationary - 1, f))
  else:
    return f(basicObject)

def _forwardSwap(basicObject):
  return basicObject.forwardAssociateA().forwardFollow(lambda basicObject:
      basicObject.forwardOnRightFollow(lambda basicObject:
        basicObject.forwardCommute()).forwardFollow(lambda basicObject:
          basicObject.forwardAssociateB()))

def _backwardSwap(basicObject):
  return basicObject.backwardAssociateB().backwardFollow(lambda basicObject:
      basicObject.backwardOnRightFollow(lambda basicObject:
        basicObject.backwardCommute()).backwardFollow(lambda basicObject:
          basicObject.backwardAssociateA()))

# This Arrow is used to introduce a new claim
class Begin(FunctorialArrow):
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
    return basic.IntroduceDoubleDual(true).forwardFollow(lambda notNotTrue:
          notNotTrue.forwardOnNotFollow(lambda value:
            value.backwardApply(self.claim().translate()).backwardFollow(lambda x:
              x.backwardCommute().backwardFollow(lambda x:
                x.backwardOnRightFollow(lambda notOneAndClaim:
                  notOneAndClaim.backwardOnNotFollow(lambda oneAndClaim:
                    oneAndClaim.forwardForgetFirst()))).backwardFollow(lambda x:
                x.backwardOnLeftFollow(lambda claim:
                  self.claim().transpose().notToTranspose())))))

# Functorial Arrows

class OnNot(FunctorialArrow):
  def __init__(self, arrow, compressed):
    self._arrow = arrow
    self._compressed = compressed

  def src(self):
    return Not(self._arrow.tgt())
  def tgt(self):
    return Not(self._arrow.src())

  def translate(self):
    return self.src().translate().forwardOnNot(self._arrow.translate())

  def compress(self):
    if self._compressed:
      return self
    kid = self._arrow.compress()
    if kid.__class__ == identity:
      return self.src().identity()
    else:
      return OnNot(kid, compressed = True)

class OnIth(FunctorialArrow):
  def __init__(self, conj, index, arrow, compressed = False):
    assert(conj.__class__ == Conj)
    self._src = conj
    self._arrow = arrow
    self._index = index
    self._compressed = compressed

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

  def compress(self):
    if self._compressed:
      return self
    kid = self.arrow().compress()
    if kid.__class__ == Identity:
      return self.src().identity()
    return OnIth(self._src, self.index(), kid, compressed = True)

  def translate(self):
    stationary = len(self.src().values()) - (self.index() + 1)
    if self.src().demorganed():
      basicObject = self.src().translate()
      assert(basicObject.__class__ == basic.Not)
      return basicObject.forwardOnNotFollow(lambda claim:
          _backwardWithin(
            claim,
            stationary,
            lambda basicObject: basicObject.backwardOnRightFollow(lambda basicObject:
              basicObject.backwardOnNot(self.arrow().translate()))))
    else:
      return _forwardWithin(self.src().translate(), stationary,
          lambda basicObject: basicObject.forwardOnRight(self.arrow().translate()))

class OnBody(FunctorialArrow):
  def __init__(self, type, variables, arrow, compressed = False):
    assert(type in basic.quantifierTypes)
    self._type = type
    self._variables = variables
    self._arrow = arrow
    self._compressed = compressed

  def type(self):
    return self._type
  def variables(self):
    return self._variables
  def arrow(self):
    return self._arrow

  def compress(self):
    if self._compressed:
      return self
    kid = self.arrow().compress()
    if kid.__class__ == Identity:
      return self.src().identity()
    return OnBody(self.type(), self.variables(), kid, compressed = True)

  def src(self):
    return Quantifier(type = self.type(), variables = self.variables(), body = self.arrow().src())
  def tgt(self):
    return Quantifier(type = self.type(), variables = self.variables(), body = self.arrow().tgt())

  def translate(self):
    return _quantifierWithin(self.src().translate(), len(self.variables()), lambda body:
        self.arrow().translate())

# n: an integer >= 0
# basicQuantifier: a basic quantifier.  It must consist of at least n of the same quantifier
#                   type applied in sequence
#         e.g. (n == 3)  forall a. forall b. forall c. forall d. <body>
# f: a function between basic objects
# return: the transition that applies f within the body of the first n quantifiers
#         e.g. (n == 3)  forall a. forall b. forall c. f(forall d. <body>)
def _quantifierWithin(basicQuantifier, n, f):
  if n == 0:
    return f(basicQuantifier)
  else:
    return basicQuantifier.forwardOnBodyFollow(lambda body:
        _quantifierWithin(body, n - 1, f))

# Compose any two arrows between enriched objects.
def compose(left, right):
  if left.__class__ == Identity:
    return right
  elif right.__class__ == Identity:
    return left

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

class Composite(PrimitiveArrow):
  def __init__(self, values, compressed = False):
    assert(len(values) > 0)
    self._values = values
    self._compressed = compressed

  def values(self):
    return self._values

  def compress(self):
    if self._compressed:
      return self
    compressedValues = [ value.compress() for value in self.values() ]
    nonIdentityValues = [ value for value in compressedValues if value.__class__ != Identity ]
    if len(nonIdentityValues) == 0:
      return Identity(self.values()[0].src())
    elif len(nonIdentityValues) == 1:
      return nonIdentityValues[0]
    else:
      assert(len(nonIdentityValues) >= 2)
      firstValue = nonIdentityValues[0]
      T = firstValue.forwardCompose(Composite(nonIdentityValues[1:]).compress())
      assert(T.__class__ == Composite)
      values = T.values()
      if len(values) == 1:
        return values[0]
      else:
        x = _compressTwo(values[0], values[1])
        if x is None:
          return T
        else:
          if len(values) == 2:
            return x
          else:
            xs = [x]
            xs.extend(values[2:])
            return Composite(xs, compressed = True)

  def translate(self):
    res = self.values()[0].translate()
    for a in self.values()[1:]:
      res = res.forwardCompose(a.translate())
    return res

  def src(self):
    return self.values()[0].src()
  def tgt(self):
    return self.values()[-1].tgt()

class OnValues:
  # conj: a Conj
  # arrows: a list of (index, arrow) pairs where arrow can be applied to conj.values()[index]
  def __init__(self, conj, arrows, compressed = False):
    self._conj = conj
    self._arrows = arrows
    self._compressed = compressed

  def arrows(self):
    return self._arrows

  def compress(self):
    if self._compressed:
      return self
    return OnValues(self._conj,
        [ (index, arrow.compress()) for (index, arrow) in self.arrows() ],
        compressed = True)

  def type(self):
    return self._conj.type()
  def src(self):
    return self._conj
  def tgt(self):
    values = list(self._conj.values())
    for (i, arrow) in self._arrows:
      values[i] = arrow.tgt()
    return Conj(type = self.type(), values = values)

  def translate(self):
    # TODO: Define a translation that returns a more "compressed" basic arrow.
    # Note: even with below implementation, this class is still useful for compression because
    #       it allows for compressing arrows on the same index that are separated
    #       e.g. Composite([OnIth(index = i, ...),  OnIth(index = j, ...), OnIth(i, ...)])
    t = self.src().identity()
    for (index, arrow) in self._arrows:
      t = t.forwardFollow(lambda x:
          x.forwardOnIth(index, arrow))
    return t.translate()

# a, b: Enriched Arrows, they must be composable.
# return: a single compressed arrow, not a Composite, which is equivalent to Composite([a, b])
#         or None if no such suitable arrow exists.
def _compressTwo(a, b):
  if a.__class__ == OnValues and b.__class__ == OnValues:
    arrows = dict(a.arrows())
    for (index, arrow) in b.arrows():
      if arrows.has_key(index):
        arrows[index] = arrows[index].forwardCompose(arrow).compress()
      else:
        arrows[index] = arrow
    return OnValues(a.src(), arrows.items())
  elif a.__class__ == OnValues and b.__class__ == OnIth:
    arrows = dict(a.arrows())
    if arrows.has_key(b.index()):
      arrows[b.index()] = arrows[b.index()].forwardCompose(b.arrow()).compress()
    else:
      arrows[b.index()] = b.arrow()
    return OnValues(a.src(), arrows.items())
  elif a.__class__ == OnIth and b.__class__ == OnValues:
    arrows = dict(b.arrows())
    if arrows.has_key(a.index()):
      arrows[a.index()] = arrows[a.index()].backwardCompose(a.arrow()).compress()
    else:
      arrows[a.index()] = a.arrow()
    return OnValues(a.src(), arrows.items())
  elif a.__class__ == OnIth and b.__class__ == OnValues:
    if a.index() == b.index():
      return OnIth(a.src(), a.index(), a.arrow().forwardCompose(b.arrow()).compress())
    else:
      return OnValues(a.src(), [ (a.index(), a.arrow()), (b.index(), b.arrow()) ])
  elif a.__class__ != b.__class__:
    return None
  else:
    c = a.__class__
    if c == OnBody:
      # This assert should succeed because a and b are composable.
      assert(a.type() == b.type() and a.variables() == b.variables())
      return OnBody(type = a.type(), variables = a.variables(),
          arrow = a.arrow().forwardCompose(b.arrow()).compress())
    elif c == OnNot:
      return OnNot(a.arrow().backwardCompose(b.arrow()).compress())
    else:
      return None


