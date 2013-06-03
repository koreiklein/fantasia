# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic, enriched
from lib import common_vars

class Endofunctor:
  # Return a basic endofunctor
  def translate(self):
    return self
  def variables(self):
    raise Exception("Abstract superclass.")
  # self must be covariant()
  # return a list of (B, a function representing some natural transform: F --> (B|.) o F)
  # such that f(B) == True.
  def importFiltered(self, f):
    return []
  # self must not be covariant()
  # return a list of (B, a function representing some natural transform: (B|.) o F --> F)
  # such that f(B) == True.
  def exportFiltered(self, f):
    return []
  # self must be covariant()
  # return a function representing a natural transform: F o (B|.) --> (B|.) o F
  def _import(self, B):
    raise Exception("Abstract superclass.")
  # self must not be covariant()
  # return a function representing some natural transform: (B|.) o F o (B|.) --> F
  def _export(self, B):
    raise Exception("Abstract superclass.")

  def onObject(self, object):
    raise Exception("Abstract superclass.")
  def onArrow(self, arrow):
    raise Exception("Abstract superclass.")
  def negations(self):
    raise Exception("Abstract superclass.")
  def covariant(self):
    return 0 == (self.negations() % 2)
  # Return a pair of functors (F, G) such that self == F.compose(G), F is non-trivial,
  # and F is "as simple as possible".
  def pop(self):
    return (self, identity_functor)
  def compose(self, other):
    if self.__class__ == Id:
      return other
    elif other.__class__ == Id:
      return self
    else:
      return Composite(left = self, right = other)

def new_path(object):
  return Path(identity_functor, object)

class Path:
  def __init__(self, functor, object):
    self.functor = functor
    self.object = object

  def __repr__(self):
    return "PATH:\nBEGIN_WITH: %s\nAPPLY_FUNCTOR:\n%s"%(self.object, self.functor)

  def variables(self):
    return self.functor.variables()
  def top(self):
    return self.functor.onObject(self.object)
  def bottom(self):
    return self.object

  def covariant(self):
    return self.functor.covariant()

  def translate(self):
    return Path(functor = self.functor.translate(), object = self.object.translate())

  # return a path arrow that uses the indexth import available from self.importFiltered(f)
  def doImportFiltered(self, f, index):
    l = self.importFiltered(f)
    if index < len(l):
      (B, nt) = l[index]
      bAnd = And(side = right, other = B)
      a = nt(self.object)
      return Arrow(src = self,
          tgt = Path(functor = self.functor, object = basic.And(B, self.object)),
          arrow = a)
    else:
      raise Exception("Failed to import because the index %s does not exist in %s"%(index, l))

  # self must be covariant
  # return a list of (B, a function representing some natural transform: F --> (B|.) o F)
  # such that f(B) == True.
  def importFiltered(self, f):
    return self.functor.importFiltered(f)

  # self must be covariant
  # return a list of (B, a path arrow to self.onObject((B|self.object)))
  # such that f(B) == True
  def importFilteredArrow(self, f):
    return [(B, Arrow(src = self,
      tgt = Path(functor = self.functor, object = basic.And(B, self.object)),
      arrow = nt(self.object)))
      for (B, nt) in self.importFiltered(f)]

  # self must be contravariant
  # return: a list of path arrows : self --> self.functor.onObject(basic.true)
  def exportBottom(self):
    assert(not self.functor.covariant())
    # x F --> (x|1) F = 1 ((x|.) o F) --> 1F
    return [Arrow(src = self, tgt = Path(functor = self.functor, object = basic.true),
                  arrow = self.functor.onArrow(
                    self.object.backwardForgetRight(basic.true)).forwardCompose(nt(basic.true)))
            for (B, nt) in self.functor.exportFiltered(lambda x: self.object == x)]
    #exports = self.functor.exportFiltered(lambda x: self.object == x)
    #if len(exports) == 0:
    #  return None
    #else:
    #  (B, nt) = exports[0]
    #  assert(self.object == B)
    #  return Arrow(
    #      src = self,
    #      tgt = Path(functor = self.functor, object = basic.true),
    #      arrow = self.functor.onArrow(
    #        self.object.backwardForgetRight(basic.true)).forwardCompose(
    #          nt(basic.true)))

  # self must be contravariant.
  # return a path arrow "which exports as much as possible from nested Ands at the bottom".
  # FIXME: exportBottom has changed, change this function accordingly.
  def exportConjunctively(self):
    assert(not self.functor.covariant())
    trial = self.exportBottom()
    if trial is not None:
      return trial
    else:
      def maybeBackwardIntroduceUnit(x):
        if x.__class__ == And:
          if x.left == basic.true:
            return x.right.forwardAndTrue()
          elif x.right == basic.true:
            return x.left.forwardAndTrue().forwardFollow(lambda x:
                x.forwardCommute())
        return x.identity()
      return self.advanceLeft().forwardFollow(lambda x:
          x.exportConjunctively().forwardFollow(lambda x:
            x.retreat().forwardFollow(lambda x:
              x.advanceRight().forwardFollow(lambda x:
                x.exportConjunctively().forwardFollow(lambda x:
                  x.retreat().forwardFollow(lambda x:
                    x.forwardOnPathFollow(lambda x:
                      maybeBackwardIntroduceUnit(x))))))))

  def _forwardIdentityArrow(self, tgt):
    return Arrow(src = self, tgt = tgt, arrow = self.top().identity())

  def retreat(self):
    assert(self.functor.__class__ == Composite)
    (a, b) = self.functor.pop()
    return self._forwardIdentityArrow(Path(functor = b, object = a.onObject(self.object)))

  def advance(self):
    if self.object.__class__ == basic.Always:
      p = Path(functor = always_functor.compose(self.functor),
          object = self.object.value)
    elif self.object.__class__ == basic.Not:
      p = Path(functor = not_functor.compose(self.functor),
          object = self.object.value)
    elif self.object.__class__ == basic.Exists:
      p = Path(functor = Exists(variables = self.object.variables).compose(self.functor),
          object = self.object.value)
    elif self.object.__class__ == enriched.BoundedExists:
      p = Path(functor = BoundedExists(variables = self.object.variable,
        domains = self.object.domains).compose(self.functor),
        object = self.object.value)
    else:
      raise Exception("Can't advance path: %s\npast object: %s:"%(self,self.bottom()))
    return self._forwardIdentityArrow(p)
  def advanceLeft(self):
    return self.advanceToSide(left)
  def advanceRight(self):
    return self.advanceToSide(right)
  def advanceToSide(self, side):
    object = _getSide(side, self.object)
    other = _getSide(_swapSide(side), self.object)
    if self.object.__class__ == basic.And:
      p = Path(functor = And(side = side, other = other).compose(self.functor),
          object = object)
    else:
      assert(self.object.__class__ == basic.Or)
      p = Path(functor = Or(side = side, other = other).compose(self.functor),
          object = object)
    return self._forwardIdentityArrow(p)

  def forwardOnPath(self, arrow):
    assert(isinstance(arrow, basic.Arrow))
    if self.covariant():
      assert(self.object == arrow.src)
      x = arrow.tgt
    else:
      assert(self.object == arrow.tgt)
      x = arrow.src
    return Arrow(src = self,
        tgt = Path(functor = self.functor, object = x),
        arrow = self.functor.onArrow(arrow))
  def forwardOnPathFollow(self, f):
    return self.forwardOnPath(f(self.bottom()))

  # self must be covariant.
  # variables: a list of variables that are in scope
  # return: a list of pairs (B, a) such that B is the value of some importable bounded forall
  #         into which variables have been substituted
  #         and a is a path arrow leading to self.onObject((B|self.object)).
  def universalIn(self, variables):
    return [(S, Arrow(src = self,
      tgt = Path(functor = self.functor, object = basic.And(S, self.object)),
      arrow = toU.arrow.forwardCompose(toS.arrow)).forwardFollow(lambda p:
        p.forwardOnPathFollow(lambda x: x.forwardUndoubleDual())))
        # U is a bounded universal, S is the value of U with its variables substituted.
        for (U, toU) in self.importFilteredArrow(lambda x:
          enriched.isBoundedForall(x) and len(enriched.boundedForallVariables(x)) == len(variables))
        for (S, toS) in toU.tgt.advanceLeft().tgt.advance().tgt.instantiate()]

  # self must be contravariant.
  # self.object must be a bounded existential of the same length as variables
  # return a list of pairs (B, A) such that B is like self.object.value with substituted variables
  #   and A is a path arrow to self.onObject(B)
  def instantiate(self, variables):
    assert(not self.covariant())
    assert(self.object.__class__ == enirched.BoundedExists)
    assert(len(self.object.variables) == len(variables))
    if len(variables) == 0:
      newPath = Path(functor = self.functor, object = self.object.value)
      return [(self.object.value, self.forwardOnPathFollow(lambda x: x.backwardIntroExists()))]
    else:
      removedExists = enriched.BoundedExists(
      return [ 
          for (v, variables) in _functional_pops(variables)
          for (B, A) in Path(functor = self.functor,
            object = enriched.BoundedExists()).instantiate(variables)]

def _functional_pop(i, l):
  r = list(l)
  x = r.pop(i)
  return (x, r)

def _functional_pops(l):
  return [_functional_pop(i, l) for i in range(len(l))]

class Arrow:
  # src, tgt: paths
  # arrow: an arrow : src.top() --> tgt.top()
  def __init__(self, src, tgt, arrow):
    assert(src.top() == arrow.src)
    if not(tgt.top() == arrow.tgt):
      raise Exception("Incorrect path arrow\ntgt.top() = %s\narrow.tgt = %s"%(tgt.top(), arrow.tgt))
    assert(tgt.top() == arrow.tgt)
    self.src = src
    self.tgt = tgt
    self.arrow = arrow

  def translate(self):
    return Arrow(src = self.src.translate(),
        tgt = self.tgt.tranlate(),
        arrow = self.arrow.translate())

  def forwardCompose(self, other):
    assert(self.tgt.top() == other.src.top())
    return Arrow(src = self.src, tgt = other.tgt, arrow = self.arrow.forwardCompose(other.arrow))
  def backwardCompose(self, other):
    return other.forwardCompose(self)
  def forwardFollow(self, f):
    return self.forwardCompose(f(self.tgt))
  def backwardFollow(self, f):
    return self.backwardCompose(f(self.src))

left = 'left'
right = 'right'

def _swapSide(side):
  if side == left:
    return right
  else:
    assert(side == right)
    return left

def _getSide(side, object):
  if side == left:
    return object.left
  else:
    assert(side == right)
    return object.right

class BoundedExists(Endofunctor):
  def __init__(self, variables, domains):
    self.variables = variables
    self.domains = domains
    self.pairs = [(variables[i], domains[i]) for i in range(len(variables))]

  def __repr__(self):
    return "BoundedExists(%s)"%(self.pairs,)
  def translate(self):
    result = identity_functor
    for (v, d) in self.pairs:
      result = result.compose(And(side = right, other = basic.Holds(v, d)))
    return result.compose(Exists(self.variables))
  def _import(self, B):
    freeInB = B.freeVariables()
    for variable in self.variables:
      assert(variable not in freeInB)
    return (lambda x:
        SimpleEnrichedArrow(src = basic.And(B, self.onObject(x)),
          tgt = self.onObject(basic.And(B, x)),
          basicArrow = self.translate()._import(B)))
  def variables(self):
    return self.variables
  def onObject(self, object):
    return enriched.BoundedExists(variables = self.variables,
        domains = self.domains, value = object)
  def onArrow(self, arrow):
    return SimpleEnrichedArrow(src = self.onObject(arrow.src),
        tgt = self.onObject(arrow.tgt),
        basicArrow = self.translate().onArrow(arrow))
  def negations(self):
    return 0

class Exists(Endofunctor):
  def __init__(self, variables):
    self.variables = variables
  def __repr__(self):
    return "Exists(%s)"%(self.variables,)
  def _import(self, B):
    freeInB = B.freeVariables()
    for variable in self.variables:
      assert(variable not in freeInB)
    return (lambda x:
        basic.And(left = B, right = self.onObject(x)).forwardAndPastExists())
  def variables(self):
    return self.variables
  def onObject(self, object):
    return basic.Exists(variables = self.variables, value = object)
  def onArrow(self, arrow):
    return basic.OnBody(variables = self.variables, arrow = arrow)
  def negations(self):
    return 0

class Always(Endofunctor):
  def __repr__(self):
    return "!"
  def _import(self, B):
    # B|!X --> !(B|X) (not always possible!)
    # but when   B == !C
    # !C | !X --> !!C | !X --> ! (!C | X)
    if B.__class__ != Always:
      raise Exception("Unable to import B past Always when B is not also an Always.  B == %s"%(B,))
    else:
      C = B.value
      return (lambda x:
          And(left = B, right = self.onObject(x)).forwardOnLeftFollow(lambda x:
            x.forwardCojoin()).forwardFollow(lambda x:
              x.forwardZip()))

  def variables(self):
    return []
  def onObject(self, object):
    return basic.Always(object)
  def onArrow(self, arrow):
    return basic.OnAlways(arrow)
  def negations(self):
    return 0

always_functor = Always()

class Not(Endofunctor):
  def __repr__(self):
    return "~"
  # self must not be covariant()
  # return a function representing some natural transform: (B|.) o F o (B|.) --> F
  def _export(self, b):
    bAnd = lambda x: basic.And(left = b, right = x)
    return (lambda x:
        # B|(~(B|x)) --> ~x
        bAnd(self.onObject(bAnd(x))).forwardApply())
  def variables(self):
    return []
  def onObject(self, object):
    return basic.Not(object)
  def onArrow(self, arrow):
    return basic.OnNot(arrow)
  def negations(self):
    return 1

not_functor = Not()

class Id(Endofunctor):
  def __repr__(self):
    return "ID"
  def _import(self, B):
    # Id o (B|.) --> (B|.) o Id
    # (B|x) --> (B|x)
    return (lambda x:
        And(left = B, right = x).identity())
  def variables(self):
    return []
  def pop(self):
    raise Exception("Can't pop the identity functor.")
  def onObject(self, object):
    return object
  def onArrow(self, arrow):
    return arrow
  def negations(self):
    return 0

identity_functor = Id()

class Composite(Endofunctor):
  # if right is covariant, self will represent (left o right)
  # otherwise secod is contravariant, and self will represent (oppositeFunctor(left) o right)
  def __init__(self, left, right):
    self.left = left
    self.right = right

  def __repr__(self):
    return "%s\no\n%s"%(self.left, self.right)
  def _import(self, B):
    if self.right.covariant():
      assert(self.left.covariant())
      # F o G o (B|.) --> F o (B|.) o G --> (B|.) o F o G
      return (lambda x:
          self.right._import(B)(self.left.onObject(x)).forwardCompose(
            self.right.onArrow(self.left._import(B)(x))))
    else:
      assert(not self.right.covariant())
      assert(not self.left.covariant())
      # F o G o (B|.) --> (B|.) o F o (B|.) o G o (B|.) --> (B|.) o F o G
      bAnd = And(side = right, other = B)
      G_o_BAnd = self.right.compose(bAnd)
      return (lambda x:
          G_o_BAnd.onArrow(self.left._export(B)(x)).forwardCompose(
            self.right._export(B)(self.left.onObject(bAnd.onObject(x)))))

  def _export(self, B):
    bAnd = And(side = right, other = B)
    if self.right.covariant():
      assert(not self.left.covariant())
      # (B|.) o F o G o (B|.) --> (B|.) o F o (B|.) o G --> F o G
      return (lambda x:
          self.right._import(B)(self.left.onObject(bAnd.onObject(x))).forwardCompose(
            self.right.onArrow(self.left._export(B)(x))))
    else:
      assert(not self.right.covariant())
      assert(self.left.covariant())
      # (B|.) o F o G o (B|.) --> F o (B|.) o G o (B|.) --> F o G
      return (lambda x:
          bAnd.onArrow(self.right.onArrow(self.left._import(B)(x))).forwardCompose(
            self.right._export(B)(self.left.onObject(x))))

  def importFilteredCovariantCovariant(self, f):
    assert(self.left.covariant())
    assert(self.right.covariant())
    result = []
    # F o G --> ((B|.) o F) o G
    result.extend([(B_nt[0], lambda x:
      self.right.onArrow(B_nt[1](x))) for B_nt in self.left.importFiltered(f)])
    a = len(result)
    # F o G --> F o ((B|.) o G) --> (B|.) o F o G
    result.extend([(B_nt[0], lambda x:
      B_nt[1](self.left.onObject(x)).forwardCompose(
        self.right.onArrow(self.left._import(B_nt[0])(x)))) for B_nt in self.right.importFiltered(f)])
    return result

  def importFilteredContravariantContravariant(self, f):
    assert(not self.right.covariant())
    assert(not self.left.covariant())
    result = []
    # F o G --> ((B|.) o F) o G
    result.extend([(B_nt[0], lambda x:
      self.right.onArrow(B_nt[1](x))) for B_nt in self.left.exportFiltered(f)])
    # F o G --> ((B|.) o F o (B|.)) o G = ((B|.) o F) o ((B|.) o G) --> ((B|.) o F) o G
    result.extend([(B_nt[0], lambda x:
      self.right.onArrow(self.left._export(B_nt[0])(x)).forwardCompose(
        B_nt[1](self.left.onObject(basic.And(B_nt[0], x))))) for B_nt in self.right.exportFiltered(f)])
    return result

  def importFiltered(self, f):
    assert(self.covariant())
    if self.right.covariant():
      return self.importFilteredCovariantCovariant(f)
    else:
      return self.importFilteredContravariantContravariant(f)

  def exportFilteredContravariantCovariant(self, f):
    assert(self.right.covariant())
    assert(not self.left.covariant())
    result = []
    # (B|.) o F o G --> F o G
    result.extend([(B_nt[0], lambda x:
      self.right.onArrow(B_nt[1](x))) for B_nt in self.left.exportFiltered(f)])
    # (B|.) o F o G --> (B|.) o F o (B|.) o G --> F o G
    result.extend([(B_nt[0], lambda x:
      B_nt[1](self.left.onObject(basic.And(B_nt[0], x))).forwardCompose(
        self.right.onArrow(self.left._export(B_nt[0])))) for B_nt in self.right.importFiltered(f)])
    return result

  def exportFilteredCovariantContravariant(self, f):
    assert(self.left.covariant())
    assert(not self.right.covariant())
    result = []
    # (B|.) o F o G --> F o G
    result.extend([(B_nt[0], lambda x:
      self.right.onArrow(B_nt[1](x))) for B_nt in self.left.importFiltered(f)])
    # (B|.) o F o G --> F o (B|.) o G --> F o G
    result.extend([(B_nt[0], lambda x:
      self.right.onArrow(self.left._import(B_nt[0])(x)).forwardCompose(
        B_nt[1](self.left.onObject(x)))) for B_nt in self.right.exportFiltered(f)])
    return result

  # self must not be covariant()
  # return (B, a function representing some natural transform: (B|.) o F (B|.) --> F)
  # such that f(B) == True, or return None if no such natural transform exists.
  def exportFiltered(self, f):
    if self.right.covariant():
      return self.exportFilteredContravariantCovariant(f)
    else:
      return self.exportFilteredCovariantContravariant(f)


  def variables(self):
    result = list(self.left.variables())
    result.extend(self.right.variables())
    return result
  def pop(self):
    (a, b) = self.left.pop()
    return (a, b.compose(self.right))
  def onObject(self, object):
    return self.right.onObject(self.left.onObject(object))
  def onArrow(self, arrow):
    return self.right.onArrow(self.left.onArrow(arrow))
  def negations(self):
    return self.left.negations() + self.right.negations()

class Conjunction(Endofunctor):
  def __init__(self, side, other):
    self.side = side
    self.other = other

  def __repr__(self):
    if self.side == left:
      return "(.%s%s)"%(self.stringDivider(), self.other,)
    else:
      assert(self.side == right)
      return '(%s%s.)'%(self.other, self.stringDivider())

  def variables(self):
    return []
  def createObject(self, left, right):
    raise Exception("Abstract superclass.")
  def createArrow(self, leftArrow, rightArrow):
    return basic.OnConjunction(leftArrow = leftArrow, rightArrow = rightArrow,
        src = self.createObject(left = leftArrow.src, right = rightArrow.src),
        tgt = self.createObject(left = leftArrow.tgt, right = rightArrow.tgt))

  def onObject(self, object):
    if self.side == left:
      return self.createObject(left = object, right = self.other)
    else:
      assert(self.side == right)
      return self.createObject(left = self.other, right = object)

  def onArrow(self, arrow):
    if self.side == left:
      return self.createArrow(leftArrow = arrow, rightArrow = self.other.identity())
    else:
      assert(self.side == right)
      return self.createArrow(leftArrow = self.other.identity(), rightArrow = arrow)

  def negations(self):
    return 0

class And(Conjunction):
  def createObject(self, left, right):
    return basic.And(left = left, right = right)

  def stringDivider(self):
    return "|"

  def _import(self, B):
    bAnd = And(side = right, other = B)
    if self.side == left:
      # B|(X|OTHER) --> (B|X) | OTHER
      return (lambda x: bAnd.onObject(self.onObject(x)).forwardAssociateOther())
    else:
      assert(self.side == right)
      # B|(OTHER|X) --> (OTHER|X)|B --> (OTHER|(X|B)) --> (OTHER|(B|X))
      return (lambda x:
          bAnd.onObject(self.onObject(x)).forwardCommute().forwardFollow(lambda x:
            x.forwardAssociate().forwardFollow(lambda x:
              x.forwardOnRightFollow(lambda x:
                x.forwardCommute()))))

  def importFiltered(self, f):
    if self.side == left:
      # (X|A) --> (X|(B|A)) --> ((X|B)|A) --> ((B|X)|A)
      return [(a.tgt.left, lambda x:
        self.onObject(x).forwardOnRight(a).forwardFollow(lambda x:
          x.forwardAssociateOther().forwardFollow(lambda x:
            x.forwardOnLeftFollow(lambda x:
              x.forwardCommute())))) for a in self.other.produceFiltered(f)]
    else:
      # (A|X) --> ((B|A)|X) --> ((A|B)|X) --> (A|(B|X))
      assert(self.side == right)
      return [(a.tgt.left, lambda x:
        self.onObject(x).forwardOnLeft(a.forwardFollow(lambda x:
          x.forwardCommute())).forwardFollow(lambda x:
            x.forwardAssociate())) for a in self.other.produceFiltered(f)]

class Or(Conjunction):
  def stringDivider(self):
    return "-"
  def _import(self, B):
    bAnd = And(side = right, other = B)
    if self.side == left:
      # B|(X-OTHER) --> (B|X)-OTHER
      return (lambda x:
          bAnd.onObject(self.onObject(x)).forwardDistributeLeft())
    else:
      assert(self.side == right)
      # B|(OTHER-X) --> (OTHER-(B|X))
      return (lambda x:
          bAnd.onObject(self.onObject(x)).forwardDistributeRight())

  def createObject(self, left, right):
    return basic.Or(left = left, right = right)

