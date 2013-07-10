# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from misc import *
from calculus.basic import formula

class UnliftableException(Exception):
  def __init__(self, functor, B):
    self.functor = functor
    self.B = B
  def __str__(self):
    return "%s does not move past %s"%(self.B, self.functor)

class UnimportableException(Exception):
  def __init__(self, formula, endofunctor):
    self.formula = formula
    self.endofunctor = endofunctor
  def __str__(self):
    return "UnimportableException: can import %s through %s"%(self.formula, self.endofunctor)

class Endofunctor:
  def variables(self):
    raise Exception("Abstract superclass.")

  # self must be covariant()
  # f takes each object x to a list f(x)
  # return a list of all triples [(B, nt, y)] such that
  #   nt is a natural transform self -> (B|.) o self
  #   y is in f(B)
  def importFiltered(self, f):
    return []
  # self must not be covariant()
  # f takes each object x to a list f(x)
  # return a list of all triples [(B, nt, y)] such that
  #   nt is a natural transform (B|.) o self -> self
  #   y is in f(B)
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

  # self must be covariant
  # return a function representing some natural transform: (B|.) o F --> F o (B|.) if possible
  #  otherwise, throw an UnliftableException
  def lift(self, B):
    raise UnliftableException(self, B)
  # return a (its tgt, function represention some natural transform:
  #   (Exists variable .) o F -> G o (Exists variable .) o H such that
  #   G o H = F and H is as small as reasonably possible.)
  def liftExists(self, variable):
    (extent, x) = self._liftExists(variable)
    if extent == 'partial':
      return x
    else:
      assert(extent == 'full')
      nt = x
      return (self.compose(Exists(variable)), nt)

  # return either:
  #   ('full', nt) for a full lift
  #   ('partial', (tgt, nt)) for a partial lift
  def _liftExists(self, variable):
    return ('partial', ( Exists(variable).compose(self)
                       , lambda x: self.onObject(formula.Exists(variable, x)).identity()))

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

  # self must be covariant()
  # formula: a formula
  # return: a a natural transform self -> (B|.) o self
  #    or raise an UnimportableException if no such natural transform exists.
  def importExactly(self, formula):
    def f(x):
      if x == formula:
        return ['dummy']
      else:
        return []
    result = self.importFiltered(f)
    if len(result) == 0:
      raise UnimportableException(formula = formula, endofunctor = self)
    else:
      (B, nt, y) = result[0]
      assert(B == formula)
      return nt


class Exists(Endofunctor):
  def __init__(self, variable):
    self.variable = variable
  def __repr__(self):
    return "Exists(%s)"%(self.variable,)
  def _import(self, B):
    assert(self.variable not in B.freeVariables())
    return (lambda x:
        formula.And(left = B, right = self.onObject(x)).forwardAndPastExists())
  def variables(self):
    return [self.variable]
  def onObject(self, object):
    return formula.Exists(variable = self.variable, value = object)
  def onArrow(self, arrow):
    return formula.OnBody(variable = self.variable, arrow = arrow)
  def negations(self):
    return 0

  def lift(self, B):
    if self.variable in B.freeVariables():
      raise UnliftableException(self, B)
    else:
      # Exist a . (B|x) --> B|(Exists a.x)
      return (lambda x: formula.And(B, self.onObject(x)).forwardAndPastExists().invert())

class Always(Endofunctor):
  def __repr__(self):
    return "!"
  def _import(self, B):
    # B|!X --> !(B|X) (not always possible!)
    # but when   B == !C
    # !C | !X --> !!C | !X --> ! (!C | X)
    if B.__class__ != formula.Always:
      raise Exception("Unable to import B past Always when B is not also an Always.  B == %s"%(B,))
    else:
      C = B.value
      return (lambda x:
          formula.And(left = B, right = self.onObject(x)).forwardOnLeftFollow(lambda x:
            x.forwardCojoin()).forwardFollow(lambda x:
              x.forwardZip()))

  # return either:
  #   ('full', nt) for a full lift
  #   ('partial', (tgt, nt)) for a partial lift
  def _liftExists(self, variable):
    return ('full', lambda x: self.onObject(formula.Exists(variable, x)).forwardAlwaysPastExists())

  def variables(self):
    return []
  def onObject(self, object):
    return formula.Always(object)
  def onArrow(self, arrow):
    return formula.OnAlways(arrow)
  def negations(self):
    return 0

always_functor = Always()

class Not(Endofunctor):
  def __repr__(self):
    return "~"
  # self must not be covariant()
  # return a function representing some natural transform: (B|.) o F o (B|.) --> F
  def _export(self, b):
    bAnd = lambda x: formula.And(left = b, right = x)
    return (lambda x:
        # B|(~(B|x)) --> ~x
        bAnd(self.onObject(bAnd(x))).forwardApply())
  def variables(self):
    return []
  def onObject(self, object):
    return formula.Not(object)
  def onArrow(self, arrow):
    return formula.OnNot(arrow)
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
        formula.And(left = B, right = x).identity())
  def lift(self, B):
    return (lambda x: formula.And(left = B, right = x).identity())
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

  def covariant(self):
    if self.left.covariant():
      return self.right.covariant()
    else:
      return not self.right.covariant()

  def lift(self, B):
    # One of the following two calls may throw an exception, pass it on.
    left = self.left.lift(B)
    right = self.right.lift(B)
    return (lambda x:
        self.right.onArrow(left(x)).forwardCompose(right(self.left.onObject(x))))

  # return either:
  #   ('full', nt) for a full lift
  #   ('partial', (tgt, nt)) for a partial lift
  def _liftExists(self, variable):
    (extent0, x0) = self.left._liftExists(variable)
    if extent0 == 'partial':
      (tgt, nt) = x0
      return ('partial', ( tgt.compose(self.right)
                       , lambda x: self.right.onArrow(nt(x))))
    else:
      assert(extent0 == 'full')
      nt0 = x0
      (extent1, x1) = self.right._liftExists(variable)
      if extent1 == 'partial':
        (tgt, nt1) = x1
        # (Exists x.) o F o G -> F o (Exists x.) o G -> F o (H o (Exists x.) o K)
        return ('partial', ( self.left.compose(tgt)
                         , lambda x: self.right.onArrow(nt0(x)).forwardCompose(
                             nt1(self.left.onObject(x)))))
      else:
        assert(extent1 == 'full')
        # (Exists x.) o F o G -> F o (Exists x.) o G -> F o G o (Exists x.)
        return ('full', lambda x: self.right.onArrow(nt0(x)).forwardCompose(
                          nt1(self.left.onObject(x))))

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
    result.extend([(B, lambda x, nt=nt: self.right.onArrow(nt(x)), X)
                   for B, nt, X in self.left.importFiltered(f)])
    # F o G --> F o ((B|.) o G) --> (B|.) o F o G
    result.extend([(B, lambda x, B=B, nt=nt: nt(self.left.onObject(x)).forwardCompose(
                                 self.right.onArrow(self.left._import(B)(x))), X)
                    for B, nt, X in self.right.importFiltered(f)])
    return result

  def importFilteredContravariantContravariant(self, f):
    assert(not self.right.covariant())
    assert(not self.left.covariant())
    result = []
    # F o G --> ((B|.) o F) o G
    result.extend([(B, lambda x, nt=nt: self.right.onArrow(nt(x)), X)
                   for B, nt, X in self.left.exportFiltered(f)])
    # F o G --> ((B|.) o F o (B|.)) o G = ((B|.) o F) o ((B|.) o G) --> ((B|.) o F) o G
    result.extend([(B, lambda x, B=B, nt=nt: self.right.onArrow(self.left._export(B)(x)).forwardCompose(
                                nt(self.left.onObject(formula.And(B, x)))), X)
                   for B, nt, X in self.right.exportFiltered(f)])
    return result

  # self must be covariant()
  # f takes each object x to a list f(x)
  # return a list of all triples [(B, nt, y)] such that
  #   nt is a natural transform self -> (B|.) o self
  #   y is in f(B)
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
    result.extend([(B, lambda x, nt=nt: self.right.onArrow(nt(x)), X)
                   for B, nt, X in self.left.exportFiltered(f)])
    # (B|.) o F o G --> (B|.) o F o (B|.) o G --> F o G
    result.extend([(B, lambda x, B=B, nt=nt: nt(self.left.onObject(formula.And(B, x))).forwardCompose(
                                 self.right.onArrow(self.left._export(B)(x))), X)
                   for B, nt, X in self.right.importFiltered(f)])
    return result

  def exportFilteredCovariantContravariant(self, f):
    assert(self.left.covariant())
    assert(not self.right.covariant())
    result = []
    # (B|.) o F o G --> F o G
    result.extend([(B, lambda x, nt=nt: self.right.onArrow(nt(x)), X)
                   for B, nt, X in self.left.importFiltered(f)])
    # (B|.) o F o G --> F o (B|.) o G --> F o G
    result.extend([(B, lambda x, B=B, nt=nt: self.right.onArrow(self.left._import(B)(x)).forwardCompose(
                                 nt(self.left.onObject(x))), X)
                   for B, nt, X in self.right.exportFiltered(f)])
    return result

  # self must not be covariant()
  # f takes each object x to a list f(x)
  # return a list of all triples [(B, nt, y)] such that
  #   nt is a natural transform (B|.) o self -> self
  #   y is in f(B)
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
    return formula.OnConjunction(leftArrow = leftArrow, rightArrow = rightArrow,
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
    return formula.And(left = left, right = right)

  def stringDivider(self):
    return "|"

  def lift(self, B):
    if self.side == left:
      # (B|x)|Y --> B|(x|Y)
      return (lambda x: self.onObject(formula.And(B, x)).forwardAssociate())
    else:
      assert(self.side == right)
      # Y|(B|x) --> (B|x)|Y --> B|(x|Y) --> B|(Y|x)
      return (lambda x:
          self.onObject(formula.And(B, x)).forwardCommute().forwardFollow(lambda x:
            x.forwardAssociate().forwardFollow(lambda x:
              x.forwardOnRightFollow(lambda x:
                x.forwardCommute()))))

  # return a function represention some natural transform:
  #   (Exists variable .) o F -> G o (Exists variable .) o H such that
  #   G o H = F and H is as small as reasonably possible.
  def _liftExists(self, variable):
    if self.side == left:
      # (Exists variable .) o (.|B) -> (.|B) o (Exists variable .)
      return ('full', lambda x: self.onObject(formula.Exists(variable, x)).forwardAndPastExistsOther())
    else:
      assert(self.side == right)
      # (Exists variable .) o (B|.) -> (B|.) o (Exists variable .)
      return ('full', lambda x: self.onObject(formula.Exists(variable, x)).forwardAndPastExists())

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

  # self must be covariant()
  # f takes each object x to a list f(x)
  # return a list of triples all [(B, nt, y) such that
  #   nt is a natural transform self -> (B|.) o self
  #   y is in f(B)
  def importFiltered(self, f):
    if self.side == left:
      # (X|A) --> (X|(B|A)) --> ((X|B)|A) --> ((B|X)|A)
      return [(a.tgt.left, lambda x, a=a:
        self.onObject(x).forwardOnRight(a).forwardFollow(lambda x:
          x.forwardAssociateOther().forwardFollow(lambda x:
            x.forwardOnLeftFollow(lambda x:
              x.forwardCommute()))), X) for a, X in self.other.produceFiltered(f)]
    else:
      # (A|X) --> ((B|A)|X) --> ((A|B)|X) --> (A|(B|X))
      assert(self.side == right)
      return [(a.tgt.left, lambda x, a=a:
        self.onObject(x).forwardOnLeft(a.forwardFollow(lambda x:
          x.forwardCommute())).forwardFollow(lambda x:
            x.forwardAssociate()), X) for a, X in self.other.produceFiltered(f)]

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
    return formula.Or(left = left, right = right)

class SubstituteVariable(Endofunctor):
  def __init__(self, oldVariable, newVariable):
    self.oldVariable = oldVariable
    self.newVariable = newVariable
  def variables(self):
    return []
  def _import(self, B):
    free = B.freeVariables()
    if self.oldVariable in free or self.newVariable in free:
      # TODO Investigate whether this is necessary.
      raise UnliftableException(self, B)
    else:
      return (lambda x: formula.And(B, self.onObject(x)).identity())
  def lift(self, B):
    free = B.freeVariables()
    if self.oldVariable in free or self.newVariable in free:
      # TODO Investigate whether this is necessary.
      raise UnliftableException(self, B)
    else:
      return (lambda x: formula.And(B, self.onObject(x)).identity())
  def onObject(self, object):
    return object.substituteVariable(self.oldVariable, self.newVariable)
  def onArrow(self, arrow):
    return arrow.substituteVariable(self.oldVariable, self.newVariable)
  def negations(self):
    return 0
