# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from misc import *
from calculus import variable
from lib import common_vars
from lib.common_symbols import domainSymbol, relationSymbol, leftSymbol, rightSymbol
from calculus.basic import endofunctor
from calculus.basic import formula

class UntransportableException(Exception):
  def __init__(self, unliftableException):
    self.unliftableException = unliftableException
  def __str__(self):
    return "UntransportableException caused by \n%s"%(self.unliftableException,)

class UntransportingOrException(UntransportableException):
  def __init__(self, B):
    self.B = B
  def __str__(self):
    return "UntransportingOrException can't transport %s"%(self.B,)

class Bifunctor:
  def onObjects(self, left, right):
    raise Exception("Abstract superclass.")
  def onArrows(self, left, right):
    raise Exception("Abstract superclass.")

  # return a function representing a natural transform F(., .) o (B|.) --> F(B|., B|.)
  def _import(self, B):
    raise Exception("Abstract superclass.")

  # return those variable quantified anywhere in self.
  def variables(self):
    raise Exception("Abstract superclass.")

  # a natural transform B|F(., .) --> F(B|., .)
  def _importLeft(self, B):
    raise Exception("Abstract superclass.")
  # a natural transform B|F(., .) --> F(., B|.)
  def _importRight(self, B):
    raise Exception("Abstract superclass.")

  # a natural transform F(B|., .) --> B|(F., .)
  # or raise an UnliftableException
  def _liftLeft(self, B):
    raise endofunctor.UnliftableException(self, B)
  # a natural transform F(., B|.) --> B|(F., .)
  # or raise an UnliftableException
  def _liftRight(self, B):
    raise endofunctor.UnliftableException(self, B)

  # B: an enriched formula such that B.forwardCopy() is defined.
  # return a function representing a natural transform: F(B, .) --> F(B, B|.)
  def transport_duplicating(self, B):
    # F(B, x) --> F(B|B, x) --> F(B, B|x)
    return (lambda x:
        self.onArrows(B.forwardCopy(), x.identity()).forwardCompose(
          self.transport(B)(B, x)))

  # return a function reperesenting a natural transform: F(B|., .) --> F(., B|.) if possible,
  #  otherwise, raise an intransportable exception.
  def transport(self, B):
    try:
      lifted = self._liftLeft(B)
    except endofunctor.UnliftableException as e:
      raise UntransportableException(e)
    # F(B|., .) --> B|F(., .) --> F(., B|.)
    return (lambda x, y:
        lifted(x, y).forwardCompose(self._importRight(B)(x, y)))

  def precompose(self, left, right):
    assert(left.covariant())
    assert(right.covariant())
    return PrecompositeBifunctor(self, left, right)
  def precomposeLeft(self, left):
    return self.precompose(left = left, right = endofunctor.identity_functor)
  def precomposeRight(self, right):
    return self.precompose(left = endofunctor.identity_functor, right = right)

  def compose(self, other):
    assert(other.covariant())
    return PostcompositeBifunctor(self, other)

  def join(self):
    return Join(self)

  def commute(self):
    return Commute(self)

class Commute(Bifunctor):
  def __init__(self, bifunctor):
    self.bifunctor = bifunctor

  def __repr__(self):
    return "commute %s"%(self.bifunctor,)

  def onObjects(self, left, right):
    return self.bifunctor.onObjects(right, left)
  def onArrows(self, left, right):
    return self.bifunctor.onArrows(right, left)
  def _import(self, B):
    return (lambda x, y:
        self.bifunctor._import(B)(y, x))
  def variables(self):
    return self.bifunctor.variables()
  def _importLeft(self, B):
    return (lambda x, y:
        self.bifunctor._importRight(B)(y, x))
  def _importRight(self, B):
    return (lambda x, y:
        self.bifunctor._importLeft(B)(y, x))
  def _liftLeft(self, B):
    # May throw an exception.
    lift = self.bifunctor._liftRight(B)
    return (lambda x, y:
        lift(y, x))
  def _liftRight(self, B):
    # May throw an exception.
    lift = self.bifunctor._liftLeft(B)
    return (lambda x, y:
        lift(y, x))

class And(Bifunctor):
  def __repr__(self):
    return "AND"
  def onObjects(self, left, right):
    return formula.And(left, right)
  def onArrows(self, left, right):
    return formula.OnAnd(left, right)
  def variables(self):
    return []
  def _import(self, B):
    # B|(x|y) --> (B|B)|(x|y) --> B|(B|(x|y)) --> B|((B|x)|y) --> (B|x)|(B|y)
    return (lambda x, y:
        formula.And(B, formula.And(x, y)).forwardOnLeftFollow(lambda f:
          f.forwardCopy()).forwardFollow(lambda f:
            f.forwardAssociate()).forwardFollow(lambda f:
              f.forwardOnRight(self._importLeft(B)(x, y))).forwardCompose(
                self._importRight(B)(formula.And(B, x), y)))

  def _liftLeft(self, B):
    # ((B|x)|y) --> B|(x|y)
    return (lambda x, y: self.onObjects(formula.And(B, x), y).forwardAssociate())
  def _liftRight(self, B):
    # (x|(B|y)) --> (x|B)|y --> (B|x)|y --> B|(x|y)
    return (lambda x, y:
        self.onObjects(x, formula.And(B, y)).forwardAssociateOther().forwardFollow(lambda x:
          x.forwardOnLeftFollow(lambda x:
            x.forwardCommute()).forwardFollow(lambda x:
              x.forwardAssociate())))
  def _importLeft(self, B):
    # B|(x|y) --> (B|x)|y
    return (lambda x, y: formula.And(B, formula.And(x, y)).forwardAssociateOther())
  def _importRight(self, B):
    # B|(x|y) --> (x|y)|B --> x|(y|B) --> x|(B|y)
    return (lambda x, y:
        formula.And(B, formula.And(x, y)).forwardCommute().forwardFollow(lambda x:
          x.forwardAssociate()).forwardFollow(lambda x:
            x.forwardOnRightFollow(lambda x:
              x.forwardCommute())))

and_functor = And()

class Or(Bifunctor):
  def __repr__(self):
    return "OR"
  def onObjects(self, left, right):
    return formula.Or(left, right)
  def onArrows(self, left, right):
    return formula.OnOr(left, right)
  def variables(self):
    return []
  def _import(self, B):
    # B|(x-y) --> (B|x)-(B|y)
    return (lambda x, y:
        formula.And(B, formula.Or(x, y)).forwardDistribute())

  def _importLeft(self, B):
    return (lambda x, y:
        self._import(x, y).forwardCompose(self.onArrows(formula.And(B, x).identity(),
          formula.And(B.updateVariables(), y).forwardForgetLeft())))
  def _importRight(self, B):
    return (lambda x, y:
        self._import(x, y).forwardCompose(self.onArrows(formula.And(B, x).forwardForgetLeft(),
          formula.And(B.updateVariables(), y).identity())))

or_functor = Or()

class PostcompositeBifunctor(Bifunctor):
  def __init__(self, bifunctor, functor):
    self.bifunctor = bifunctor
    self.functor = functor
  
  def __repr__(self):
    return "%s . %s"%(self.bifunctor, self.functor)

  def variables(self):
    result = []
    result.extend(self.bifunctor.variables())
    result.extend(self.functor.variables())
    return result

  def _liftLeft(self, B):
    # The following two lines may throw an exception
    bifunctor_nt = self.bifunctor._liftLeft(B)
    functor_nt = self.functor.lift(B)
    return (lambda x, y:
        self.functor.onArrow(bifunctor_nt(x, y)).forwardCompose(
          functor_nt(self.bifunctor.onObjects(x, y))))

  def _liftRight(self, B):
    # The following two lines may throw an exception
    bifunctor_nt = self.bifunctor._liftRight(B)
    functor_nt = self.functor.lift(B)
    return (lambda x, y:
        self.functor.onArrow(bifunctor_nt(x, y)).forwardCompose(
          functor_nt(self.bifunctor.onObjects(x, y))))

  def onArrows(self, left, right):
    return self.functor.onArrow(self.bifunctor.onArrows(left, right))
  def onObjects(self, left, right):
    return self.functor.onObject(self.bifunctor.onObjects(left, right))
  def precompose(self, left, right):
    return PostcompositeBifunctor(bifunctor = self.bifunctor.precompose(left, right),
        functor = self.functor)
  def compose(self, other):
    return PostcompositeBifunctor(bifunctor = self.bifunctor, functor = self.functor.compose(other))

  def _import(self, B):
    return (lambda left, right:
        self.functor._import(B)(self.bifunctor.onObjects(left, right)).forwardCompose(
          self.functor.onArrow(self.bifunctor._import(B)(left, right))))

  def _importLeft(self, B):
    return (lambda x, y:
        self.functor._import(B)(self.bifunctor.onObjects(x, y)).forwardCompose(
          self.functor.onArrow(self.bifunctor._importLeft(B)(x, y))))

  def _importRight(self, B):
    return (lambda x, y:
        self.functor._import(B)(self.bifunctor.onObjects(x, y)).forwardCompose(
          self.functor.onArrow(self.bifunctor._importRight(B)(x, y))))

class PrecompositeBifunctor(Bifunctor):
  def __init__(self, bifunctor, left, right):
    self.bifunctor = bifunctor
    self.left = left
    self.right = right
    
  def __repr__(self):
    return "%s x %s . %s"%(self.left, self.right, self.bifunctor)

  def variables(self):
    result = []
    result.extend(self.left.variables)
    result.extend(self.right.variables)
    result.extend(self.bifunctor.variables)
    return result

  def _liftLeft(self, B):
    # The following two lines may throw an exception.
    bifunctor_nt = self.bifunctor._liftLeft(B)
    left_nt = self.left.lift(B)
    return (lambda x, y:
        self.bifunctor.onArrows(left_nt(x), self.right.onObject(y).identity()).forwardCompose(
          bifunctor_nt(self.left.onObject(x), self.right.onObject(y))))

  def _liftRight(self, B):
    # The following two lines may throw an exception.
    bifunctor_nt = self.bifunctor._liftRight(B)
    right_nt = self.right.lift(B)
    return (lambda x, y:
        self.bifunctor.onArrows(self.left.onObject(x).identity(), right_nt(y)).forwardCompose(
          bifunctor_nt(self.left.onObject(x), self.right.onObject(y))))

  def onArrows(self, left, right):
    return self.bifunctor.onArrows(self.left.onArrow(left), self.right.onArrow(right))
  def onObjects(self, left, right):
    return self.bifunctor.onObjects(self.left.onObject(left), self.right.onObject(right))

  def precompose(self, left, right):
    return PrecompositeBifunctor(bifunctor = self.bifunctor,
        left = left.compose(self.left),
        right = right.compose(self.right))

  # a natural transform B|F(., .) --> F(., B|.)
  def _importRight(self, B):
    #B| F(L(.), R(.)) --> F(L(.), B|R(.)) --> F(L(.), R(B|.))
    return (lambda left, right:
        self.bifunctor._importRight(B)(self.left.onObject(left),
          self.right.onObject(right)).forwardCompose(
            self.bifunctor.onArrows(self.left.onObject(left).identity(),
              self.right._import(B)(right))))

  def _importLeft(self, B):
    #B| F(L(.), R(.)) --> F(B|L(.), R(.)) --> F(L(B|.), R(.))
    return (lambda left, right:
        self.bifunctor._importLeft(B)(self.left.onObject(left),
          self.right.onObject(right)).forwardCompose(
            self.bifunctor.onArrows(self.left._import(B)(left),
              self.right.onObject(right).identity())))

  def _import(self, B):
    return (lambda left, right:
        self.bifunctor._import(B)( self.left.onObject(left)
                                 , self.right.onObject(right)).forwardCompose(
          self.bifunctor.onArrows( self.left._import(B)(left)
                                 , self.right._import(B)(right))))

# for a bifunctor F, Join(F) is the endofunctor F(x, x) obtained by precomposing F with the diagonal.
class Join(endofunctor.Endofunctor):
  def __init__(self, bifunctor):
    self.bifunctor = bifunctor

  def __repr__(self):
    return "JoinBifunctor(%s)"%(self.bifunctor,)

  # self must be covariant()
  # f takes each object x to a list f(x)
  # return a list of all triples [(B, nt, y)] such that
  #   nt is a natural transform self -> (B|.) o self
  #   y is in f(B)
  def importFiltered(self, f):
    return []
  # self must be covariant()
  # return a function representing a natural transform: F o (B|.) --> (B|.) o F
  def _import(self, B):
    return (lambda x:
        self.bifunctor._import(B)(x, x.updateVariables()))

  def lift(self, B):
    try:
      left = self.bifunctor._liftLeft(B)
      return (lambda x:
          self.bifunctor.onArrows( formula.And(B, x).identity()
                                 , formula.And(B, x).forwardForgetLeft()).forwardCompose(
            left(x, x)))
    except endofunctor.UnliftableException as e:
      # The following line may raise an exception.
      right = self.bifunctor._liftRight
      return (lambda x:
          self.bifunctor.onArrows( formula.And(B, x).forwardForgetLeft()
                                 , formula.And(B, x).identity()).forwardCompose(
            right(x, x)))

  def variables(self):
    return self.bifunctor.variables()

  # self must be covariant
  # return a function representing some natural transform: (B|.) o F --> F o (B|.) if possible
  #  otherwise, throw an UnliftableException
  def lift(self, B):
    # TODO Consider actually lifting B.
    return endofunctor.UnliftableException(self, B)

  def onObject(self, object):
    return self.bifunctor.onObjects(object, object.updateVariables())
  def onArrow(self, arrow):
    return self.bifunctor.onArrows(arrow, arrow)
  def covariant(self):
    return True

