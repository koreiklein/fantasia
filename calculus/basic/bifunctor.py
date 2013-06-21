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
  # return a function reperesenting a natural transform: F(B|., .) --> F(., B|.) if possible,
  #  otherwise, raise an intransportable exception.
  def transport(self, B):
    raise Exception("Abstract superclass.")

  # return a function representing a natural transform F(., .) o (B|.) --> F(B|., B|.)
  def _import(self, B):
    raise Exception("Abstract superclass.")

  # return those variable quantified anywhere in self.
  def variables(self):
    raise Exception("Abstract superclass.")

  # a natural transform F(., .) o (B|.) --> F(B|., .)
  def _importLeft(self, B):
    raise Exception("Abstract superclass.")
  # a natural transform F(., .) o (B|.) --> F(., B|.)
  def _importRight(self, B):
    raise Exception("Abstract superclass.")

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

class And(Bifunctor):
  def onObjects(self, left, right):
    return formula.And(left, right)
  def onArrows(self, left, right):
    return formula.OnAnd(left, right)
  def variables(self):
    return []
  def transport(self, B):
    # (B|x)|y --> B|(x|y)
    return (lambda x, y: formula.And(formula.And(B, x), y).forwardAssociate())
  def _import(self, B):
    # B|(x|y) --> (B|B)|(x|y) --> B|(B|(x|y)) --> B|((B|x)|y) --> (B|x)|(B|y)
    return (lambda x, y:
        formula.And(B, formula.And(x, y)).forwardOnLeftFollow(lambda f:
          f.forwardCopy()).forwardFollow(lambda f:
            f.forwardAssociate()).forwardFollow(lambda f:
              f.forwardOnRight(self._importLeft(B)(x, y))).forwardCompose(
                self._importRight(B)(formula.And(B, x), y)))

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
  def onObjects(self, left, right):
    return formula.Or(left, right)
  def onArrows(self, left, right):
    return formula.OnOr(left, right)
  def variables(self):
    return []
  def transport(self, B):
    raise UntransportingOrException(B)
  def _import(self, B):
    # B|(x-y) --> (B|x)-(B|y)
    return (lambda x, y:
        formula.And(B, formula.Or(x, y)).forwardDistibute())

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

  def variables(self):
    result = []
    result.extend(self.bifunctor.variables())
    result.extend(self.functor.variables())
    return result

  def onArrows(self, left, right):
    return self.functor.onArrow(self.bifunctor.onArrows(left, right))
  def onObjects(self, left, right):
    return self.functor.onObject(self.bifunctor.onObjects(left, right))
  def transport(self, B):
    nt = self.bifunctor.transport(B)
    return (lambda x: self.functor.onArrow(nt(x)))
  def precompose(self, left, right):
    return PostcompositeBifunctor(bifunctor = self.bifunctor.precompose(left, right),
        functor = self.functor)
  def compose(self, other):
    return PostcompositeBifunctor(bifunctor = self.bifunctor, functor = self.functor.compose(other))

  def _import(self, B):
    return (lambda left, right:
        self.functor._import(B)(self.bifunctor.onObjects(left, right)).forwardCompose(
          self.functor.onArrow(self.bifunctor._import(B)(left, right))))

class PrecompositeBifunctor(Bifunctor):
  def __init__(self, bifunctor, left, right):
    self.bifunctor = bifunctor
    self.left = left
    self.right = right

  def variables(self):
    result = []
    result.extend(self.left.variables)
    result.extend(self.right.variables)
    result.extend(self.bifunctor.variables)
    return result

  def onArrows(self, left, right):
    return self.bifunctor.onArrows(self.left.onArrow(left), self.right.onArrow(right))
  def onObjects(self, left, right):
    return self.bifunctor.onObjects(self.left.onObject(left), self.right.onObject(right))

  def precompose(self, left, right):
    return PrecompositeBifunctor(bifunctor = self.bifunctor,
        left = left.compose(self.left),
        right = right.compose(self.right))

  def transport(self, B):
    try:
      left = self.left.lift(B)
    except endofunctor.UnliftableException as e:
      raise UntransportableException(e)
    return (lambda x, y:
        self.bifunctor.onArrows(left(x), self.right.onObject(y).identity()).forwardCompose(
        self.bifunctor.transport(B)(self.left.onObject(x), self.right.onObject(y))).forwardCompose(
        self.bifunctor.onArrows(self.left.onObject(x).identity(), self.right._import(B)(y))))


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

  def variables(self):
    return self.bifunctor.variables()

  # self must be covariant
  # return a function representing some natural transform: (B|.) o F --> F o (B|.) if possible
  #  otherwise, throw an UnliftableException
  def lift(self, B):
    # TODO Consider actually lifting B.
    return UnliftableException(self, B)

  def onObject(self, object):
    return self.bifunctor.onObjects(object, object.updateVariables())
  def onArrow(self, arrow):
    return self.bifunctor.onArrows(arrow, arrow)
  def covariant(self):
    return True


def InDomain(x, e):
  return formula.Holds(x, variable.ProjectionVariable(e, domainSymbol))

def EqualUnder(a, b, e):
  return formula.Holds(
      variable.ProductVariable([(leftSymbol, a), (rightSymbol, b)]),
      variable.ProjectionVariable(e, relationSymbol))

def WellDefined(variable, newVariable, equivalence):
  isEqual = formula.And(
        formula.Always(InDomain(newVariable, equivalence)),
        formula.Always(EqualUnder(newVariable, variable, equivalence)))
  F = endofunctor.SubstituteVariable(variable, newVariable).compose(
      endofunctor.not_functor.compose(
        endofunctor.Exists(newVariable)).compose(
          endofunctor.And(side = right, other = isEqual)).compose(
            endofunctor.not_functor))
  return and_functor.precomposeRight(F).join()

