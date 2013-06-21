# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.basic import endofunctor
from calculus.basic import formula

class UntransportableException(Exception):
  def __init__(self, unliftableException):
    self.unliftableException = unliftableException
  def __str__(self):
    return "UntransportableException cause by \n%s"%(self.unliftableException,)

class Bifunctor:
  def onObjects(self, left, right):
    raise Exception("Abstract superclass.")
  def onArrows(self, left, right):
    raise Exception("Abstract superclass.")
  # return a function reperesenting a natural transform: F(B|., .) --> F(., B|.) if possible,
  #  otherwise, raise an intransportable exception.
  def transport(self, B):
    raise Exception("Abstract superclass.")

  def precompose(self, left, right):
    return PrecompositeBifunctor(self, left, right)

  def compose(self, other):
    return PostcompositeBifunctor(self, other)

class And(Bifunctor):
  def onObjects(self, left, right):
    return formula.And(left, right)
  def onArrows(self, left, right):
    return formula.OnAnd(left, right)
  def transport(self, B):
    # (B|x)|y --> B|(x|y)
    return (lambda x, y: formula.And(formula.And(B, x), y).forwardAssociate())

class PostcompositeBifunctor(Bifunctor):
  def __init__(self, bifunctor, functor):
    self.bifunctor = bifunctor
    self.functor = functor

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

class PrecompositeBifunctor(Bifunctor):
  def __init__(self, bifunctor, left, right):
    self.bifunctor = bifunctor
    self.left = left
    self.right = right

  def onArrow(self, left, right):
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
