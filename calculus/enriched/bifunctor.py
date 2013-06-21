# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import forumla

class Bifunctor:
  def translate(self):
    raise Exception("Abstract superclass.")
  def variables(self):
    raise Exception("Abstract superclass.")
  def onObjects(self, left, right):
    raise Exception("Abstract superclass.")

  def transport(self, B):
    return self.translate().transport(B.translate())

  def onArrows(self, left, right):
    return formula.Arrow(src = self.onObjects(left.src, right.src),
        tgt = self.onObjects(left.tgt, right.tgt),
        basicArrow = self.translate().onArrows(left.translate(), right.translate()))


class PostcompositeBifunctor(Bifunctor):
  def __init__(self, bifunctor, functor):
    self.bifunctor = bifunctor
    self.functor = functor

  def translate(self):
    return self.bifunctor.translate().compose(self.functor.translate())

  def onObjects(self, left, right):
    return self.functor.onObject(self.bifunctor.onObjects(left, right))

  def variables(self):
    result = []
    result.extend(self.bifunctor.variables())
    result.extend(self.functor.variables())
    return result

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

  def variables(self):
    result = []
    result.extend(self.left.variables)
    result.extend(self.right.variables)
    result.extend(self.bifunctor.variables)
    return result

  def translate(self):
    return self.bifunctor.translate().precompose(
        left = self.left.translate(),
        right = self.right.translate())

  def onObjects(self, left, right):
    return self.bifunctor.onObjects(self.left.onObject(left), self.right.onObject(right))

  def precompose(self, left, right):
    return PrecompositeBifunctor(bifunctor = self.bifunctor,
        left = left.compose(self.left),
        right = right.compose(self.right))

