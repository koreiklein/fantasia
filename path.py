# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic

class Endofunctor:
  def onObject(self, object):
    raise Exception("Abstract superclass.")
  def onArrow(self, arrow):
    raise Exception("Abstract superclass.")
  def negations(self):
    raise Exception("Abstract superclass.")
  def covariant(self):
    return 0 == (self.negations() % 2)

class Path:
  def __init_(self, endofunctor, object):
    self.endofunctor = endofunctor
    self.object = object

  def top(self):
    return self.endofunctor.onObject(self.object)
  def bottom(self):
    return self.object

left = 'left'
right = 'right'

class Always(Endofunctor):
  def onObject(self, object):
    return basic.Always(object)
  def onArrow(self, arrow):
    return basic.OnAlways(arrow)
  def negations(self):
    return 0

class Not(Endofunctor):
  def onObject(self, object):
    return basic.Not(object)
  def onArrow(self, arrow):
    return basic.OnNot(arrow)
  def negations(self):
    return 1

class Composite(Endofunctor):
  # if second is covariant, self will represent (first o second)
  # otherwise secod is contravariant, and self will represent (oppositeFunctor(first) o second)
  def __init__(self, first, second):
    self.first = first
    self.second = second

  def onObject(self, object):
    return self.second.onObject(self.first.onObject(object))
  def onArrow(self, arrow):
    return self.second.onArrow(self.first.onArrow(object))
  def negations(self):
    return self.first.negations() + self.second.negations()

class Conjunction(Endofunctor):
  def __init__(self, side, other):
    self.side = side
    self.other = other

  def createObject(self, left, right):
    raise Exception("Abstract superclass.")
  def createArrow(self, leftArrow, rightArrow):
    return basic.OnConjunction(leftArrow = leftArrow, rightArrow = rightArrow,
        src = self.createObject(left = leftArrow.src, right = rightArrow.src),
        tgt = self.createObject(left = leftArrow.tgt, right = rightArrow.tgt),

  def onObject(self, object):
    if self.side == left:
      return self.createObject(left = object, right = self.other)
    else:
      assert(self.side == right)
      return self.createObject(left = self.other, right = object)

  def onArrow(self, arrow):
    if self.side == left:
      return self.createArrow(left = arrow, right = self.other.identity())
    else:
      assert(self.side == right)
      return self.createArrow(left = self.other.identity(), right = arrow)

  def negations(self):
    return 0

class And(Conjunction):
  def createObject(self, left, right):
    return basic.And(left = left, right = right)
class Or(Conjunction):
  def createObject(self, left, right):
    return basic.Or(left = left, right = right)

