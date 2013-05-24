# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic
from lib import common_vars

class Endofunctor:
  def variables(self):
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
    return (self, identity_endofunctor)
  def compose(self, other):
    if self.__class__ == Id:
      return other
    elif other.__class__ == Id:
      return self
    else:
      return Composite(left = self, right = other)

def new_path(object):
  return Path(identity_endofunctor, object)

class Path:
  def __init_(self, endofunctor, object):
    self.endofunctor = endofunctor
    self.object = object

  def variables(self):
    return self.endofunctor.variables()
  def top(self):
    return self.endofunctor.onObject(self.object)
  def bottom(self):
    return self.object
  def functor(self):
    return self.endofunctor

  def retreat(self):
    assert(self.endofunctor.__class__ == Composite)
    (a, b) = self.endofunctor.pop()
    return Path(endofunctor = b, object = a.onObject(self.object))

  def advance(self):
    if self.object.__class__ == basic.Always:
      return Path(endofunctor = always_endofunctor.compose(self.endofunctor),
          object = self.object.value)
    elif self.object.__class__ == basic.Not:
      return Path(endofunctor = not_endofunctor.compose(self.endofunctor),
          object = self.object.value)
    elif self.object.__class__ == basic.Exists:
      return Path(endofunctor = Exists(variables = self.object.variables).compose(self.endofunctor),
          object = self.object.value)
  def advanceLeft(self):
    return self.advanceToSide(left)
  def advanceRight(self):
    return self.advanceToSide(right)
  def advanceToSide(self, side):
    object = _getSide(side, self.object)
    other = _getSide(_swapSide(side), self.object)
    if self.object.__class__ == basic.And:
      return Path(endofunctor = And(side = side, other = other), object = object)
    else:
      assert(self.object.__class__ == basic.Or)
      return Path(endofunctor = Or(side = side, other = other), object = object)

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

class Exists(Endofunctor):
  def __init__(self, variables):
    self.variables = variables
  def variables(self):
    return self.variables
  def onObject(self, object):
    return basic.Exists(variables = self.variables, value = object)
  def onArrow(self, arrow):
    return basic.OnBody(variables = self.variables, arrow = arrow)
  def negations(self):
    return 0

class Always(Endofunctor):
  def variables(self):
    return []
  def onObject(self, object):
    return basic.Always(object)
  def onArrow(self, arrow):
    return basic.OnAlways(arrow)
  def negations(self):
    return 0

always_endofunctor = Always()

class Not(Endofunctor):
  def variables(self):
    return []
  def onObject(self, object):
    return basic.Not(object)
  def onArrow(self, arrow):
    return basic.OnNot(arrow)
  def negations(self):
    return 1

not_endofunctor = Not()

class Id(Endofunctor):
  def variables(self):
    return []
  def pop(self):
    raise Exception("Can't pop the identity endofunctor.")
  def onObject(self, object):
    return object
  def onArrow(self, arrow):
    return arrow
  def negations(self):
    return 0

identity_endofunctor = Id()

class Composite(Endofunctor):
  # if right is covariant, self will represent (left o right)
  # otherwise secod is contravariant, and self will represent (oppositeFunctor(left) o right)
  def __init__(self, left, right):
    self.left = left
    self.right = right

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
    return self.right.onArrow(self.left.onArrow(object))
  def negations(self):
    return self.left.negations() + self.right.negations()

class Conjunction(Endofunctor):
  def __init__(self, side, other):
    self.side = side
    self.other = other

  def variables(self):
    return []
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

