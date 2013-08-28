# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from misc import *
from calculus.enriched import formula, endofunctor, constructors
from calculus.basic import bifunctor as basicBifunctor, endofunctor as basicEndofunctor

UntransportableException = basicBifunctor.UntransportableException

class Bifunctor:
  def translate(self):
    raise Exception("Abstract superclass.")
  def variables(self):
    raise Exception("Abstract superclass.")
  def onObjects(self, left, right):
    raise Exception("Abstract superclass.")

  def right_covariant(self):
    raise Exception("Abstract superclass.")
  def left_covariant(self):
    raise Exception("Abstract superclass.")
  def right_onObject(self, x):
    raise Exception("Abstract superclass.")

  # return a function representing a natural transform: F(B, .) --> F(B, And([B, .]))
  def transport_duplicating(self, B):
    nt = self.translate().transport_duplicating(B.translate())
    return (lambda x:
        formula.Arrow(src = self.onObjects(left = B, right = x),
          tgt = self.onObjects(left = B, right = constructors.And([B.updateVariables(), x])),
          basicArrow = nt(x.translate())))

  def onArrows(self, left, right):
    return formula.Arrow(src = self.onObjects(left.src, right.src),
        tgt = self.onObjects(left.tgt, right.tgt),
        basicArrow = self.translate().onArrows(left.translate(), right.translate()))

  def precompose(self, left, right):
    return PrecompositeBifunctor(bifunctor = self, left = left, right = right)
  def compose(self, other):
    return PostcompositeBifunctor(bifunctor = self, functor = other)
  def precomposeLeft(self, left):
    return self.precompose(left = left, right = endofunctor.identity_functor)
  def precomposeRight(self, right):
    return self.precompose(left = endofunctor.identity_functor, right = right)


class PostcompositeBifunctor(Bifunctor):
  def __init__(self, bifunctor, functor):
    self.bifunctor = bifunctor
    self.functor = functor

  def right_covariant(self):
    return self.functor.covariant() ^ self.bifunctor.right_covariant()

  def left_covariant(self):
    return self.functor.covariant() ^ self.bifunctor.left_covariant()

  def right_onObject(self, x):
    return self.bifunctor.right_onObject(x).compose(self.functor)

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

  def right_covariant(self):
    return self.right.covariant() ^ self.bifunctor.right_covariant()

  def left_covariant(self):
    return self.left.covariant() ^ self.bifunctor.left_covariant()

  def right_onObject(self, x):
    return self.left.compose(self.bifunctor.right_onObject(self.right.onObject(x)))

  def __repr__(self):
    return "%s x %s . %s"%(self.left, self.right, self.bifunctor)

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

class Conjunction(Bifunctor):
  # rightIndex is an index into the list formed after inserting at leftIndex
  # e.g. Conjunction([a, b, c], 1, 1).onObjects(x, y) -> [a, x, b, c] -> [a, y, x, b, c]
  # e.g. Conjunction([a, b, c], 1, 2).onObjects(x, y) -> [a, x, b, c] -> [a, x, y, b, c]
  # e.g. Conjunction([a, b, c], 1, 0).onObjects(x, y) -> [a, x, b, c] -> [y, a, x, b, c]
  def __init__(self, values, leftIndex, rightIndex):
    self.values = values
    self.leftIndex = leftIndex
    self.rightIndex = rightIndex

  def right_covariant(self):
    return True

  def left_covariant(self):
    return True

  def right_onObject(self, x):
    values = list(self.values)
    if self.rightIndex <= self.leftIndex:
      # the right comes first
      index = self.leftIndex + 1
      values.insert(self.rightIndex, x)
    else:
      # the left comes first
      index = self.leftIndex
      values.insert(self.rightIndex - 1, x)
    return self.enrichedEndofunctor()(values = values, index = index)

  def __repr__(self):
    values = [repr(value) for value in self.values]
    values.insert(self.leftIndex, " . ")
    values.insert(self.rightIndex, " . ")
    return self.name() + " [ " + ', '.join(values) + ' ]'

  def translate(self):
    lesserIndex = min(self.leftIndex, self.rightIndex)
    greaterIndex = max(self.leftIndex, self.rightIndex)
    # begin, (lesser), middle, (greater), end
    begin = self.values[:lesserIndex]
    m = greaterIndex
    if self.leftIndex < self.rightIndex:
      m -= 1
    middle = self.values[lesserIndex:m]
    end = self.values[m:]
    if len(end) > 0:
      result = self.basicEndofunctor()(side = left,
          other = self.multiOp()(end).translate())
    else:
      result = basicEndofunctor.identity_functor
    for value in middle[::-1]:
      result = result.compose(self.basicEndofunctor()(side = right,
        other = value.translate()))
    result = self.basicBifunctor().precomposeRight(result)
    for value in begin[::-1]:
      result = result.compose(self.basicEndofunctor()(side = right,
        other = value.translate()))
    if self.leftIndex < self.rightIndex:
      return result
    else:
      return result.commute()

  def variables(self):
    return []
  def onObjects(self, left, right):
    values = list(self.values)
    values.insert(self.leftIndex, left)
    values.insert(self.rightIndex, right)
    return self.multiOp()(values)

class And(Conjunction):
  def name(self):
    return 'AND'
  def basicEndofunctor(self):
    return basicEndofunctor.And
  def enrichedEndofunctor(self):
    return endofunctor.And
  def basicBifunctor(self):
    return basicBifunctor.and_functor
  def multiOp(self):
    return formula.And

class Or(Conjunction):
  def name(self):
    return 'OR'
  def basicEndofunctor(self):
    return basicEndofunctor.Or
  def enrichedEndofunctor(self):
    return endofunctor.Or
  def basicBifunctor(self):
    return basicBifunctor.or_functor
  def multiOp(self):
    return formula.Or
