# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic
from lib import common_vars
from lib.common_symbols import domainSymbol, relationSymbol, leftSymbol, rightSymbol

# FIXME Remove this whole path class, but first make sure that the insights inherent in this
#       implementation of instantiate are captured elsewhere.
class Path:
  def maybeInstantiate(self, variables):
    if basic.isExistentialOfLength(len(variables), self.object):
      return self.instantiate(variables)
    else:
      return PathArrowList()

  # self must be contravariant.
  # self.object must be a bounded existential of the same length as variables
  # return a list of pairs (B, A) such that B is like self.object.value with substituted variables
  #   and A is a path arrow to self.onObject(B)
  def instantiate(self, variables):
    assert(not self.functor.covariant())
    if len(variables) > 4:
      raise Exception("WARNING: Running instantiate on more than 4 variables may be inefficient.")
    return self.toPathArrowList().forwardFollowWithValues(_perms(variables), lambda perm, path:
        path.instantiate_ordered(perm))

  # like instantiate, but only return instantiations that substitute the variables in order.
  def instantiate_ordered(self, variables):
    path = self
    assert(not path.covariant())
    path_arrow = path.identity()
    for v in variables:
      assert(path_arrow.src == self)
      if path.object.__class__ == basic.Exists:
        path_arrow = path_arrow.forwardFollow(lambda p, v=v:
            p.forwardOnPathFollow(lambda x, v=v:
              x.backwardIntroExists(v)))
        path = path_arrow.tgt
      else:
        return PathArrowList()
    exportArrow = path.exportConjunctively()
    if exportArrow.tgt.bottom().__class__ == basic.Not:
      return path_arrow.forwardCompose(exportArrow).toPathArrowList()
    else:
      return PathArrowList()

def _perms(xs):
  if len(xs) == 0:
    return [[]]
  else:
    return [_functional_insert(ys, i, xs[0])
        for ys in _perms(xs[1:])
        for i in range(len(xs))]

def _functional_insert(l, index, x):
  result = list(l)
  result.insert(index, x)
  return result

def _functional_pop(i, l):
  r = list(l)
  x = r.pop(i)
  return (x, r)

def _functional_pops(l):
  return [_functional_pop(i, l) for i in range(len(l))]

class PathArrowList:
  # arrows: a list of path arrows
  def __init__(self, arrows = []):
    self.arrows = arrows

  def __len__(self):
    return len(self.arrows)
  def __getitem__(self, i):
    return self.arrows[i]
  def __iter__(self):
    return iter(self.arrows)

  # f: takes a tag and a path p and returns a PathArrowList of arrows that start at p.
  # return: <See the below python code.>
  def forwardFollow(self, f):
    return PathArrowList([a.forwardCompose(A)
      for a in self
      for A in f(a.tgt)])

  # f: takes paths to paths.
  def forwardOnTgts(self, f):
    return PathArrowList([A.forwardFollow(f) for A in self])

  # f: takes a pair (value, oldArrow.tgt) to a PathArrowList of arrows composable with oldArrow.tgt
  # return: a list of all arrows formable from applying f to an arrow of self and a value in values.
  def forwardFollowWithValues(self, values, f):
    return PathArrowList([X
      for value in values
      for X in self.forwardFollow(lambda path, value=value: f(value, path))])

  # like forwardFollowWithValues, but as if values were equal to a list of all importable claims.
  # TODO: Consider passing extra arguments that allow for caching or better filtering so as
  #       to improve performance.
  def forwardFollowWithImports(self, f):
    return PathArrowList([A.forwardCompose(B).forwardCompose(C)
      for A in self
      for (b, nt, C) in A.tgt.functor.importFiltered(lambda x, A=A:
        f(x, Path(functor = A.tgt.functor, object = basic.And(x, A.tgt.object))).arrows)
      for B in [Arrow(src = A.tgt, tgt = C.src, arrow = nt(A.tgt.object))] ])

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

