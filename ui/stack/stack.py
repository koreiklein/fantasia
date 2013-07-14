# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>


class Backend:
  # other: another Backend object
  # return: a new backend object in which self is draw with other drawn on top.
  def below(self, other):
    raise Exception("Abstract superclass.")

  # return: a new backend object in which self is draw transposed
  def flip(self):
    raise Exception("Abstract superclass.")

  # offset: a list of coordinates, meant to serve as a translation of other.
  # return: a new backend object like self, but shifted by offset.
  def shift(self, offset):
    raise Exception("Abstract superclass.")

  @staticmethod
  def null():
    raise Exception("Abstract superclass.")

  def stacks(self):
    return False

  def uses_epsilon(self):
    return True

def stackAll(dimension, xs, spacing = 0):
  assert(len(xs) > 0)
  res = xs[0]
  for x in xs[1:]:
    res = res.stack(dimension, x, spacing = spacing)
  return res

def stackAllX(xs):
  return stackAll(0, xs)
def stackAllY(xs):
  return stackAll(0, xs)
def stackAllZ(xs):
  return stackAll(0, xs)
def stackAllT(xs):
  return stackAll(0, xs)

class Stack:
  def __init__(self, coords, backend):
    self._coords = coords
    self._backend = backend

  def uses_epsilon(self):
    return self._backend.uses_epsilon()

  def flip(self):
    coords = list(self.coords)
    tmp = coords[0]
    coords[0] = coords[1]
    coords[1] = tmp
    return Stack(coords, self.backend.flip())

  # Return widths.
  def widths(self):
    return self._coords

  # Get the number of dimensions.
  def dimension(self):
    return len(self._coords)

  def shift(self, offset):
    assert(self.dimension() == len(offset))
    return Stack([self.widths()[i] + offset[i] for i in range(self.dimension())],
        self._backend.shift(offset))
  # Return a new stack in which self is drawn before other with other shifted by offset.
  def below(self, other):
    assert(self.dimension() == other.dimension())
    return Stack([max(self.widths()[i], other.widths()[i]) for i in range(self.dimension())],
        self._backend.below(other._backend))

  def atLeast(self, widths):
    return Stack([max(self.widths()[i], widths[i]) for i in range(self.dimension())],
        self._backend)

  # Return a new stack with other drawn just dimension of self.
  def stack(self, dimension, other, spacing = 0):
    if self._backend.stacks():
      offset = [0 for i in range(self.dimension())]
      offset[dimension] = spacing
      coords = list(self._coords)
      for i in range(len(coords)):
        if i == dimension:
          coords[i] += spacing + other._coords[i]
        else:
          coords[i] = max(coords[i], other._coords[i])
      return Stack(coords, self._backend.stack(dimension, other._backend.shift(offset)))
    else:
      offset = [0 for i in range(self.dimension())]
      offset[dimension] = self.widths()[dimension] + spacing
      return self.below(other.shift(offset))

  def stackCentered(self, dimension, other, spacing = 0):
    assert(self.dimension() == other.dimension())
    offsetSelf = [0 for i in range(self.dimension())]
    offsetOther = [0 for i in range(self.dimension())]
    for i in range(self.dimension()):
      if i != dimension:
        m = max(self.widths()[i], other.widths()[i])
        offsetSelf[i] = (m - self.widths()[i]) / 2
        offsetOther[i] = (m - other.widths()[i]) / 2
      else:
        assert(i == dimension)
        offsetOther[i] = self.widths()[i] + spacing
    return self.shift(offsetSelf).below(other.shift(offsetOther))

  def stackx(self, other):
    return self.stack(0, other)
  def stacky(self, other):
    return self.stack(1, other)
  def stackz(self, other):
    return self.stack(2, other)
  def stackt(self, other):
    return self.stack(2, other)

