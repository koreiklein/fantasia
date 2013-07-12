# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from ui.stack import stack

blank = ' '

def extend(xs, i):
  assert(len(xs) <= i)
  copy = []
  m = 0
  if len(xs) > 0:
    m = len(xs[0])
  for e in range(len(xs), i):
    copy.append(blank * m)
  copy.extend(xs)
  return copy

class TextBackend(stack.Backend):
  def __init__(self, strings):
    self.strings = strings
    assert(len(strings) <= 2)
    if len(strings) > 0:
      m = len(strings[0])
      for s in strings:
        assert(m == len(s))

  def stacks(self):
    return True

  def stack(self, dimension, other):
    if dimension == 0:
      length = max(len(self.strings), len(other.strings))
      self_strings = extend(self.strings, length)
      other_strings = extend(other.strings, length)
      for i in range(length):
        self_strings[i] += other_strings[i]
      return TextBackend(self_strings)
    else:
      assert(dimension == 1)
      l = []
      l.extend(other.strings)
      l.extend(self.strings)
      return TextBackend(l)

  def below(self, other):
    strings = list(other.strings)
    for i in range(len(self.strings)):
      string = self.strings[i]
      if i >= len(strings):
        strings.append(string)
      else:
        other_string = strings[i]
        if len(string) >= len(other_string):
          strings[i] = string
        else:
          strings[i] = string + other_string[len(string):]
    return TextBackend(strings)

  # return: a new backend object in which self is draw transposed
  def flip(self):
    raise Exception("Abstract superclass.")

  # offset: a list of coordinates, meant to serve as a translation of other.
  # return: a new backend object like self, but shifted by offset.
  def shift(self, offset):
    assert(len(offset) == 2 or offset[2] == 0)
    strings = [blank * offset[0] + s for s in self.strings]
    m = 0
    if len(strings) > 0:
      m = len(strings[0])
    for i in range(offset[1]):
      strings.append(blank * m)
    return TextBackend(strings)

  def __repr__(self):
    return '\n'.join(self.strings)

