# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from ui.stack import stack

blank = ' '

def vextend(xs, i):
  assert(len(xs) <= i)
  copy = []
  m = 0
  if len(xs) > 0:
    m = len(xs[0])
  for e in range(len(xs), i):
    copy.append(blank * m)
  copy.extend(xs)
  return copy

def hextend(xs, i):
  if len(xs) > 0:
    assert(len(xs[0]) <= i)
  result = []
  for x in xs:
    result.append(x + blank * (i - len(x)))
  return result

class TextBackend(stack.Backend):
  def __init__(self, strings):
    self.strings = strings
    if len(strings) > 0:
      m = len(strings[0])
      for s in strings:
        assert(m == len(s))

  def stacks(self):
    return True

  def uses_epsilon(self):
    return False

  def stack(self, dimension, other):
    if dimension == 0:
      length = max(len(self.strings), len(other.strings))
      self_strings = vextend(self.strings, length)
      other_strings = vextend(other.strings, length)
      for i in range(length):
        self_strings[i] += other_strings[i]
      return TextBackend(self_strings)
    else:
      assert(dimension == 1)
      length = 0
      if len(self.strings) > 0:
        length = len(self.strings[0])
      if len(other.strings) > 0:
        length = max(length, len(other.strings[0]))
      self_strings = hextend(self.strings, length)
      other_strings = hextend(other.strings, length)
      other_strings.extend(self_strings)
      return TextBackend(other_strings)

  def below(self, other):
    length = max(len(self.strings), len(other.strings))
    self_strings = vextend(self.strings, length)
    other_strings = vextend(other.strings, length)

    for i in range(len(self_strings)):
      string = self_strings[i]
      other_string = other_strings[i]
      if len(string) >= len(other_string):
        self_strings[i] = string
      else:
        self_strings[i] = string + other_string[len(string):]
    return TextBackend(self_strings)

  # return: a new backend object in which self is draw transposed
  def flip(self):
    raise Exception("Abstract superclass.")

  # offset: a list of coordinates, meant to serve as a translation of other.
  # return: a new backend object like self, but shifted by offset.
  def shift(self, offset):
    assert(len(offset) == 2 or offset[2] == 0)
    strings = list(self.strings)
    m = 0
    if len(strings) > 0:
      m = len(strings[0])
    for i in range(offset[1]):
      strings.append(blank * m)
    strings = [blank * offset[0] + s for s in self.strings]
    return TextBackend(strings)

  def __repr__(self):
    return '\n'.join(self.strings)

