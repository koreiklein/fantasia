# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from ui.stack import stack
from ui.stack.text import TextBackend
from ui.render.text import colors, distances

def newTextStack(color, s):
  return stack.Stack([len(s), 1], TextBackend([s]))

dot = newTextStack(None, '.')

nullStack = newTextStack(None, '')

def holds():
  return newTextStack(None, ':')

negationStack = newTextStack(None, "~")

def surroundWithNot(s):
  return negationStack.stack(0, s)

def solidSquare(color, widths):
  return stack.Stack(widths, TextBackend([' ' * widths[1] for i in range(widths[0])]))

def identical(covariant):
  if covariant:
    s = ' == '
  else:
    s = ' != '
  return newTextStack(None, s)

def _dimension_for_variance(covariant):
  if covariant:
    return 0
  else:
    return 1

def _dual_dimension(dimension):
  if dimension == 0:
    return 1
  else:
    assert(dimension == 1)
    return 0

def andDivider(covariant):
  def f(length):
    r = divider(colors.andColor, _dual_dimension(_dimension_for_variance(covariant)),
        length, distances.conjunctiveDividerWidth)
    if not covariant:
      r = newTextStack(None, '|').stack(0, r).stack(0, newTextStack(None, '|'))
    return r
  return f

def orDivider(covariant):
  def f(length):
    r = divider(colors.orColor, _dimension_for_variance(covariant),
        length, distances.conjunctiveDividerWidth)
    if not covariant:
      r = newTextStack(None, '-').stack(1, r).stack(1, newTextStack(None, '-'))
    return r
  return r

def quantifierDivider(covariant, length):
  return divider(colors.quantifierDividerColor, _dimension_for_variance(not covariant),
      length, distances.quantifier_divider_width,
      special_character = '.')

def divider(color, dimension, length, width, special_character = None):
  assert(width == 1)
  if dimension == 0:
    return newTextStack(color, ('-' if special_character is None else special_character) * length)
  else:
    assert(dimension == 1)
    return stack.Stack([width, length],
        TextBackend([('|' if special_character is None else special_character) for i in range(length)]))

