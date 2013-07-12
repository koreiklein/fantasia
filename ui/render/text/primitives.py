# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from ui.stack import stack
from ui.stack.text import TextBackend
from ui.render.text import colors, distances

def newTextStack(color, s):
  return stack.Stack([len(s), 1], TextBackend([s]))

dot = newTextStack(None, '.')

def solidSquare(color, widths):
  return stack.Stack(widths, TextBackend([' ' * widths[1] for i in range(widths[0])]))

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
  return (lambda length:
    divider(colors.andColor, _dual_dimension(_dimension_for_variance(covariant)),
        length, distances.conjunctiveDividerWidth))

def orDivider(covariant):
  return (lambda length:
    divider(colors.orColor, _dimension_for_variance(covariant),
        length, distances.conjunctiveDividerWidth))

def quantifierDivider(covariant, length):
  return divider(colors.quantifierDividerColor, _dimension_for_variance(covariant),
      length, distances.quantifier_divider_width)

def divider(color, dimension, length, width):
  assert(width == 1)
  if dimension == 0:
    return newTextStack(color, '-' * length)
  else:
    assert(dimension == 1)
    return stack.Stack([width, length],
        TextBackend(['|' for i in range(length)]))
