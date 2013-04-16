# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from OpenGL.GL import *

from ui.render.gl import colors, distances

from ui.stack.gl import newGLStack
from ui.stack.point import Point

def _dual_dimension(dimension):
  if dimension == 0:
    return 1
  else:
    assert(dimension == 1)
    return 0


# always: a boolean, True for always, false for Maybe.
# widths: a list of the widths of the box.
# return: a gl stack representing the background for an exponential.
#
# c----------------b
# |                |
# d----------------a
#
def exponentialBox(always, widths):
  return solidSquare(colors.exponentialColor(always), widths)

def empty():
  return newGLStack([0.0, 0.0, 0.0], lambda: None)

def solidSquare(color, widths):
  d = Point(0.0, 0.0, 0.0)
  a = d.translate(0, widths[0])
  c = d.translate(1, widths[1])
  b = a.translate(1, widths[1])
  def render():
    color.render()
    glBegin(GL_TRIANGLE_FAN)
    for point in [a, b, c, d]:
      point.render()
    glEnd()
  return newGLStack(widths, render)

def divider(color, dimension, length, width, capLength):
  widths = [0 for i in range(3)]
  tDimension = _dual_dimension(dimension)
  widths[dimension] = width
  widths[tDimension] = length
  z = Point(0.0, 0.0)
  a = z.translate(tDimension, capLength)
  b = a.translate(tDimension, length - 2 * capLength)
  e = a.translate(dimension, width)
  d = b.translate(dimension, width)
  f = z.translate(dimension, width / 2.0)
  c = f.translate(tDimension, length)
  def render():
    color.render()
    glBegin(GL_TRIANGLE_FAN)
    for point in [a, b, c, d, e, f]:
      point.render()
    glEnd()
  return newGLStack(widths, render)

def _dimension_for_variance(covariant):
  if covariant:
    return 0
  else:
    return 1


def intersectDivider(covariant):
  return (lambda length:
    divider(colors.intersectColor, _dimension_for_variance(covariant),
        max(length, distances.min_intersect_divider_length),
        distances.conjunctiveDividerWidth,
        distances.capLengthOfDividerByLength(length)))

def andDivider(covariant):
  return (lambda length:
    divider(colors.andColor, _dimension_for_variance(covariant),
        length, distances.conjunctiveDividerWidth,
        distances.capLengthOfDividerByLength(length)))

def orDivider(covariant):
  return (lambda length:
    divider(colors.orColor, _dimension_for_variance(covariant),
        length, distances.conjunctiveDividerWidth,
        distances.capLengthOfDividerByLength(length)))

def quantifierDivider(covariant, length):
  return divider(colors.quantifierDividerColor, _dimension_for_variance(covariant),
      length, distances.quantifier_divider_width,
      distances.capLengthOfDividerByLength(length))

def trueDivider(length):
  return divider(colors.trueColor, 0, length, distances.unit_width,
      distances.capLengthOfDividerByLength(length))

def falseDivider(length):
  return divider(colors.falseColor, 1, length, distances.unit_width,
      distances.capLengthOfDividerByLength(length))

projectDot = solidSquare(colors.projectDotColor,
    [distances.dotWidth, distances.dotWidth, 0.0])
injectDot = solidSquare(colors.injectDotColor,
    [distances.dotWidth, distances.dotWidth, 0.0])

def notSymbol(widths):
  upper = [distances.notThickness, widths[1], 0.0]
  lower = [widths[0], distances.notThickness, 0.0]
  return solidSquare(colors.notColor, upper).below(solidSquare(colors.notColor, lower))


