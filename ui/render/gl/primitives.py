# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from OpenGL.GL import *

from calculus import enriched, limit
from ui.render.gl import colors, distances

from ui.stack.gl import newGLStack
from ui.stack.point import Point

def stackingDimensionOfConjType(type):
  if type in [enriched.andType, enriched.withType]:
    return 0
  else:
    assert(type in [enriched.orType, enriched.parType])
    return 1

def stackingDimensionOfQuanifierType(type):
  if type == enriched.forallType:
    return 1
  else:
    assert(type == enriched.existsType)
    return 0

def stackingDimensionForLimit(limit):
  if limit.type() == limit.limitType:
    return 0
  else:
    assert(limit.type() == limit.colimitType)
    return 1

def transposeDimension(dimension):
  if dimension == 0:
    return 1
  else:
    assert(dimension == 1)
    return 0

# Typical backgrounds will be some pleasant unassuming color.
# Like, say, off white.

# Unit divider (2 Kinds)
  # enriched makes it appear as though there are 4 units. 2 of them, however, can be converted
  # into the other two.  We will burden the author of this code with keeping track of
  # the conversion in order to present the user with a mental model that involves only
  # two units.
# Conj divider (4 Kinds) | (Vertical, Horizontal) X (Blue, Yellow)
# Quantifier divider (2 Kinds)
  # Dotted lines, as quantifiers are really unimportant and should be downplayed as much as possible.
# Exponential background (2 Kinds)
  # ? Light Blue for Always  (Good, light blue is a normal, unassuming, boring color)
  # ? Orange for Maybe       (Good, the Maybe combinator is INSANE and deserves to stand out)

# return: a gl stack representing the unit for the given enriched conj type.
#
#   e===================================d
#  /                                     \
# f                                       c
#  \                                     /
#   a===================================b
#
def unitDivider(type, length):
  return divider(
      color = colors.colorOfUnitType(type),
      dimension = stackingDimensionOfConjType(type),
      length = length,
      width = distances.widthOfDividerByLength(length),
      capLength = distances.capLengthOfDividerByLength(length))

# return: a gl stack representing the conj divider for the given enriched conj type.
def conjDivider(type, length):
  return divider(
      color = colors.colorOfConjType(type),
      dimension = stackingDimensionOfConjType(type),
      length = length,
      width = distances.widthOfDividerByLength(length),
      capLength = distances.capLengthOfDividerByLength(length))

def divider(color, dimension, length, width, capLength):
  widths = [0 for i in range(3)]
  tDimension = transposeDimension(dimension)
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

# return: a gl stack representing the quantifier divider for the given enriched quantifier type.
def quantifierDivider(type, length):
  return divider(
      color = colors.quantifierDividerColor,
      dimension = stackingDimensionOfQuanifierType(type),
      length = length,
      width = distances.widthOfQuantifierDividerByLength(length),
      capLength = distances.capLengthOfDividerByLength(length))

def colorForLimitLine(usedAsType):
  if usedAsType:
    return colors.limitLineColorForType
  else:
    return colors.limitLineColor

def limitLine(longDimension, length, usedAsType):
  widths = [distances.limitLineThickness, distances.limitLineThickness, 0.0]
  widths[longDimension] = length
  return solidSquare(colorForLimitLine(usedAsType), widths)

def limitClauseStart(stackingDimension):
  widths = [0.0, 0.0, 0.0]
  widths[stackingDimension] = distances.limitClausesOffset
  return solidSquare(colors.limitLineColor, widths)

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

def notSymbol(widths):
  upper = [distances.notThickness, widths[1], 0.0]
  lower = [widths[0], distances.notThickness, 0.0]
  return solidSquare(colors.notColor, upper).below(solidSquare(colors.notColor, lower))

def holdsStack(distance):
  widths = [distance, distances.holdsStackHeight, 0.0]
  return solidSquare(colors.holdsColor, widths)
