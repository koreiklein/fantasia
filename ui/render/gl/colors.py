# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

# Colors for gl rendering of enriched are collected here.
from OpenGL.GL import *

from ui.stack.color import Color
from calculus import enriched
from calculus.basic import andType, orType

trueDividerColor = Color(r = 0.0, g = 0.0, b = 0.0)
falseDividerColor = Color(r = 0.0, g = 0.0, b = 0.0)

# Prefer choosing the colors of dividers based on the underlying basic type.
chooseColorsByConcreteness = False

concreteDividerColor = Color(r = 0.0, g = 0.0, b = 1.0)
demorganedDividerColor = Color(r = 0.68, g = 0.09, b = 0.63)

andBasedDividerColor = Color(r = 0.0, g = 0.0, b = 1.0)
orBasedDividerColor = Color(r = 0.68, g = 0.09, b = 0.63)

quantifierDividerColor = Color(r = 0.5, g = 0.5, b = 0.5)
alwaysBackgroundColor = Color(r = 0.0, g = 1.0, b = 1.0, a = 0.2)
maybeBackgroundColor = Color(r = 1.0, g = 0.5, b = 0.0, a = 0.8)
notColor = Color(r = 0.0, g = 0.0, b = 0.0, a = 0.8)

textColor = Color(r = 0.2, g = 0.2, b = 0.2, a= 1.0)
variableColor = Color(r = 0.2, g = 0.5, b = 0.2, a= 1.0)

def colorOfConjType(type):
  if chooseColorsByConcreteness:
    if type in enriched.concreteConjTypes:
      return concreteDividerColor
    else:
      assert(type in enriched.demorganedConjTypes)
      return demorganedDividerColor
  else:
    basicType = enriched.correspondingConcreteBasicType(type)
    if basicType == andType:
      return andBasedDividerColor
    else:
      assert(basicType == orType)
      return orBasedDividerColor

def colorOfUnitType(type):
  if type in [enriched.andType, enriched.withType]:
    return trueDividerColor
  else:
    assert(type in [enriched.orType, enriched.parType])
    return falseDividerColor


# always: a boolean.  True for always, False for maybe.
# return: the background color associated with the exponential.
def exponentialColor(always):
  if always:
    return alwaysBackgroundColor
  else:
    return maybeBackgroundColor

