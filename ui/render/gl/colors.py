# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from OpenGL.GL import *

from ui.stack.color import Color

genericColor = Color(r = 0.0, g = 0.0, b = 0.0)

variableColor = Color(r = 0.0, g = 0.0, b = 0.0)
symbolColor = Color(r = 0.0, g = 0.0, b = 0.0)

andColor = Color(r = 0.0, g = 0.0, b = 1.0)
orColor = Color(r = 0.68, g = 0.09, b = 0.63)

callColor = Color(r = 1.0, g = 0.0, b = 0.0)

quantifierDividerColor = Color(r = 0.5, g = 0.5, b = 0.3)
notColor = Color(r = 0.0, g = 0.0, b = 0.0, a = 1.0)

alwaysBackgroundColor = Color(r = 0.0, g = 1.0, b = 1.0, a = 1.0)
maybeBackgroundColor = Color(r = 1.0, g = 0.5, b = 0.0, a = 1.0)

relationColor = Color(r = 0.0, g = 0.0, b = 0.0, a = 1.0)

iffColor = Color(r = 1.0, g = 1.0, b = 1.0, a = 1.0)
applyColor = Color(r = 0.0, g = 0.0, b = 0.0, a = 1.0)
hiddenColor = Color(r = 0.0, g = 0.0, b = 0.0, a = 1.0)

symbolVariablePairBorderColor = Color(r = 0.0, g = 0.0, b = 0.0, a = 1.0)

injectionSymbolBackgroundColor = Color(r = 0.4, g = 0.4, b = 0.7, a = 1.0)
injectionVariableBackgroundColor = Color(r = 0.2, g = 0.2, b = 0.9, a = 1.0)

projectionSymbolBackgroundColor = Color(r = 0.4, g = 0.4, b = 0.7, a = 1.0)
projectionVariableBackgroundColor = Color(r = 0.2, g = 0.2, b = 0.9, a = 1.0)

callSymbolBackgroundColor = Color(r = 0.4, g = 0.4, b = 0.7, a = 1.0)
callVariableBackgroundColor = Color(r = 0.2, g = 0.2, b = 0.9, a = 1.0)

_colorPairs = [ ( Color(r = 1.0, g = 0.3, b = 0.3, a = 1.0)
                , Color(r = 0.8, g = 0.5, b = 0.5, a = 1.0))

              , ( Color(r = 0.3, g = 1.0, b = 0.3, a = 1.0)
                , Color(r = 0.5, g = 0.8, b = 0.5, a = 1.0))

              , ( Color(r = 0.3, g = 0.3, b = 1.0, a = 1.0)
                , Color(r = 0.5, g = 0.5, b = 0.8, a = 1.0))
              ]

def productPairsColor(i):
  return _colorPairs[i % len(_colorPairs)]

def exponentialColor(isAlways):
  if isAlways:
    return alwaysBackgroundColor
  else:
    return maybeBackgroundColor

projectDotColor = Color(r = 0.0, g = 0.0, b = 0.0)
injectDotColor = Color(r = 0.5, g = 0.5, b = 0.5)

trueColor = Color(r = 0.0, g = 0.0, b = 0.0)
falseColor = Color(r = 0.0, g = 0.0, b = 0.0)
