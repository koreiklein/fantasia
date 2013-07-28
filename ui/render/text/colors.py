# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

genericColor = None

variableColor = None
symbolColor = None

andColor = None
orColor = None

callColor = None

quantifierDividerColor = None
notColor = None

alwaysBackgroundColor = None
maybeBackgroundColor = None

relationColor = None

iffColor = None
applyColor = None
hiddenColor = None

symbolVariablePairBorderColor = None

injectionSymbolBackgroundColor = None
injectionVariableBackgroundColor = None

projectionSymbolBackgroundColor = None
projectionVariableBackgroundColor = None

callSymbolBackgroundColor = None
callVariableBackgroundColor = None

_colorPairs = [ (None
                ,None)

              , (None
                ,None)

              , (None
                ,None)
              ]

def productPairsColor(i):
  return _colorPairs[i % len(_colorPairs)]

symbolBackgroundColor = None
symbolForegroundColor = None

def exponentialColor(isAlways):
  if isAlways:
    return alwaysBackgroundColor
  else:
    return maybeBackgroundColor

projectDotColor = None
injectDotColor = None

trueColor = None
falseColor = None
