# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol


leftSymbol = symbol.StringSymbol('left', type = symbol.projection)
rightSymbol = symbol.StringSymbol('right', type = symbol.projection)

relationSymbol = symbol.StringSymbol('=', infix = (leftSymbol, rightSymbol), type = symbol.projection)
domainSymbol = symbol.StringSymbol('\'', type = symbol.projection)

srcSymbol = symbol.StringSymbol('src', type = symbol.projection)
tgtSymbol = symbol.StringSymbol('tgt', type = symbol.projection)
functionPairsSymbol = symbol.StringSymbol('\'', symbol.projection)

inputSymbol = symbol.StringSymbol('input', type = symbol.projection)
outputSymbol = symbol.StringSymbol('output', type = symbol.projection)

