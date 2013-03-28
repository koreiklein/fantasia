# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from extraction.python.arrows import curry_howard
from extraction.python.lib.natural import startingFormulaRep
from examples.two import arrow

def test():
  compressedT = arrow.compress().translate().compress()
  #print >>open('arrow.txt', 'w'), compressedT
  program_transformation = curry_howard(compressedT)
  finalRep = program_transformation(startingFormulaRep)

  print "final claim is represented by:"
  print finalRep
