# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from extraction.python.arrows import curry_howard
from extraction.python import utils
from extraction.python.lib import oldNatural as natural

from examples.easy_induction import t

starting_claimRep = utils.repAnd(
    [ natural.increasingRep
    , natural.inductionRep
    , natural.successorExistsRep
    , natural.transitivityRep
    , natural.weakeningRep
    , natural.reflexivityRep
    , natural.zero_naturalRep ])

def test():
  # This function performs a program extraction and prints out the resulting program.
  # The extraction is represented by the following commutative diagram:
  #
  # examples.easy_induction.s --examples.easy_induction.t----> examples.easy_induction.e
  #       |                         |                                  |
  #       |                         |                                  |
  #       |                         |                                  |
  #       v                         v                                  v
  #     sRep ---------------------tRep----------------------------->> eRep
  sRep = utils.repAnd([starting_claimRep, natural.exists_fiveRep])
  # With the 03/21/13 implementation, this compression reduces the amount of data associated
  # with t by about a factor of 2.
  compressedT = t.compress().translate().compress()
  print >>open('arrow.txt', 'w'), t.translate().compress()
  tRep = curry_howard(compressedT)
  eRep = tRep(sRep)

  print "ending claim is represented by:"
  print eRep
