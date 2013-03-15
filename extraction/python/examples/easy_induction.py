# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from extraction.python.arrows import curry_howard
from extraction.python import utils
from extraction.python.lib import natural

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
  tRep = curry_howard(t.translate())
  eRep = tRep(sRep)

  print "ending claim is represented by:"
  print eRep
