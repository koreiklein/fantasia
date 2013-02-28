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

sRep = utils.repAnd(
    [starting_claimRep, natural.exists_fiveRep])

def test():
  tProgramTransformation = curry_howard(t.translate())
  ending_claimRep = tProgramTransformation(sRep)

  print "ending claim is:"
  print ending_claimRep
