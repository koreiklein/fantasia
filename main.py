# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from examples.easy_induction import transition #, ending_claim as claim
from examples.natural_examples import transition as natural_transition
from extraction.python.examples import easy_induction, silly
from ui.run.glimmediate import slideshow, static
from lib import natural

import profile

from sys import setrecursionlimit

from examples.easy_induction import transition as transition

setrecursionlimit(500000)

#silly.test()
#static.run(transition.tgt())

#easy_induction.test()

#x = [transition.values()[0].src()]
#x.extend([t.tgt() for t in transition.compress().values()])
#slideshow.run(x)

#static.run(natural.preludeFormula)
static.run(natural_transition.tgt())
