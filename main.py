# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from examples.easy_induction import transition #, ending_claim as claim
from extraction.python.examples import easy_induction, silly
from ui.run.glimmediate import slideshow, static

import profile

from sys import setrecursionlimit

from examples.easy_induction import transition as transition

setrecursionlimit(500000)

#silly.test()
#static.run(transition.tgt())

easy_induction.test()

#x = [transition.values()[0].src()]
#x.extend([t.tgt() for t in transition.values()])
#slideshow.run(x)
