# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from examples import natural as natural_example
from examples.easy_induction import transition #, ending_claim as claim
from examples.two import transition as natural_transition
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
x = [t.src() for t in natural_transition.values()]
x.append(natural_transition.values()[-1].tgt())
static.run(x[-1])
