# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from examples import natural as natural_example
from examples.easy_induction import arrow #, ending_claim as claim
from examples.two import arrow as natural_arrow
from extraction.python.examples import easy_induction, silly
from ui.run.glimmediate import slideshow, static
from lib import natural

import profile

from sys import setrecursionlimit

from examples.easy_induction import arrow as arrow

setrecursionlimit(500000)

#silly.test()
#static.run(arrow.tgt())

easy_induction.test()
x = [arrow.values()[0].src()]
x.extend([t.tgt() for t in arrow.compress().values()])
slideshow.run(x)



#static.run(natural.preludeFormula)
#x = [t.src() for t in natural_arrow.values()]
#x.append(natural_arrow.values()[-1].tgt())
#static.run(x[-1])

#static.run(natural_example.arrow.tgt())
#two.test()
