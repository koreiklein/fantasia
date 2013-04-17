# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from ui.run.glimmediate import static
from lib import natural, equivalence
from examples import SS

import profile

from sys import setrecursionlimit

#from examples.easy_induction import arrow as arrow

setrecursionlimit(500000)

#silly.test()
#static.run(arrow.tgt())

#easy_induction.test()
#x = [arrow.values()[0].src()]
#x.extend([t.tgt() for t in arrow.compress().values()])
#slideshow.run(x)

#static.run(SS.proof)
static.run(natural.lib.beginProof().translate())

#static.run(natural.preludeFormula)
#x = [t.src() for t in natural_arrow.values()]
#x.append(natural_arrow.values()[-1].tgt())
#static.run(x[-1])

#static.run(natural_example.arrow.tgt())
#two.test()
