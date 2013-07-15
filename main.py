# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from ui.run.text import static
from lib import natural, equivalence, common_vars
from examples import QR
from calculus import variable
from calculus.enriched.constructors import *
from calculus.enriched.formula import RenderingContext

import profile

from sys import setrecursionlimit

#from examples.easy_induction import arrow as arrow

setrecursionlimit(50000000)


#static.run(natural.lib.beginProof())
static.run(QR.proof)
