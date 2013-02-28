# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from examples.easy_induction import ending_claim as claim
from extraction.python.examples import easy_induction, silly
from ui.run.glimmediate import static as static_gl_image

from sys import setrecursionlimit

setrecursionlimit(500000)

silly.test()
easy_induction.test()

static_gl_image.run(claim)
