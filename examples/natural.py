# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from lib import natural

from calculus import enriched
from importables import *
from about import *

natural.preludeArrow.translate()
natural.preludeArrow.translate().tgt().assertEqual(natural.preludeArrow.tgt().translate())
natural.preludeArrow.tgt().forwardAssociateOut(0, 0).translate()

arrow = natural.preludeArrow.forwardFollow(lambda x:
    x.forwardAssociateOut(0, 0))
arrow = arrow.forwardFollow(lambda x:
    beginImportingOnIthFollow(x, 0, lambda x:
      finishImporting(x,
        about([natural.zero], 1))))

arrow.translate()
