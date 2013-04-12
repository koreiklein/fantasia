# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import enriched
from lib import natural

import importables
import about

arrow = natural.alwaysPreludeArrow.forwardFollow(lambda x:
    x.forwardSingleton(enriched.andType).forwardFollow(lambda x:
      x.forwardAssociateOut(0, 0)))
arrow = arrow.forwardFollow(lambda x:
    importables.beginImportingOnIthFollow(x, 0, lambda x:
      importables.finishImporting(x,
        about.about([natural.zero], 0)))).forwardFollow(lambda x:
            x.forwardHeavyClean())

arrow = arrow.forwardFollow(lambda x:
    importables.beginImportingOnIthFollow(x, 0, lambda q:
      importables.continueImportingOnBodyFollow(q, lambda x:
        importables.finishImporting(x,
          about.about([q.variables()[0]], 0))))).forwardFollow(lambda x:
            x.forwardHeavyClean())


