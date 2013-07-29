# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import cProfile
import pstats

from tempfile import mkstemp

def profile(pythonString, sortorder = 'cum'):
  outputFile = mkstemp()[1]
  cProfile.run(pythonString, outputFile)
  p = pstats.Stats(outputFile)
  p.strip_dirs().sort_stats(sortorder).print_stats()

if __name__ == '__main__':
  profile('import main')


