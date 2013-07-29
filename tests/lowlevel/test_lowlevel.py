# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import unittest

from tests.lowlevel import test_basic_bifunctor, test_basic_endofunctor
from tests.lowlevel import test_enriched_functors, test_path

def suite():
  return unittest.TestSuite([ test_basic_bifunctor.suite()
                            , test_basic_endofunctor.suite()
                            , test_enriched_functors.suite()
                            , test_path.suite()])
