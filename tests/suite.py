# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import unittest
from tests import test_basic_bifunctor, test_basic_endofunctor, test_enriched_functors, test_path

def suite():
  testSuite = unittest.TestSuite(( test_basic_bifunctor.suite()
                                 , test_basic_endofunctor.suite()
                                 , test_enriched_functors.suite()
                                 , test_path.suite()))
  return testSuite

def run():
  runner = unittest.TextTestRunner()
  runner.run(suite())

