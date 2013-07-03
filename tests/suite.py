# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import unittest
from tests import test_basic_bifunctor, test_basic_endofunctor

def suite():
  testSuite = unittest.TestSuite(( test_basic_bifunctor.suite()
                                 , test_basic_endofunctor.suite()))
  return testSuite
