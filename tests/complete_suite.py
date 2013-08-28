# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import unittest
from tests.lowlevel import test_lowlevel
from tests.midlevel import test_midlevel, test_lower_midlevel

def suite():
  return unittest.TestSuite([ test_lowlevel.suite(),
    test_lower_midlevel.suite()
    ])

def run():
  runner = unittest.TextTestRunner()
  runner.run(suite())

