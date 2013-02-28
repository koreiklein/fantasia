# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from logic import linear_example, linear_example_python_backend
from logic.lib import induction, induction_python_backend
import glrunner

from sys import setrecursionlimit

setrecursionlimit(500000)

linear_example_python_backend.test()
induction_python_backend.test()

glrunner.run()
