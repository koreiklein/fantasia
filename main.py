# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from logic import linear_example, linear_example_python_backend
from logic.lib import induction
import glrunner

linear_example_python_backend.test()

glrunner.run()
