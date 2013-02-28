# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from logic import linearui
from logic.linear_python_backend import curry_howard

repTrue = 1

def repAnd(repsOfValues):
  res = repTrue
  for valueRep in repsOfValues:
    res = (res, valueRep)
  return res

