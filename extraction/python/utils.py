# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

repTrue = 1

def repAnd(repsOfValues):
  res = repTrue
  for valueRep in repsOfValues:
    res = (res, valueRep)
  return res

