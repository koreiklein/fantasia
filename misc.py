# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

left = 'left'
right = 'right'

def flipSide(side):
  if side == left:
    return right
  else:
    assert(side == right)
    return left

def _interleave(a, xs):
  result = []
  for x in xs:
    result.append(x)
    result.append(a)
  return result

