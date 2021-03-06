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
  if len(xs) == 0:
    return [a]
  result = []
  for x in xs[:-1]:
    result.append(x)
    result.append(a)
  result.append(xs[-1])
  return result

