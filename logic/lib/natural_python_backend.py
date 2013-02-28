# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from logic import linearui_backend_utils
from logic.lib import natural

class SuccessorRep:
  def __init__(self, small, big):
    self.small = small
    self.big = big

class CompareRep:
  def __init__(self, values, strict):
    self.values = values
    self.strict = strict

  def __repr__(self):
    if self.strict:
      c = "<"
    else:
      c = "<="
    return "%s %s %s, via %s"%(self.values[0], c, self.values[-1], self.values)

increasingRep = (lambda ((one, notNotSTR), notC): notNotSTR(lambda STR:
    notC(CompareRep(values = [STR.small, STR.big], strict = True))))

successorExistsRep = (lambda ((one, notNotN), notResults): notNotN(lambda n:
    notResults((((1, n + 1), SuccessorRep(n, n + 1)), SuccessorRep(n, n + 1)))))

def _e(compareABRep, compareBCRep):
  if compareABRep.values[-1] != compareBCRep.values[0]:
    raise Exception("\n\tCompare AB = %s, \n\tCompare BC = %s"%(compareABRep.values, compareBCRep.values))
  assert(compareABRep.values[-1] == compareBCRep.values[0])
  assert(False == compareABRep.strict)
  assert(True == compareBCRep.strict)
  values = list(compareABRep.values)
  values.extend(compareBCRep.values[1:])
  return CompareRep(values, True)
transitivityRep = (lambda (((one, notNotCAB), notNotCBC), notC):
  notNotCAB(lambda CAB: notNotCBC(lambda CBC:
    notC(_e(CAB, CBC)))))

def _r(compareSLRep):
  assert(compareSLRep.strict == True)
  return CompareRep(compareSLRep.values, False)
weakeningRep = (lambda ((one, notNotC), notC): notNotC(lambda c:
  notC(_r(c))))

reflexivityRep = (lambda ((one, notNotN), notCompare): notNotN(lambda n:
    notCompare(CompareRep([n], False))))

zero_naturalRep = 0

exists_fiveRep = 5

