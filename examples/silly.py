# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic

class StringPrimitive(basic.PrimitiveObject):
  def __init__(self, s):
    self._s = s
  def __eq__(self, other):
    return other.__class__ == StringPrimitive and self._s == other._s
  def __ne__(self, other):
    return not (self == other)
  def string(self):
    return self._s
  def substituteVar(self, a, b):
    return self
  def updateVars(self):
    return self
  def assertEqual(self, other):
    assert(self._s == other._s)

# These need have no real implementation.
# TODO(koreiklein) Consider formally defining what properties we should require of the building blocks
# for primitive Logic formulas.
cookie = StringPrimitive("cookie")
milk = StringPrimitive("milk")
napkin = StringPrimitive("napkin")

cookie_implies_milk = basic.Implies(cookie, milk)
milk_implies_napkin = basic.Implies(milk, napkin)

starting_claim = basic.And(cookie_implies_milk, milk_implies_napkin)

# COMPACT VERSION
#modus_ponens = starting_claim.identity().forwardFollow(lambda formula:
#    formula.forwardOnLeftFollow(lambda formula:
#      formula.forwardOnNotFollow(lambda formula:
#        formula.backwardOnRightFollow(lambda formula:
#          formula.backwardApply(basic.Not(napkin)).backwardFollow(lambda formula:
#          formula.backwardCommute())).backwardFollow(lambda formula:
#        formula.backwardAssociateA()))).forwardFollow(lambda formula:
#    formula.forwardApply()))

# COMMENTED VERSION
modus_ponens = starting_claim.identity().forwardFollow(lambda formula:
    # | cookie | | milk    |   | milk | | napkin
    # |        | *-----    |   |      | *-------
    # *-----------------   |   *-----------------
    formula.forwardOnLeftFollow(lambda formula:
      # | cookie | | milk
      # |        | *-----
      # *-----------------
      formula.forwardOnNotFollow(lambda formula:
        # cookie | | milk
        #        | *-----
        formula.backwardOnRightFollow(lambda formula:
          # | milk
          # *-----
          formula.backwardApply(basic.Not(napkin)).backwardFollow(lambda formula:
          # | milk | |napkin | |napkin
          # |      | *------ | *------
          # *----------------|
          formula.backwardCommute())).backwardFollow(lambda formula:
        # cookie | |napkin | milk_implies_napkin
        #        | *------ |
        #        |
        formula.backwardAssociateA()))).forwardFollow(lambda formula:
    # | cookie | | napkin | milk_implies_napkin | milk_implies_napkin
    # |        | *------- |                     |
    # |                   |                     |
    # *---------------------------------------- |
    formula.forwardApply()))

    # Q.E.D.

    # This proof contains 4 non-functorial arrows.
    # This proof contains 2 arrows which are not functorial, commute, or associate.
    # When performed in a reasonably nice UI, this proof will consist of but a single arrow.


