# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import endofunctor, bifunctor

# forall formulas X,
#  self.composite().onObject(X)
#  == self.bifunctor().compose_right(f(self.right_leg())).onObjects(X, f(self.formula()))
# where f replaces each variable x with y, where (x, y) is in self.replacements().
class Factorization:
  # return: the endofunctor being factored
  def composite(self):
    raise Exception("Not yet implemented.")

  # return: the factored bifunctor
  def bifunctor(self):
    raise Exception("Not yet implemented.")

  # return: another endofunctor
  def right_leg(self):
    raise Exception("Not yet implemented.")

  # return: a formula
  def formula(self):
    raise Exception("Not yet implemented.")

  # return: a list of (a, b) pairs where
  #  a, b are variables,
  #  a is quantified in self.right_leg()
  #  a is to be replaced with b.
  def replacements(self):
    raise Exception("Not yet implemented.")

# Integer ranges of the form [a, b) or [a, infinity)
class Range:
  # set b = None for infinity
  def __init__(self, a, b = None):
    self.a = a
    self.b = b

  def contains(self, x):
    return self.a <= x and (b is None or x < b)

class Condition:
  def _continue(self, formula):
    raise Exception("Not yet implemented.")
  def _matches(self, formula):
    raise Exception("Not yet implemented.")
  # ... more private methods as needed ...

class IsAlways(Condition):
  pass

class IdentityRightLeg(Condition):
  pass

class Variance(Condition):
  # desired_variance: true or false
  def __init__(self, desired_variance):
    self.desired_variance = desired_variance

class Involving(Condition):
  def __init__(self, variables):
    self.variables = variables

class Universal(Condition):
  def __init__(self, range):
    self.range = range

class Disjunctive(Condition):
  def __init__(self, range):
    self.range = range

class Concludes(Condition):
  def __init__(self, formula):
    self.formula = formula

class Assumes(Condition):
  def __init__(self, formula):
    self.formula = formula

# endofunctor: an endofunctor to be factored.
# conditions: a list of Condition instances constraining the kinds of factorizations to look for.
# return: a list of factorizations f meeting each of the conditions with f.composite() == endofunctor.
def factor(endofunctor, conditions):
  raise Exception("Not yet implemented.")

