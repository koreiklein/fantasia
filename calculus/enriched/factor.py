# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import endofunctor, bifunctor

# forall formulas X,
#  self.composite().onObject(X)
#  == self.bifunctor().compose_right(self.right_leg()).onObjects(X, self.formula())
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

  # return: a list of pairs (a, b) where a, b are variables and
  #   a will be instantiated in self.formula(), self.right_leg(),
  #   and self.bifunctor() to produce the instantiated versions.
  def replacements(self):
    raise Exception("Not yet implemented.")

  # formula: an enriched formula
  # return: an enriched arrow:
  #  self.composite().onObject(formula)
  #  =
  #  self.bifunctor().onObjects(
  #          formula,
  #          self.right_leg().onObject(self.formula()))
  # -->
  #  self.instantiated_bifunctor().onObjects(
  #          formula,
  #          self.instantiated_right_leg().onObject(self.instantiated_formula())
  def replace(self, formula):
    raise Exception("Not yet implemented.")

  # return: true if there's anything for the instantiator to do.
  def needs_instantiation(self):
    raise Exception("Not yet implemented.")

  def instantiated_bifunctor(self):
    raise Exception("Not yet implemented.")
  def instantiated_right_leg(self):
    raise Exception("Not yet implemented.")
  def instantiated_formula(self):
    raise Exception("Not yet implemented.")

# Integer ranges of the form [a, b) or [a, infinity)
class Range:
  # set b = None for infinity
  def __init__(self, a, b = None):
    self.a = a
    self.b = b

  def contains(self, x):
    return self.a <= x and (b is None or x < b)

class Constraint:
  def _continue(self, formula):
    raise Exception("Not yet implemented.")
  def _matches(self, factorization):
    raise Exception("Not yet implemented.")
  # ... more private methods as needed ...

class IsAlways(Constraint):
  def __init__(self, is_always):
    self.is_always = is_always

class IdentityRightLeg(Constraint):
  def __init__(self, be_identity):
    self.be_identity = be_identity

# for controlling the variance of the right argument to the BIFUNCTOR
class BifunctorVariance(Constraint):
  # desired_variance: true or false
  def __init__(self, desired_variance):
    self.desired_variance = desired_variance

class Involving(Constraint):
  def __init__(self, variables):
    self.variables = variables

class Universal(Constraint):
  def __init__(self, range):
    self.range = range

class Disjunctive(Constraint):
  def __init__(self, range):
    self.range = range

class ExactFormula(Constraint):
  def __init__(self, formula):
    self.formula = formula

class RightLegVariance(Constraint):
  def __init__(self, covariant):
    self.covariant = covariant

class ReplaceAny(Constraint):
  def __init__(self, variables):
    self.variables = variables

class ReplaceAll(Constraint):
  def __init__(self, variables):
    self.variables = variable

# NOTE: This function should not return a factorization when there exists a "closer" factorization.
# TODO: Describe this requirement fully.

# endofunctor: an endofunctor to be factored.
# conditions: a list of Constraint instances constraining the kinds of factorizations to look for.
# return: a list of factorizations f meeting each of the conditions with f.composite() == endofunctor.
def factor(endofunctor, conditions):
  raise Exception("Not yet implemented.")

