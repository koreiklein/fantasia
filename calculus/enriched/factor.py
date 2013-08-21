# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import endofunctor, bifunctor

class SearchResult:
  # return: the endofunctor being factored
  def composite(self):
    raise Exception("Not yet implemented.")

  # return: a factorization fact such that
  # self.composite() == factorization.composite()
  def factorization(self):
    raise Exception("Not yet implemented.")

  # return: true iff self.instantiated_right_leg().onObject(self.instantiated_formula())
  #         is different from self.factorization().right_leg().onObject(
  #                               self.factorization().formula())
  #     iff self.instantiate() is not the identity arrow.
  def needs_instantiation(self):
    raise Exception("Not yet implemented.")

  # return: an endofunctor
  def instantiated_right_leg(self):
    raise Exception("Not yet implemented.")

  # return: a formula.
  def instantiated_formula(self):
    raise Exception("Not yet implemented.")

  # return: a list of pairs (a_i, b_i) such that
  # self.instantiated_right_leg() and self.instantiated_formula() differ
  # from self.factorization().right_leg() and self.factorization().formula() only in
  # that the variables a_i have been instantiated with b_i.
  def replacements(self):
    raise Exception("Not yet implemented.")

  # return: an arrow:
  #   self.factorization().right_leg().onObject(self.factorization().formula())
  #  --> self.instantiated_right_leg().onObject(
  #           self.instantiated_formula())
  def instantiate(self, x):
    raise Exception("Not yet implemented.")

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
# return: an iterable of SearchResult instances R with R.instantiated_factorization() meeting
#  each of the constraints on factorizations and with R.replacements() meeting each
#  of the conditions on the nature of variable instantiation.
def factor(endofunctor, constraints):
  raise Exception("Not yet implemented.")

