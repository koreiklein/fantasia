# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import unittest

from tests.lowlevel import common_enriched_objects

from calculus.enriched import factor, constructors, endofunctor as enrichedEndofunctor

class FactorTest(unittest.TestCase, common_enriched_objects.CommonObjects):
  def setUp(self):
    self.add_common_objects()

  # identity_right_leg: if True, check that the right leg is the identity,
  #                     if False, check that the right leg is not the identity,
  #                     if None, check nothing.
  def assert_factorization_well_formed_with_replacements(self, endofunctor, factorization,
      intended_replacements, identity_right_leg = None):
    replacements = factorization.replacements()

    for a, b in intended_replacements:
      self.assertTrue( (a, b) in replacements )
    for a, b in replacements:
      self.assertTrue( (a, b) in intended_replacements )

    right_leg = factorization.right_leg()
    if identity_right_leg is not None:
      self.assertEqual(identity_right_leg, enrichedEndofunctor.is_identity_functor(right_leg))
    formula = factorization.formula()
    for a, b in replacements:
      right_leg = right_leg.replace(a, b)
      formula = formula.replace(a, b)

    X = self.A
    one = endofunctor.onObject(X)
    two = factorization.bifunctor().compose_right(right_leg).onObjects(X, formula)
    self.assertEqual(one, two)

  def assert_factorization_meets_condition(self, factorization, condition):
    self.assertTrue(condition._matches(factorization))

  def assert_does_not_factor(self, endofunctor, conditions):
    self.assertEqual(0, len(factor.factor(endofunctor = endofunctor, conditions = conditions)))

  def assert_factors_once_with_replacements(self, endofunctor, conditions, formula, replacements = [],
      identity_right_leg = None) :
    factorizations = factor.factor(endofunctor = endofunctor, conditions = conditions)
    self.assertEqual(1, len(factorizations))
    self.assert_factorization_well_formed_with_replacements(
        endofunctor = endofunctor,
        factorization = factorizations[0],
        intended_replacements = replacements,
        identity_irght_leg = identity_right_leg)
    self.assertEqual(formula, factorizations[0])

  def test_factor_and(self):
    for endofunctor in [self.and_W, self.W_and]:
      self.assert_factors_once_with_replacements(
          endofunctor = self.endofunctor,
          identity_right_leg = True,
          conditions = [factor.IsAlways(True)],
          formula = self.W)

      self.assert_factors_once_with_replacements(
          identity_right_leg = True,
          endofunctor = self.endofunctor,
          conditions = [factor.IsAlways(True), factor.IdentityRightLeg()],
          formula = self.W)

  def test_factor_no_always(self):
    for endofunctor in [ self._and(constructors.Holds(self.a, self.b))
                       , self.and_(constructors.Holds(self.a, self.b))]:
      self.assert_does_not_factor(
          endofunctor = endofunctor,
          conditions = [factor.IsAlways(True)])

  def test_factor_involving(self):
    self.assert_does_not_factor(
        endofunctor = self.and_W,
        conditions = [factor.Involving(variables = [self.c])])
    for variables in [ [self.a], [self.b], [self.a, self.b] ]:
      self.assert_factors_once_with_replacements(
        identity_right_leg = True,
        endofunctor = self.and_W,
        conditions = [factor.IsAlways(True), factor.Involving(variables = variables)],
        formula = self.W)

    for endofunctor in [ self.and_W.compose(self.and_X)
                       , self.W_and.compose(self.and_X)
                       , self._and(self.W_and_X)
                       , self.and_(self.W_AND_X_and_Y_and_Z)]:
      for formula, involved_variable in [(self.W, self.b), (self.X, self.c)]:
        self.assert_factors_once_with_replacements(
            identity_right_leg = True,
            endofunctor = endofunctor,
            conditions = [factor.IsAlways(True), factor.Involving(variables = [involved_variable])],
            formula = formula)

  def test_variance(self):
    endofunctor = enrichedEndofunctor.not_functor.compose(
      self.and_W).compose(
        enrichedEndofunctor.not_functor).compose(
          self.and_X)
    for formula, covariant in [(self.X, True), (self.W, False)]:
      self.assert_factors_once_with_replacements(
        identity_right_leg = True,
        endofunctor = endofunctor,
        conditions = [factor.IsAlways(True), factor.Variance(covariant)],
        formula = formula)

  def test_universal(self):
    self.assert_does_not_factor(
      endofunctor = self.and_X.compose(self._and(self.exists_d_Y)),
      conditions = [factor.Universal(factor.Range(2, 5))])

    self.assert_factors_once_with_replacements(
      identity_right_leg = True,
      endofunctor = self.and_X.compose(self._and(self.exists_d_Y)),
      conditions = [factor.Universal(factor.Range(1, 2))],
      formula = self.exists_d_Y)

    self.assert_factors_once_with_replacements(
      identity_right_leg = True,
      endofunctor = self.and_X.compose(self._and(constructors.Always(self.exists_d_Y))),
      conditions = [factor.Universal(factor.Range(0, None)), factor.IsAlways(True)],
      formula = constructors.Always(self.exists_d_Y))

  def test_disjunctive(self):
    self.assert_does_not_factor(
      endofunctor = self.and_X.compose(self._and(self.W_or_X)),
      conditions = [factor.Disjunctive(factor.Range(1, 2))])

    self.assert_factors_once_with_replacements(
      identity_right_leg = True,
      endofunctor = self.and_X.compose(self._and(self.W_or_X)),
      conditions = [factor.Disjunctive(factor.Range(1, 3))],
      formula = self.W_or_X)

    for formula, always in [ (constructors.Always(self.W_or_X), True)
                           , (self.W_or_X_or_Y_or_Z, False) ]:
      self.assert_factors_once_with_replacements(
          identity_right_leg = True,
          endofunctor = self.and_X.compose(
            self._and(constructors.Always(self.W_or_X))).compose(
              self.and_(self.W_or_X_or_Y)),
            conditions = [factor.IsAlways(always), factor.Disjunctive(factor.Range(1, 4))],
            formula = formula)

  def test_concludes(self):
    endofunctor = endofunctor.not_functor.compose(
        self._and(self.W_or_X_or_Y).compose(
          self._and(self.if_Y_then_X))).compose( # contravariant
              endofunctor.not_functor).compose(
                  self._and(self.if_W_then_X)).compose( # covariant
                      self.X_and)
    self.assert_factors_once_with_replacements(
        endofunctor = endofunctor,
        identity_right_leg = True,
        conditions = [factor.IdentityRightLeg(True), factor.Concludes(self.W)],
        formula = self.W)

    self.assertEqual(2, len(factor.factor(
      endofunctor = endofunctor,
      conditions = [factor.IdentityRightLeg(False), factor.Concludes(self.X)])))

    self.assert_factors_once_with_replacements(
        endofunctor = endofunctor,
        conditions = [ factor.Variance(True)
                     , factor.Concludes(self.X)],
        formula = self.X)

    self.assert_factors_once_with_replacements(
        endofunctor = endofunctor,
        conditions = [ factor.IdentityRightLeg(False)
                     , factor.Variance(False)
                     , factor.Concludes(self.X)],
        formula = self.X)

  def test_assumes(self):
    endofunctor = endofunctor.not_functor.compose(
        self._and(self.W_or_X_or_Y).compose(
          self._and(self.if_Y_then_X))).compose( # contravariant
              endofunctor.not_functor).compose(
                  self._and(self.if_W_then_X)).compose( # covariant
                      self.X_and)

    self.assert_does_not_factor(
        endofunctor = endofunctor,
        conditions = [factor.Assumes(self.X)])

    self.assert_factors_once_with_replacements(
        endofunctor = endofunctor,
        conditions = [factor.Assumes(self.Y)],
        formula = self.Y)

    self.assert_factors_once_with_replacements(
        endofunctor = endofunctor,
        conditions = [factor.Assumes(self.W)],
        formula = self.W)

  def test_replacements(self):
    endofunctor = self.and_W.compose(
        self._and(constructors.Exists(
          bindings = [constructors.OrdinaryVariableBinding(self.a)],
          value = self.if_W_then_X)))

    formula = self.X.substituteVariable(self.a, self.x)
    self.assert_factors_once_with_replacements(
        endofunctor = endofunctor,
        identity_right_leg = False,
        conditions = [factor.Concludes(formula)],
        replacements = [(self.a, self.x)],
        formula = formula)

    formula = self.W.substituteVariable(self.a, self.x)
    self.assert_factors_once_with_replacements(
        endofunctor = endofunctor,
        identity_right_leg = False,
        conditions = [factor.Assumes(formula)],
        replacements = [(self.a, self.x)],
        formula = formula)

