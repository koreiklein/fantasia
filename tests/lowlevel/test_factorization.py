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
  def assert_factorization_well_formed_with_replacements(self, endofunctor, search_result,
      intended_replacements, identity_right_leg = None):
    replacements = search_result.replacements()

    for a, b in intended_replacements:
      self.assertTrue( (a, b) in replacements )
    for a, b in replacements:
      self.assertTrue( (a, b) in intended_replacements )

    right_leg = search_result.factorization().right_leg()
    if identity_right_leg is not None:
      self.assertEqual(identity_right_leg, enrichedEndofunctor.is_identity_functor(right_leg))
    formula = search_result.factorization().formula()
    for a, b in replacements:
      right_leg = right_leg.replace(a, b)
      formula = formula.replace(a, b)

    self.assertEqual(formula,
        search_result.instantiated_factorization().formula())
    self.assertEqual(right_leg.onObject(self.Z),
        search_result.instantiated_factorization().right_leg().onObject(self.Z))

    X = self.A
    one = endofunctor.onObject(X)
    two = search_result.factorization().bifunctor().compose_right(
        search_result.factorization().right_leg()).onObjects(
            X,
            search_result.factorization().formula())
    self.assertEqual(one, two)

    three = search_result.instantiated_factorization().composite().onObject(X)
    arrow = search_result.instantiate()(X)
    self.assertEqual(one, arrow.src)
    self.assertEqual(three, arrow.tgt)

  def assert_factorization_meets_condition(self, factorization, condition):
    self.assertTrue(condition._matches(factorization))

  def assert_does_not_factor(self, endofunctor, constraints):
    self.assertEqual(0, len(factor.factor(endofunctor = endofunctor, constraints = constraints)))

  def assert_factors_once_with_replacements(self, endofunctor, constraints, formula, replacements = [],
      identity_right_leg = None) :
    search_results = factor.factor(endofunctor = endofunctor, constraints = constraints)
    self.assertEqual(1, len(search_results))
    self.assert_factorization_well_formed_with_replacements(
        endofunctor = endofunctor,
        search_result = search_results[0],
        intended_replacements = replacements,
        identity_irght_leg = identity_right_leg)
    self.assertEqual(formula, search_results[0].instantiated_factorization().formula())

  def test_factor_and(self):
    for endofunctor in [self.and_W, self.W_and]:
      self.assert_factors_once_with_replacements(
          endofunctor = self.endofunctor,
          identity_right_leg = True,
          constraints = [factor.IsAlways(True)],
          formula = self.W)

      self.assert_factors_once_with_replacements(
          identity_right_leg = True,
          endofunctor = self.endofunctor,
          constraints = [factor.IsAlways(True), factor.IdentityRightLeg()],
          formula = self.W)

  def test_factor_no_always(self):
    for endofunctor in [ self._and(constructors.Holds(self.a, self.b))
                       , self.and_(constructors.Holds(self.a, self.b))]:
      self.assert_does_not_factor(
          endofunctor = endofunctor,
          constraints = [factor.IsAlways(True)])

  def test_factor_involving(self):
    self.assert_does_not_factor(
        endofunctor = self.and_W,
        constraints = [factor.Involving(variables = [self.c])])
    for variables in [ [self.a], [self.b], [self.a, self.b] ]:
      self.assert_factors_once_with_replacements(
        identity_right_leg = True,
        endofunctor = self.and_W,
        constraints = [factor.IsAlways(True), factor.Involving(variables = variables)],
        formula = self.W)

    for endofunctor in [ self.and_W.compose(self.and_X)
                       , self.W_and.compose(self.and_X)
                       , self._and(self.W_and_X)
                       , self.and_(self.W_AND_X_and_Y_and_Z)]:
      for formula, involved_variable in [(self.W, self.b), (self.X, self.c)]:
        self.assert_factors_once_with_replacements(
            identity_right_leg = True,
            endofunctor = endofunctor,
            constraints = [factor.IsAlways(True), factor.Involving(variables = [involved_variable])],
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
        constraints = [factor.IsAlways(True), factor.BifunctorVariance(covariant)],
        formula = formula)

  def test_universal(self):
    self.assert_does_not_factor(
      endofunctor = self.and_X.compose(self._and(self.exists_d_Y)),
      constraints = [factor.Universal(factor.Range(2, 5))])

    self.assert_factors_once_with_replacements(
      identity_right_leg = True,
      endofunctor = self.and_X.compose(self._and(self.exists_d_Y)),
      constraints = [factor.Universal(factor.Range(1, 2))],
      formula = self.exists_d_Y)

    self.assert_factors_once_with_replacements(
      identity_right_leg = True,
      endofunctor = self.and_X.compose(self._and(constructors.Always(self.exists_d_Y))),
      constraints = [factor.Universal(factor.Range(0, None)), factor.IsAlways(True)],
      formula = constructors.Always(self.exists_d_Y))

  def test_disjunctive(self):
    self.assert_does_not_factor(
      endofunctor = self.and_X.compose(self._and(self.W_or_X)),
      constraints = [factor.Disjunctive(factor.Range(1, 2))])

    self.assert_factors_once_with_replacements(
      identity_right_leg = True,
      endofunctor = self.and_X.compose(self._and(self.W_or_X)),
      constraints = [factor.Disjunctive(factor.Range(1, 3))],
      formula = self.W_or_X)

    for formula, always in [ (constructors.Always(self.W_or_X), True)
                           , (self.W_or_X_or_Y_or_Z, False) ]:
      self.assert_factors_once_with_replacements(
          identity_right_leg = True,
          endofunctor = self.and_X.compose(
            self._and(constructors.Always(self.W_or_X))).compose(
              self.and_(self.W_or_X_or_Y)),
            constraints = [factor.IsAlways(always), factor.Disjunctive(factor.Range(1, 4))],
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
        constraints = [factor.IdentityRightLeg(True),
          factor.RightLegVariance(True),
          factor.ExactFormula(self.W)],
        formula = self.W)

    self.assertEqual(2, len(factor.factor(
      endofunctor = endofunctor,
      constraints = [factor.IdentityRightLeg(False),
        factor.RightLegVariance(True),
        factor.ExactFormula(self.X)])))

    self.assert_factors_once_with_replacements(
        endofunctor = endofunctor,
        constraints = [ factor.BifunctorVariance(True)
                     , factor.RightLegVariance(True)
                     , factor.ExactFormula(self.X)],
        formula = self.X)

    self.assert_factors_once_with_replacements(
        endofunctor = endofunctor,
        constraints = [ factor.IdentityRightLeg(False)
                     , factor.BifunctorVariance(False)
                     , factor.RightLegVariance(True)
                     , factor.ExactFormula(self.X)],
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
        constraints = [factor.RightLegVariance(False), factor.ExactFormula(self.X)])

    self.assert_factors_once_with_replacements(
        endofunctor = endofunctor,
        constraints = [factor.RightLegVariance(False), factor.ExactFormula(self.Y)],
        formula = self.Y)

    self.assert_factors_once_with_replacements(
        endofunctor = endofunctor,
        constraints = [factor.RightLegVariance(False), factor.ExactFormula(self.W)],
        formula = self.W)

  def test_replacements(self):
    endofunctor = self.and_W.compose(
        self._and(constructors.Exists(
          bindings = [constructors.OrdinaryVariableBinding(self.a)],
          value = self.if_W_then_X)))

    self.assert_factors_once_with_replacements(
        endofunctor = endofunctor,
        constraints = [factor.ReplaceAll([self.e])],
        formula = self.if_W_then_X.substituteVariable(self.a, self.e))

    self.assert_does_not_factor(
        endofunctor = endofunctor,
        constraints = [factor.ReplaceAny([])])

    self.assert_factors_once_with_replacements(
        endofunctor = endofunctor,
        identity_right_leg = False,
        constraints = [factor.ReplaceAny([self.e]),
          factor.ExactFormula(self.X.substituteVariable(self.a, self.e))],
        formula = self.X.substituteVariable(self.a, self.e))

    formula = self.X.substituteVariable(self.a, self.x)
    self.assert_factors_once_with_replacements(
        endofunctor = endofunctor,
        identity_right_leg = False,
        constraints = [factor.RightLegVariance(True), factor.ExactFormula(formula)],
        replacements = [(self.a, self.x)],
        formula = formula)

    formula = self.W.substituteVariable(self.a, self.x)
    self.assert_factors_once_with_replacements(
        endofunctor = endofunctor,
        identity_right_leg = False,
        constraints = [factor.RightLegVariance(False), factor.ExactFormula(formula)],
        replacements = [(self.a, self.x)],
        formula = formula)

def suite():
  return unittest.makeSuite(FactorTest)
