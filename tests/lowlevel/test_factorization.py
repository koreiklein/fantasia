# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import unittest

from tests.lowlevel import common_enriched_objects

from calculus.enriched import factor, constructors, endofunctor as enrichedEndofunctor

class FactorTest(unittest.TestCase, common_enriched_objects.CommonObjects):
  def setUp(self):
    self.add_common_objects()

  def assert_does_not_match(self, endofunctor, ef_constraint, f):
    for c in f(ef_constraint = ef_constraint, endofunctor = endofunctor):
      self.fail("Should not have matched.")

  def assert_matches_once(self, endofunctor, ef_constraint, f, datum = None):
    found = False
    for c in f( ef_constraint = ef_constraint, endofunctor = endofunctor):
      if found:
        self.fail("found too many matches")
      else:
        found = True
        if datum is not None:
          self.assertEqual(datum, c)
    if not found:
      self.fail("found not enough matcheds")

  def assert_ef_matches_once(self, endofunctor, ef_constraint, datum = None):
    self.assert_matches_once(endofunctor, ef_constraint, factor.ef_match, datum)
  def assert_ef_does_not_match(self, endofunctor, ef_constraint):
    self.assert_does_not_match(endofunctor, ef_constraint, factor.ef_match)
  def assert_bf_matches_once(self, bifunctor, bf_constraint, datum = None):
    self.assert_matches_once(bifunctor, bf_constraint, factor.bf_match, datum)
  def assert_bf_does_not_match(self, bifunctor, bf_constraint):
    self.assert_does_not_match(bifunctor, bf_constraint, factor.bf_match)
  def assert_formula_matches_once(self, formula, formula_constraint, datum = None):
    self.assert_matches_once(formula, formula_constraint, factor.formula_match, datum)
  def assert_formula_does_not_match(self, formula, formula_constraint):
    self.assert_does_not_match(formula, formula_constraint, factor.formula_match)

  def test_variance(self):
    for ef in [self.and_W, self.W_and, endofunctor.not_functor.compose(self.W_and),
        self._and(self.exists_d_Y), endofunctor.not_functor.compose(endofunctor.not_functor)]:
      self.assert_ef_matches_once(
          endofunctor = ef, ef_constraint = factor.variance(ef.covariant()))
      self.assert_ef_does_not_match(
          endofunctor = ef, ef_constraint = factor.variance(not ef.covariant()))

  def test_right_variance(self):
    for bf in [self._and_, self._and__Z_and, self._and_.compose(endofunctor.not_functor),
        self._and_.precompose(
          endofunctor.not_functor,
          self.and_W.compose(endofunctor.not_functor))]:
      self.assert_bf_matches_once(
          bifunctor = bf, bf_constraint = factor.right_variance(bf.right_variance()))
      self.assert_bf_does_not_match(
          bifunctor = bf, bf_constraint = factor.right_variance(not bf.right_variance()))

  def test_exact(self):
    self.assert_formula_matches_once(
        formula = self.X, formula_constraint = factor.exact(self.X))
    self.assert_formula_does_not_match(
        formula = self.X, formula_constraint = factor.exact(self.W))

  def test_involving_all(self):
    self.assert_formula_matches_once(
        formula = self.X, formula_constraint = factor.involving_all([self.a, self.c]))
    self.assert_formula_does_not_match(
        formula = self.X, formula_constraint = factor.involving_all([self.a, self.b]))
    self.assert_formula_does_not_match(
        formula = self.X, formula_constraint = factor.involving_all([self.b]))

  def test_involving_any(self):
    self.assert_formula_matches_once(
        formula = self.X, formula_constraint = factor.involving_any([self.a]),
        datum = [self.a])
    self.assert_formula_matches_once(
        formula = self.X, formula_constraint = factor.involving_any([self.a, self.b]),
        datum = [self.a])
    self.assert_formula_matches_once(
        formula = self.X, formula_constraint = factor.involving_any([self.b, self.a]),
        datum = [self.a])

    self.assert_formula_matches_once(
        formula = self.X, formula_constraint = factor.involving_any([self.c, self.a]))

    self.assert_formula_does_not_match(
        formula = self.X, formula_constraint = factor.involving_any([self.b, self.d]))

  def test_apply(self):
    def f(formula, a, b):
      self.assertEqual(formula, b.onObject(a))
      return a
    results = list(factor.formula_match(
      formula = constructors.Not(self.W_and_X),
      formula_constraint = factor.apply(
        formula_constraint = factor.involving_all([self.a, self.c]) ,
        ef_constraint = factor.variance(covariant = False),
        f = f)))

    self.assertEqual(len(results), 3)
    self.assertTrue( self.X.value in results )
    self.assertTrue( self.X in results )
    self.assertTrue( self.W_and_X in results )

########################## OLD CODE #######################

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
        search_result.instantiated_formula())
    self.assertEqual(right_leg.onObject(self.Z),
        search_result.instantiated_right_leg().onObject(self.Z))

    X = self.A
    one = endofunctor.onObject(X)
    two = search_result.factorization().bifunctor().compose_right(
        search_result.factorization().right_leg()).onObjects(
            X,
            search_result.factorization().formula())
    self.assertEqual(one, two)

    arrow = search_result.instantiate()
    self.assertEqual(arrow.src,
        search_result.factorization().right_leg().onObject(
          search_result.factorization().formula()))
    self.assertEqual(arrow.tgt,
        search_result.instantiated_right_leg().onObject(
          search_result.instantiated_formula()))

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
    self.assertEqual(formula, search_results[0].instantiated_formula())

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
