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


def suite():
  return unittest.makeSuite(FactorTest)
