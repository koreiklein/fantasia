# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import unittest

from tests.lowlevel import common_enriched_objects

from calculus.enriched import factor, constructors, endofunctor as enrichedEndofunctor

from calculus.enriched.endofunctor import not_functor, always_functor

class FactorTest(unittest.TestCase, common_enriched_objects.CommonObjects):
  def setUp(self):
    self.add_common_objects()

  def assert_does_not_match(self, gen):
    for c in gen:
      self.fail("Should not have matched.")

  def assert_matches_once(self, gen, datum = None):
    found = False
    for c in gen:
      if found:
        self.fail("found too many matches")
      else:
        found = True
        if datum is not None:
          self.assertEqual(datum, c)
    if not found:
      self.fail("found not enough matcheds")

  def assert_ef_matches_once(self, endofunctor, ef_constraint, datum = None):
    self.assert_matches_once(factor.ef_match(ef_constraint, endofunctor), datum)
  def assert_ef_does_not_match(self, endofunctor, ef_constraint):
    self.assert_does_not_match(factor.ef_match(ef_constraint, endofunctor))
  def assert_bf_matches_once(self, bifunctor, bf_constraint, datum = None):
    self.assert_matches_once(factor.bf_match(bf_constraint, bifunctor), datum)
  def assert_bf_does_not_match(self, bifunctor, bf_constraint):
    self.assert_does_not_match(factor.bf_match(bf_constraint, bifunctor))
  def assert_formula_matches_once(self, formula, formula_constraint, datum = None):
    self.assert_matches_once(factor.formula_match(formula_constraint, formula), datum)
  def assert_formula_does_not_match(self, formula, formula_constraint):
    self.assert_does_not_match(factor.formula_match(formula_constraint, formula))

  def test_variance(self):
    for ef in [self.and_W, self.W_and, not_functor.compose(self.W_and),
        self._and(self.exists_d_Y), not_functor.compose(not_functor)]:
      self.assert_ef_matches_once(
          endofunctor = ef, ef_constraint = factor.variance(ef.covariant()))
      self.assert_ef_does_not_match(
          endofunctor = ef, ef_constraint = factor.variance(not ef.covariant()))

  def test_right_variance(self):
    for bf in [self._and_, self._and__Z_and, self._and_.compose(not_functor),
        self._and_.precompose(
          not_functor,
          self.and_W.compose(not_functor))]:
      self.assert_bf_matches_once(
          bifunctor = bf, bf_constraint = factor.right_variance(bf.right_covariant()))
      self.assert_bf_does_not_match(
          bifunctor = bf, bf_constraint = factor.right_variance(not bf.right_covariant()))

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
        datum = (self.X, [self.a]))
    self.assert_formula_matches_once(
        formula = self.X, formula_constraint = factor.involving_any([self.a, self.b]),
        datum = (self.X, [self.a]))
    self.assert_formula_matches_once(
        formula = self.X, formula_constraint = factor.involving_any([self.b, self.a]),
        datum = (self.X, [self.a]))

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

  def test_all_with_apply(self):
    results = list(factor.formula_match(
      formula = self._and(constructors.Not(self.W_and_X)).onObject(self.Z),
      formula_constraint = factor.apply(
        formula_constraint = factor.all_formula_constraints(
          formula_constraints = [
            factor.involving_all([self.a, self.c]),
            factor.apply(
              formula_constraint = factor.no_formula_constraint,
              ef_constraint = factor.is_always,
              f = lambda formula, a, b : a)
            ],
          f = lambda x_y : x_y[1]),
        ef_constraint = factor.variance(covariant = False),
        f = lambda formula, a, b : a)))

    self.assertEqual(len(results), 1)
    self.assertEqual(results[0], self.X.value)

  def test_apply_right(self):
    def gen_ef_constraint(bi_constraint):
      return factor.apply_right(
        formula_constraint = factor.all_formula_constraints(
          formula_constraints = [
            factor.involving_all([self.a, self.c]),
            factor.apply(
              formula_constraint = factor.no_formula_constraint,
              ef_constraint = factor.is_always,
              f = lambda formula, a, b : a)
            ],
          f = lambda x_y : x_y[1]),
        bi_constraint = bi_constraint,
        f = lambda endofunctor, a, b: a)

    results = list(factor.ef_match(
      endofunctor = self._and(constructors.And([self.X, constructors.Not(self.X)])),
      ef_constraint = gen_ef_constraint(factor.right_variance(False))))
    self.assertEqual(1, len(results))
    self.assertEqual(results[0], self.X.value)

    results = list(factor.ef_match(
      endofunctor = self._and(constructors.And([self.X, constructors.Not(self.X)])),
      ef_constraint = gen_ef_constraint(factor.left_variance(True))))
    self.assertEqual(2, len(results))
    self.assertEqual(results[0], self.X.value)
    self.assertEqual(results[1], self.X.value)

  def test_replace(self):
    x = self.exists_([self.b], constructors.And([self.W, self.Z]))
    results = list(factor.formula_match(
      formula = x,
      formula_constraint = factor.formula_replace(
        formula_constraint = factor.apply(
          formula_constraint = factor.exact(self.X),
          ef_constraint = factor.variance(True),
          f = lambda formula, a, b: a),
        covariant = False,
        allowed_variables = [self.c],
        f = lambda original, arrow, substitutions, y: (y, original, substitutions))))
    self.assertEqual(1, len(results))
    y, original, substitutions = results[0]
    self.assertEqual(y, self.X)
    self.assertEqual(original, x)
    self.assertEqual(substitutions, [(self.b, self.c)])

  def test_replace_with_unallowed_variables(self):
    results = list(factor.formula_match(
      formula = self.exists_([self.b], constructors.And([self.W, self.Z])),
      formula_constraint = factor.formula_replace(
        formula_constraint = factor.apply(
          formula_constraint = factor.exact(self.X),
          ef_constraint = factor.variance(True),
          f = lambda formula, a, b: a),
        covariant = False,
        allowed_variables = [self.a],
        f = lambda original, arrow, substitutions, y: y)))
    self.assertEqual(0, len(results))

  def test_replace_within_not(self):
    x = constructors.Not(self.exists_([self.b], constructors.And([self.W, self.Z])))
    results = list(factor.formula_match(
      formula = x,
      formula_constraint = factor.formula_replace(
        formula_constraint = factor.apply(
          formula_constraint = factor.exact(self.X),
          ef_constraint = factor.variance(False),
          f = lambda formula, a, b: a),
        covariant = True,
        allowed_variables = [self.c],
        f = lambda original, arrow, substitutions, y: (y, arrow))))
    self.assertEqual(1, len(results))
    y, arrow = results[0]
    self.assertEqual(arrow.src, x)
    self.assertEqual(arrow.tgt,
        constructors.Not(constructors.And([self.X, self.Z])))
    self.assertEqual(y, self.X)

  def test_replace_bounded(self):
    x = constructors.Not(constructors.Exists(
        [constructors.BoundedVariableBinding(self.b, self.x)],
        constructors.And([self.W, self.Z])))
    results = list(factor.formula_match(
      formula = x,
      formula_constraint = factor.formula_replace(
        formula_constraint = factor.apply(
          formula_constraint = factor.exact(self.X),
          ef_constraint = factor.variance(False),
          f = lambda formula, a, b: a),
        covariant = True,
        allowed_variables = [self.c],
        f = lambda original, arrow, substitutions, y: arrow)))
    self.assertEqual(1, len(results))
    arrow = results[0]
    self.assertEqual(arrow.src, x)


def suite():
  return unittest.makeSuite(FactorTest)
