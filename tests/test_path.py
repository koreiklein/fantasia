# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>


import unittest
from calculus import variable
from calculus.enriched import path, constructors, formula, spec
from lib import common_vars
from tests.common_enriched_objects import CommonObjects

class AbstractPathSearchTest(unittest.TestCase):
  # assert that the paths a and b are equal.
  def assertEqualPaths(self, a, b):
    self.assertEqual(a.top().translate(), b.top().translate())
    self.assertEqual(a.bottom().translate(), b.bottom().translate())

  # Perform sanity checks on a path arrow.
  def assertValidPathArrow(self, arrow):
    src_path = arrow.src
    tgt_path = arrow.tgt

    src_enriched_formula = arrow.enrichedArrow.src
    tgt_enriched_formula = arrow.enrichedArrow.tgt

    src_basic_formula = arrow.enrichedArrow.basicArrow.src
    tgt_basic_formula = arrow.enrichedArrow.basicArrow.tgt

    self.assertEqual(src_path.top().translate(), src_enriched_formula.translate())
    self.assertEqual(tgt_path.top().translate(), tgt_enriched_formula.translate())

    self.assertEqual(src_enriched_formula.translate(), src_basic_formula)
    self.assertEqual(tgt_enriched_formula.translate(), tgt_basic_formula)

  def assert_path_search_succeeds(self, src_path, search_spec, number):
    result = src_path.search(search_spec)
    self.assertEqual(number, len(result))
    for B, f in result:
      self.assertTrue(search_spec.valid(B))
      path_arrow = f()
      self.assertEqualPaths(src_path, path_arrow.src)
      tgt_path = path.Path(formula = formula.And([B, src_path.formula]),
          endofunctor = src_path.endofunctor)
      self.assertEqualPaths(tgt_path, path_arrow.tgt)

      self.assertValidPathArrow(path_arrow)

  def assert_exact_path_search_fails(self, src_path, formula):
    self.assert_path_search_succeeds(src_path = src_path,
        search_spec = spec.equal_translates_search_spec(formula),
        number = 0)

  def assert_exact_path_search_succeeds_once(self, src_path, formula):
    self.assert_path_search_succeeds(src_path = src_path,
        search_spec = spec.equal_translates_search_spec(formula),
        number = 1)

class PathSearchTest(AbstractPathSearchTest, CommonObjects):
  def setUp(self):
    self.add_common_objects()
    self.P0 = path.new_path(self.W_AND_X_and_Y_and_Z)
    self.P1 = self.P0.advance(0).tgt
    self.P2 = self.P0.advance(1).tgt.advance().tgt.advance(1).tgt

    self.EP0 = path.new_path(self.exists_a_in_domain_b_X_and_Y_and_Z)
    self.EP1 = self.EP0.advance().tgt.advance().tgt.advance(1).tgt

    self.WDEP0 = path.new_path(formula.And([self.B, self.exists_wd_a_in_domain_b_X_and_Y_and_Z]))
    self.WDEP1 = self.WDEP0.advance(1).tgt.advance().tgt.advance().tgt.advance(1).tgt

  def test_search_P1(self):
    self.assert_exact_path_search_succeeds_once(src_path = self.P1,
        formula = self.X_and_Y_and_Z)

  def test_search_P2(self):
    self.assert_exact_path_search_succeeds_once(src_path = self.P2,
        formula = self.W)

  def test_search_bounded_exists(self):
    self.assert_exact_path_search_succeeds_once(src_path = self.EP1,
        formula = self.a_in_domain_b)

  def test_search_past_wd_exists(self):
    self.assert_exact_path_search_succeeds_once(src_path = self.WDEP1,
        formula = self.B)

def suite():
  return unittest.makeSuite(PathSearchTest)
