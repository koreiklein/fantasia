# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from misc import *

import unittest
from calculus.basic import endofunctor, formula
from calculus.enriched import formula as enrichedFormula
from calculus import variable
from lib import common_vars
from tests.lowlevel import common_objects

class ImportTest(unittest.TestCase):
  def assert_can_import_through_covariant_functor(self, functor):
    self.assertTrue(functor.covariant())
    importedObject = formula.Always(formula.Holds(common_vars.x(), common_vars.y()))
    self.assert_exact_import_succeeds(functor, importedObject)

  def assert_exact_import_succeeds(self, functor, B):
    base = formula.true
    src = formula.And(B, functor.onObject(base))
    tgt = functor.onObject(formula.And(B, base))
    nt = functor._import(B)
    arrow = nt(base)
    self.assertEqual(src, arrow.src)
    self.assertEqual(tgt, arrow.tgt)

  def assert_import_from_succeeds(self, functor, B):
    base = formula.true
    src = functor.onObject(base)
    tgt = functor.onObject(formula.And(B, base))
    nt = functor.importExactly(B)
    arrow = nt(base)
    self.assertEqual(src, arrow.src)
    self.assertEqual(tgt, arrow.tgt)

class ExactImportTests(ImportTest, common_objects.CommonObjects):
  def setUp(self):
    self.add_common_objects()
    self.not_not_functor = endofunctor.not_functor.compose(endofunctor.not_functor)
    self.not_andBofA_not_functor = endofunctor.not_functor.compose(
        self.and_b_of_a_functor).compose(
            endofunctor.not_functor)
    # There exists a well defined a such that....
    self.well_defined_functor = enrichedFormula.ExpandWellDefined(self.a, self.b, self.equivalence)
    self.exists_well_defined_functor = enrichedFormula.ExpandWellDefined(self.c, self.d, self.equivalence).compose(
        endofunctor.Exists(self.c))
    self.well_defined_exists_functor = endofunctor.Exists(self.e).compose(
        enrichedFormula.ExpandWellDefined(self.c, self.d, self.equivalence))

    self.B = formula.Always(formula.Holds(common_vars.x(), common_vars.y()))
    self.and_B = endofunctor.And(side = left, other = self.B)

  def test_import_through_id(self):
    self.assert_can_import_through_covariant_functor(endofunctor.identity_functor)

  def test_import_through_or(self):
    self.assert_can_import_through_covariant_functor(self.or_d_of_c_functor)

  def test_import_through_or_or(self):
    self.assert_can_import_through_covariant_functor(self.or_d_of_c_functor.compose(self.or_d_of_c_functor))

  def test_import_through_or_not_not(self):
    self.assert_can_import_through_covariant_functor(self.or_d_of_c_functor.compose(self.not_not_functor))

  def test_import_through_or_and_or(self):
    self.assert_can_import_through_covariant_functor(self.or_d_of_c_functor.compose(
      self.and_b_of_a_functor).compose(self.or_d_of_c_functor))

  def test_import_not_not(self):
    self.assert_can_import_through_covariant_functor(self.not_not_functor)

  def test_import_not_not_not_not(self):
    self.assert_can_import_through_covariant_functor(self.not_not_functor.compose(self.not_not_functor))

  def test_import_middle(self):
    functor = self.not_not_functor.compose(self.and_b_of_a_functor.compose(self.not_not_functor))
    self.assert_exact_import_succeeds(functor, self.b_of_a)

  def test_import_not_andBofA_not(self):
    self.assert_can_import_through_covariant_functor(self.not_andBofA_not_functor)

  def test_import_well_defined(self):
    self.assert_can_import_through_covariant_functor(self.well_defined_functor)

  def test_import_exists_well_defined(self):
    self.assert_can_import_through_covariant_functor(self.exists_well_defined_functor)

  def test_import_well_defined_exists(self):
    self.assert_can_import_through_covariant_functor(self.well_defined_exists_functor)

  def assert_can_import_B_from(self, functor):
    self.assert_import_from_succeeds(functor = functor, B = self.B)

  def test_import_from_and(self):
    self.assert_can_import_B_from(self.and_B)

  def test_import_from_or_and(self):
    self.assert_can_import_B_from(self.or_d_of_c_functor.compose(self.and_B))

  def test_import_from_or_not_not_and(self):
    self.assert_can_import_B_from(self.or_d_of_c_functor.compose(self.not_not_functor).compose(self.and_B))
    self.assert_can_import_B_from(self.or_d_of_c_functor.compose(self.not_not_functor.compose(self.and_B)))

def suite():
  return unittest.makeSuite(ExactImportTests)

