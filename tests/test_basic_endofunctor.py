# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import unittest
from calculus.basic import endofunctor, formula
from calculus import variable
from lib import common_vars

class CommonObjects:
  def add_common_objects(self):
    self.a = common_vars.a()
    self.b = common_vars.b()
    self.c = common_vars.c()
    self.d = common_vars.d()
    self.e = common_vars.e()
    self.b_of_a = formula.Always(formula.Holds(self.a, self.b))
    self.a_of_b = formula.Always(formula.Holds(self.b, self.a))
    self.a_of_a = formula.Always(formula.Holds(self.a, self.a))
    self.b_of_c = formula.Always(formula.Holds(self.c, self.b))
    self.d_of_c = formula.Always(formula.Holds(self.c, self.d))
    self.and_b_of_a_functor = endofunctor.And(side=endofunctor.left,
                                       other=self.b_of_a)
    self.or_d_of_c_functor = endofunctor.Or(side=endofunctor.left,
                                     other=self.d_of_c)
    self.exists_a_functor = endofunctor.Exists(variable=self.a)
    self.exists_b_functor = endofunctor.Exists(variable=self.b)
    self.exists_c_functor = endofunctor.Exists(variable=self.c)
    self.exists_d_functor = endofunctor.Exists(variable=self.d)
    self.equivalence = variable.StringVariable('equiv')

class ImportTest(unittest.TestCase):
  def assert_can_import_through_covariant_functor(self, functor):
    self.assertTrue(functor.covariant())
    importedObject = formula.Always(formula.Holds(common_vars.x(), common_vars.y()))
    self.assert_exact_import_succeeds(functor.compose(endofunctor.And(side = endofunctor.left, other=importedObject)),
                                      importedObject)

  def assert_exact_import_succeeds(self, functor, B):
    base = formula.true
    src = formula.And(B, functor.onObject(base))
    tgt = functor.onObject(formula.And(B, base))
    nt = functor._import(B)
    arrow = nt(base)
    self.assertEqual(src, arrow.src)
    self.assertEqual(tgt, arrow.tgt)

class ExactImportTests(ImportTest, CommonObjects):
  def setUp(self):
    self.add_common_objects()
    self.not_not_functor = endofunctor.not_functor.compose(endofunctor.not_functor)
    self.not_andBofA_not_functor = endofunctor.not_functor.compose(
        self.and_b_of_a_functor).compose(
            endofunctor.not_functor)
    # There exists a well defined a such that....
    self.well_defined_functor = endofunctor.WellDefined(self.a, self.b, self.equivalence)
    self.exists_well_defined_functor = endofunctor.WellDefined(self.c, self.d, self.equivalence).compose(
        endofunctor.Exists(self.c))
    self.well_defined_exists_functor = endofunctor.Exists(self.e).compose(
        endofunctor.WellDefined(self.c, self.d, self.equivalence))

  def test_import_through_id(self):
    self.assert_can_import_through_covariant_functor(endofunctor.identity_functor)

  def test_import_through_or(self):
    self.assert_can_import_through_covariant_functor(self.or_d_of_c_functor)

  def test_import_through_or_or(self):
    self.assert_can_import_through_covariant_functor(self.or_d_of_c_functor.compose(self.or_d_of_c_functor))

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

