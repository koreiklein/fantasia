# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import unittest
from calculus import basicPath as path
from calculus import basic
from lib import common_vars

class CommonObjects:
  def add_common_objects(self):
    self.a = common_vars.a()
    self.b = common_vars.b()
    self.c = common_vars.c()
    self.d = common_vars.d()
    self.e = common_vars.e()
    self.b_of_a = basic.Always(basic.Holds(self.a, self.b))
    self.a_of_b = basic.Always(basic.Holds(self.b, self.a))
    self.a_of_a = basic.Always(basic.Holds(self.a, self.a))
    self.b_of_c = basic.Always(basic.Holds(self.c, self.b))
    self.d_of_c = basic.Always(basic.Holds(self.c, self.d))
    self.and_b_of_a_functor = path.And(side=path.left,
                                       other=self.b_of_a)
    self.or_d_of_c_functor = path.Or(side=path.left,
                                     other=self.d_of_c)
    self.exists_a_functor = path.Exists(variable=self.a)
    self.exists_b_functor = path.Exists(variable=self.b)
    self.exists_c_functor = path.Exists(variable=self.c)
    self.exists_d_functor = path.Exists(variable=self.d)
    self.equivalence = basic.StringVariable('equiv')

class ImportTest(unittest.TestCase):
  def assert_can_import_through_covariant_functor(self, functor):
    self.assertTrue(functor.covariant())
    importedObject = basic.Always(basic.Holds(common_vars.x(), common_vars.y()))
    self.assert_exact_import_succeeds(functor.compose(path.And(side = path.left, other=importedObject)),
                                      importedObject)

  def assert_exact_import_succeeds(self, functor, importedObject):
    path0 = path.Path(functor=functor, object=basic.true)
    pairs = path0.importFilteredArrow(lambda x: x == importedObject)
    self.assertEqual(1, len(pairs), "Should import exactly one claim.")
    (B, A) = pairs[0]
    self.assertEqual(B, importedObject, "Imported the wrong claim.")
    self.assertEqual(A.src, path0, "path.importFilteredArrow returned an arrow whose src was not path.")
    self.assertEqual(A.tgt, path.Path(functor=functor,
                                      object = basic.And(importedObject, basic.true)))

class ExactImportTests(ImportTest, CommonObjects):
  def setUp(self):
    self.add_common_objects()
    self.not_not_functor = path.not_functor.compose(path.not_functor)
    self.not_andBofA_not_functor = path.not_functor.compose(
        self.and_b_of_a_functor).compose(
            path.not_functor)
    # There exists a well defined a such that....
    self.well_defined_functor = path.WellDefined(self.a, self.b, self.equivalence)
    self.exists_well_defined_functor = path.WellDefined(self.c, self.d, self.equivalence).compose(
        path.Exists(self.c))
    self.well_defined_exists_functor = path.Exists(self.e).compose(
        path.WellDefined(self.c, self.d, self.equivalence))

  def test_import_through_id(self):
    self.assert_can_import_through_covariant_functor(path.identity_functor)

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

class UniversalInTest(unittest.TestCase, CommonObjects):
  def setUp(self):
    self.add_common_objects()
    self.exists_a_forall_b__a_of_b = basic.MultiExists([self.a],
        basic.MultiForall([self.b],
          self.a_of_b))
    self.path = path.new_path(self.exists_a_forall_b__a_of_b).advance().tgt

  def test_one_variable_no_bounds(self):
    post_import = basic.MultiExists([self.a],
        basic.Always(basic.And(self.a_of_a, basic.MultiForall([self.b], self.a_of_b))))
    importables = self.path.importables_universalIn([self.a])
    self.assertEqual(1, len(importables), "Failed to import the valid universal claim.")
    self.assertEqual(importables[0], self.a_of_a)
