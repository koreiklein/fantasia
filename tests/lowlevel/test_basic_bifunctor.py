# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import unittest

from tests.lowlevel import common_objects
from calculus.basic import endofunctor, formula, bifunctor

class AbstractTransportTest(unittest.TestCase):
  def assert_transport_succeeds(self, bifunctor, left, right, transported):
    src = bifunctor.onObjects(formula.And(transported, left), right)
    tgt = bifunctor.onObjects(left, formula.And(transported, right))
    nt = bifunctor.transport(transported)
    arrow = nt(left, right)
    self.assertEqual(src, arrow.src)
    self.assertEqual(tgt, arrow.tgt)

  def assert_transport_duplicating_succeeds(self, bifunctor, right, transported):
    src = bifunctor.onObjects(transported, right)
    tgt = bifunctor.onObjects(transported, formula.And(transported, right))
    nt = bifunctor.transport_duplicating(transported)
    arrow = nt(right)
    self.assertEqual(src, arrow.src)
    self.assertEqual(tgt, arrow.tgt)

class AbstractStandardTransportTest(AbstractTransportTest, common_objects.CommonObjects):
  def setUp(self):
    self.add_common_objects()
    self.standard_left = self.a_of_b
    self.standard_right = self.d_of_c
    self.standard_transported = self.e_of_e

  def assert_standard_transport_succeeds(self, bifunctor):
    self.assert_transport_succeeds(bifunctor = bifunctor,
        left = self.standard_left,
        right = self.standard_right,
        transported = self.standard_transported)

  def assert_standard_transport_duplicating_succeeds(self, bifunctor):
    self.assert_transport_duplicating_succeeds(bifunctor = bifunctor,
        right = self.standard_right,
        transported = self.standard_transported)

  def assert_bifunctor_transports_correctly(self, bifunctor):
    self.assert_standard_transport_succeeds(bifunctor)
    self.assert_standard_transport_duplicating_succeeds(bifunctor)

class TransportTest(AbstractStandardTransportTest):
  def test_and(self):
    self.assert_bifunctor_transports_correctly(bifunctor.and_functor)

  # check that the composites And(left(.), right(.))
  # and after(And(left(.), right(.))) transport correctly.
  def check_composite(self,
      left = endofunctor.identity_functor,
      right = endofunctor.identity_functor,
      after = endofunctor.identity_functor):
    b = bifunctor.and_functor.precompose(left = left, right = right)
    self.assert_bifunctor_transports_correctly(b)
    d = b.compose(after)
    self.assert_bifunctor_transports_correctly(d)

  def test_and_left(self):
    self.check_composite(left = self.and_b_of_a_functor)
    self.check_composite(left = self.b_of_a_and_functor)
    self.check_composite(left = self.b_of_a_and_functor, after = self.and_b_of_a_functor)

  def test_and_right(self):
    self.check_composite(right = self.and_b_of_a_functor)
    self.check_composite(right = self.b_of_a_and_functor)

  def test_and_left_right(self):
    self.check_composite(left = self.and_b_of_a_functor, right = self.and_b_of_a_functor)
    self.check_composite(left = self.and_b_of_a_functor, right = self.b_of_a_and_functor)
    self.check_composite(left = self.b_of_a_and_functor, right = self.and_b_of_a_functor)
    self.check_composite(left = self.b_of_a_and_functor, right = self.b_of_a_and_functor)

  def test_or_right(self):
    self.check_composite(right = self.or_d_of_c_functor)
    self.check_composite(right = self.d_of_c_or_functor)

  def test_or_left(self):
    self.assertRaises(bifunctor.UntransportableException,
        self.check_composite, left = self.or_d_of_c_functor)
    self.assertRaises(bifunctor.UntransportableException,
        self.check_composite, left = self.d_of_c_or_functor)

  def test_or_both(self):
    self.assertRaises(bifunctor.UntransportableException,
        self.check_composite, right = self.or_d_of_c_functor, left = self.or_d_of_c_functor)
    self.assertRaises(bifunctor.UntransportableException,
        self.check_composite, right = self.or_d_of_c_functor, left = self.d_of_c_or_functor)
    self.assertRaises(bifunctor.UntransportableException,
        self.check_composite, right = self.or_d_of_c_functor, left = self.d_of_c_or_functor,
        after = self.and_b_of_a_functor)

  def test_or_and(self):
    self.check_composite(left = self.and_b_of_a_functor, right = self.or_d_of_c_functor)
    self.check_composite(left = self.and_b_of_a_functor, right = self.or_d_of_c_functor,
        after = self.b_of_a_and_functor)
    self.assertRaises(bifunctor.UntransportableException,
        self.check_composite, left = self.or_d_of_c_functor, right = self.and_b_of_a_functor)

  def test_deep_and_or(self):
    self.check_composite(left = self.and_b_of_a_functor.compose(self.and_b_of_a_functor))
    self.check_composite(left = self.and_b_of_a_functor.compose(self.b_of_a_and_functor))
    self.check_composite(left = self.and_b_of_a_functor.compose(self.b_of_a_and_functor),
        right = self.d_of_c_or_functor.compose(self.or_d_of_c_functor))

    self.check_composite(left = self.and_b_of_a_functor.compose(self.b_of_a_and_functor),
        right = self.d_of_c_or_functor.compose(self.or_d_of_c_functor),
        after = self.b_of_a_and_functor.compose(self.and_b_of_a_functor))

  def test_not_not(self):
    self.check_composite(right = self.not_not_functor)
    self.assertRaises(bifunctor.UntransportableException,
        self.check_composite, left = self.not_not_functor)

  def test_deep_and_not_not(self):
    self.check_composite(left = self.and_b_of_a_functor.compose(self.b_of_a_and_functor),
      right = self.not_not_functor)

  def test_exists(self):
    self.check_composite(left = self.exists_d_functor)

  def test_multiple_exists(self):
    self.check_composite(left = self.exists_d_functor,
        right = self.exists_c_functor)

    self.check_composite(left = self.exists_d_functor,
        right = self.exists_c_functor.compose(self.exists_a_functor))

    self.check_composite(left = self.exists_d_functor,
        right = self.exists_c_functor.compose(self.exists_a_functor),
        after = self.exists_b_functor)

def suite():
  return unittest.makeSuite(TransportTest)
