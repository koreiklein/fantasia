# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import unittest

from tests import common_objects
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
    self.standard_transported = self.b_of_a

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

def suite():
  return unittest.makeSuite(TransportTest)
