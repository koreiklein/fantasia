# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>


import unittest
from calculus.enriched import endofunctor, bifunctor, formula, constructors, spec
from calculus import variable
from lib import common_vars
from tests.lowlevel.common_enriched_objects import CommonObjects

class AbstractSearchTest(unittest.TestCase):
  def assert_exact_search_fails(self, functor, claim):
    self.assert_exact_search_succeeds(functor = functor, claim = claim, intended_result = [])

  def assert_exact_search_succeeds_once(self, functor, claim):
    self.assert_exact_search_succeeds(functor = functor, claim = claim, intended_result = [claim])

  def assert_exact_search_succeeds(self, functor, claim, intended_result):
    result = functor.search(spec.equal_translates_search_spec(claim))
    self.assertEqual(intended_result, result)

class SearchTest(AbstractSearchTest, CommonObjects):
  def setUp(self):
    self.add_common_objects()

  def test_search_and(self):
    self.assert_exact_search_succeeds_once(self.and_W, self.W)
    self.assert_exact_search_succeeds_once(self.W_and, self.W)
    self.assert_exact_search_succeeds_once(self.X_and_and_Y, self.X)
    self.assert_exact_search_succeeds_once(self.X_and_and_Y, self.Y)

  def test_search_and_fails(self):
    self.assert_exact_search_fails(self.X_and_and_Y, self.W)
    self.assert_exact_search_fails(self.and_W, self.X)

  def test_search_composite(self):
    self.assert_exact_search_succeeds_once(self.W_and.compose(self.X_and_and_Y), self.W)
    self.assert_exact_search_succeeds_once(self.W_and.compose(self.X_and_and_Y), self.X)
    self.assert_exact_search_succeeds_once(self.W_and.compose(self.X_and_and_Y), self.Y)

class AbstractTransportTest(unittest.TestCase):
  def assertEnrichedEqual(self, a, b):
    self.assertEqual(a.translate(), b.translate())

  def assert_transport_duplicating_succeeds(self, bifunctor, right, transported):
    src = bifunctor.onObjects(left = transported, right = right)
    tgt = bifunctor.onObjects(left = transported,
        right = constructors.And([transported, right]))
    nt = bifunctor.transport_duplicating(transported)
    arrow = nt(right)
    self.assertEnrichedEqual(src, arrow.src)
    self.assertEnrichedEqual(tgt, arrow.tgt)

  def assert_standard_transport_succeeds(self, bifunctor):
    self.assert_transport_duplicating_succeeds(bifunctor = bifunctor,
        right = self.A, transported = self.B)

class TransportTest(AbstractTransportTest, CommonObjects):
  def setUp(self):
    self.add_common_objects()

  def test_empty_and(self):
    self.assert_standard_transport_succeeds(
        bifunctor = bifunctor.And(values = [], leftIndex = 0, rightIndex = 1))
    self.assert_standard_transport_succeeds(
        bifunctor = bifunctor.And(values = [], leftIndex = 0, rightIndex = 0))

  def test_transport_front_of_large_and(self):
    self.assert_standard_transport_succeeds(
        bifunctor = bifunctor.And(values = [self.W], leftIndex = 0, rightIndex = 1))
    self.assert_standard_transport_succeeds(
        bifunctor = bifunctor.And(values = [self.W, self.X], leftIndex = 0, rightIndex = 1))
    self.assert_standard_transport_succeeds(
        bifunctor = bifunctor.And(values = [self.W, self.X, self.Y, self.Z],
          leftIndex = 0, rightIndex = 1))

  def test_transport_back_of_large_and(self):
    values = [self.W]
    self.assert_standard_transport_succeeds(
        bifunctor = bifunctor.And(values = values, leftIndex = len(values),
          rightIndex = len(values) + 1))
    self.assert_standard_transport_succeeds(
        bifunctor = bifunctor.And(values = values, leftIndex = len(values),
          rightIndex = len(values)))
    values.append(self.X)
    values.append(self.Y)
    values.append(self.Z)
    self.assert_standard_transport_succeeds(
        bifunctor = bifunctor.And(values = values, leftIndex = len(values),
          rightIndex = len(values) + 1))
    self.assert_standard_transport_succeeds(
        bifunctor = bifunctor.And(values = values, leftIndex = len(values),
          rightIndex = len(values)))

  def test_transport_back_of_large_and(self):
    values = [self.W, self.X, self.Y, self.Z]
    indices = [(4, 0), (1, 3), (2, 0), (3, 3), (4, 2), (2, 5)]
    for leftIndex, rightIndex in indices:
      self.assert_standard_transport_succeeds(
          bifunctor = bifunctor.And(values = values, leftIndex = leftIndex,
            rightIndex = rightIndex))
    self.assertRaises(Exception,
      self.assert_standard_transport_succeeds(
          bifunctor = bifunctor.And(values = values, leftIndex = 5,
            rightIndex = 2)))

  def test_transport_nested_ands(self):
    values = [self.W, self.X]
    inner_values = [self.Y, self.Z]
    f = bifunctor.And(values = values, leftIndex = 2, rightIndex = 1).precomposeLeft(
        endofunctor.And(values = inner_values, index = 1))
    self.assert_standard_transport_succeeds(bifunctor = f)

  def test_transport_doubly_nested_ands(self):
    values = [self.W, self.X]
    inner_values0 = [self.W, self.Z]
    inner_values1 = [self.X, self.Y]
    f = bifunctor.And(values = values, leftIndex = 2, rightIndex = 1).precompose(
        left = endofunctor.And(values = inner_values0, index = 1),
        right = endofunctor.And(values = inner_values1, index = 2))
    self.assert_standard_transport_succeeds(bifunctor = f)

  def test_transport_nested_and_or(self):
    values = [self.W, self.X]
    inner_values0 = [self.W, self.Z]
    inner_values1 = [self.X, self.Y]
    f_and = endofunctor.And(values = inner_values0, index = 1)
    f_or = endofunctor.Or(values = inner_values1, index = 2)
    f = bifunctor.And(values = values, leftIndex = 2, rightIndex = 1).precompose(
        left = f_and,
        right = f_or)
    self.assert_standard_transport_succeeds(bifunctor = f)

    f_broken = bifunctor.And(values = values, leftIndex = 2, rightIndex = 1).precompose(
        right = f_and,
        left = f_or)
    self.assertRaises(bifunctor.UntransportableException,
        self.assert_standard_transport_succeeds, bifunctor = f_broken)

  def test_transport_not_or_not(self):
    values = [self.W, self.X]
    inner_values0 = [self.W, self.Z]
    inner_values1 = [self.X, self.Y]
    f_and = endofunctor.And(values = inner_values0, index = 1)
    f_not_or_not = endofunctor.not_functor.compose(
        endofunctor.Or(values = inner_values1, index = 2)).compose(
            endofunctor.not_functor)
    f = bifunctor.And(values = values, leftIndex = 2, rightIndex = 1).precompose(
        left = f_and,
        right = f_not_or_not)
    self.assert_standard_transport_succeeds(bifunctor = f)

    f_broken = bifunctor.And(values = values, leftIndex = 2, rightIndex = 1).precompose(
        right = f_and,
        left = f_not_or_not)
    self.assertRaises(bifunctor.UntransportableException,
        self.assert_standard_transport_succeeds, bifunctor = f_broken)

  def test_transport_ordinary_exists(self):
    values = [self.W, self.X]
    left = self.exists_d
    right = self.exists_e
    self.assert_standard_transport_succeeds(
        bifunctor = bifunctor.And(values, leftIndex = 2, rightIndex = 1).precompose(
          left = left, right = right))

  def test_multi_ordinary_exists(self):
    values = [self.W, self.X]
    left = self.exists_d_e
    self.assert_standard_transport_succeeds(
        bifunctor = bifunctor.And(values, leftIndex = 2, rightIndex = 1).precomposeLeft(
          left = left))

def suite():
  return unittest.TestSuite( [ unittest.makeSuite(TransportTest)
                             , unittest.makeSuite(SearchTest)
                             ])
