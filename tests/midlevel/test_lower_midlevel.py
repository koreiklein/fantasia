# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import unittest

from tests.lowlevel import common_enriched_objects

from midlevel import lower
from calculus.enriched import endofunctor, constructors

class LowerTest(unittest.TestCase, common_enriched_objects.CommonObjects):
  def setUp(self):
    self.add_common_objects()

  def assert_full_absorb(self, x, f, g):
    tag, result = lower.absorb(x, f, g)
    self.assertEqual('full', tag)
    self.assertEqual(result.src, g.onObject(f.onObject(x)))
    self.assertEqual(result.tgt, g.onObject(x))

  def assert_partial_absorb(self, x, f, g, expected_f):
    tag, result = lower.absorb(x, f, g)
    self.assertEqual('partial', tag)
    a, e, i = result
    self.assertEqual(a.src, g.onObject(f.onObject(x)))
    self.assertEqual(a.tgt, g.onObject(expected_f.onObject(x)))

  def assert_no_absorb(self, x, f, g):
    tag, result = lower.absorb(x, f, g)
    self.assertEqual('none', tag)
    self.assertTrue(result is None)

  # Covariant absorb is a degenerate form of absorb, but it should still work.
  def test_covariant_absorb(self):
    for g in [ endofunctor.identity_functor
             , endofunctor.not_functor.compose(endofunctor.not_functor)
             , self.and_W, self.X_and_and_Y, self.exists_d ]:
      for f in [self.and_W, self.W_and, self._and(self.if_W_then_X)]:
        for x in [self.X, self.Y]:
          self.assert_full_absorb(x, f, g)

  def test_absorb_once(self):
    for g in [ endofunctor.not_functor.compose(self.and_W)
             , endofunctor.not_functor.compose(self.W_and)
             , self.and_W.compose(endofunctor.not_functor)
             , self.and_X.compose(endofunctor.not_functor).compose(self.and_W) ]:
      for f in [self.and_W, self.W_and]:
        for x in [self.Y, self.Z]:
          self.assert_full_absorb(x, f, g)

  def test_absorb_twice(self):
    l = [self.and_X, self.and_W]
    for i in range(1 + len(l)):
      ll = list(l)
      ll.insert(i, endofunctor.not_functor)
      g = ll[0].compose(ll[1]).compose(ll[2])
      for f in [ self.and_X.compose(self.and_W)
               , self.and_W.compose(self.and_X)
               , self._and(self.W_and_X) ]:
        for x in [self.Y, self.Z]:
          self.assert_full_absorb(x, f, g)

  def test_absorb_half(self):
    l = [self.and_X, self.and_W]
    for i in range(1 + len(l)):
      ll = list(l)
      ll.insert(i, endofunctor.not_functor)
      g = ll[0].compose(ll[1]).compose(ll[2])
      for f, expected_f in [ (self.and_X.compose(self.and_Y), self.and_Y)
                           , (self.and_Y.compose(self.and_X), self.and_Y)
                           , (self.and_X.compose(
                               self.and_Y).compose(
                                 self.W_and).compose(
                                   self.Z_and), self.and_Y.compose(self.Z_and)) ]:
        for x in [self.W_or_X]:
          self.assert_partial_absorb(x, f, g, expected_f)

  def test_absorb_none(self):
    l = [self.and_X, self.and_W]
    for i in range(1 + len(l)):
      ll = list(l)
      ll.insert(i, endofunctor.not_functor)
      g = ll[0].compose(ll[1]).compose(ll[2])
      for f in [ self.and_Y, self.and_Y.compose(self.and_Y), self.exists_d ]:
        for x in [self.W_or_X, self.Z, self.W]:
          self.assert_no_absorb(x, f, g)

  def test_absorb_with_implies(self):
    and_if_Y_then_X = self._and(constructors.Always(self.if_Y_then_X))
    for g in [ self.and_Y.compose(endofunctor.not_functor).compose( and_if_Y_then_X )
             , endofunctor.not_functor.compose(self.and_Y.compose(and_if_Y_then_X))
             , endofunctor]:
      self.assert_full_absorb(
          x = self.Z,
          f = self.and_X,
          g = g)

  def test_absorb_from_bottom(self):
    and_if_Y_then_X = self._and(constructors.Always(self.if_Y_then_X))
    self.assert_full_absorb(
        x = self.Z,
        f = self.and_Z,
        g = endofunctor.identity_functor)
    self.assert_full_absorb(
        x = self.Y,
        f = self.and_X,
        g = endofunctor.not_functor.compose(and_if_Y_then_X))
    self.assert_full_absorb(
        x = constructors.Always(self.if_Y_then_X),
        f = self.and_X,
        g = endofunctor.not_functor.compose(self.Y_and))

  def test_absorb_modus_ponens(self):
    and_if_Y_then_X = self._and(constructors.Always(self.if_Y_then_X))
    and_if_Z_then_Y = self._and(constructors.Always(self.if_Z_then_Y))

    for g0, g1 in [ (and_if_Y_then_X, and_if_Z_then_Y)
                  , (and_if_Z_then_Y, and_if_Y_then_X) ]:
      self.assert_full_absorb(
          x = self.Z,
          f = self.and_X,
          g = endofunctor.not_functor.compose(
            g0.compose(endofunctor.not_functor).compose(
              g1)))

  def test_absorb_with_existentials(self):
    gs = []
    for claim in [ self._and(constructors.OrdinaryForall([self.d], self.Y))
                 , self._and(constructors.And([ constructors.OrdinaryForall([self.d], self.if_Z_then_Y)
                                    , self.Z])) ]:
      gs.append(endofunctor.not_functor.compose(claim))
    for g in gs:
      for f in [self.and_X]:
        for x in [self.W]:
          self.assert_full_absorb(x, f, g)

def suite():
  return unittest.makeSuite(LowerTest)
