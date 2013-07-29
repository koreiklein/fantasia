# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import unittest

from proof import proof
from examples import QR
from calculus.basic.endofunctor import UnimportableException
from calculus.enriched import constructors
from calculus.enriched.constructors import *
from lib import library, natural, common_vars

class AbstractProofTest(unittest.TestCase):
  def assert_proof_yields(self, proof, formula):
    self.assertEqual(proof.current_formula(), formula)
    arrow = proof.arrow()
    self.assertEqual(arrow.src, proof.src_formula())
    self.assertEqual(arrow.tgt, proof.tgt_formula())

  def build_lib(x):
    return library.Library(claims = [x], variables = [], sub_libraries = [QR.lib])

class SimpleProofTest(AbstractProofTest):
  def setUp(self):
    pass

  def test_instantiate_zero_zero(self):
    q = common_vars.q()
    r = common_vars.r()
    claim = natural.ForallNatural([q, r],
        natural.Less(q, r))
    reduced_claim = natural.Less(natural.zero, natural.zero)
    for q, r in [(q, r), (r, q)]:
      self.assert_natural_proof_succeeds(
          claim = claim,
          reduced_claim = reduced_claim,
          variables = [],
          build_proof = (lambda proof: (proof
            .instantiate()
              .assign(q, natural.zero)
              .assign(r, natural.zero)
            .finish())))

  def test_import_about(self):
    a = common_vars.a()
    claim = Always(Natural.Natural(a))
    imported = Or([Always(Identical(natural.zero, a)), natural.Less(natural.zero, a)])
    self.assert_natural_proof_succeeds(
        claim = claim,
        reduced_claim = And([imported, claim]),
        build_proof = (lambda proof: (proof
          .importt()
            .safe()
            .about([a])
            .involvingVariables([natural.zero, natural.natural_less])
          .finish())))

  def test_reduce_using_transitivity(self):
    a = common_vars.a()
    b = common_vars.b()
    c = common_vars.c()
    self.assert_natural_proof_succeeds(
        claim = And([ Always(Natural.Natural(a))
                    , Always(Natural.Natural(b))
                    , Always(Natural.Natural(c))
                    , Not(natural.Less(a, c))]),
        reduced_claim = And([ Always(Natural.Natural(a))
                            , Always(Natural.Natural(b))
                            , Always(Natural.Natural(c))
                            , Not(And([ natural.Less(a, b)
                                      , natural.Less(b, c)]))]),
        variables = [a, b, c],
        build_proof = lambda proof: (proof
          .down(3).down()
          .reduce()
          .finish()))

  def assert_natural_proof_succeeds(claim, reduced_claim, variables, build_proof):
    lib = library.Library(claims = [claim],
      variables = variables,
      sub_libraries = [natural.lib])
    reduced_formula = library.Library(claims = [reduced_claim],
        variables = variables,
        sub_libraries = [natural.lib]).formula()
    self.assert_proof_yields(
        proof = build_proof(proof.from_library(lib)),
        formula = reduced_formula())

class SmallQRProofsTest(AbstractProofTest):
  def setUp(self):
    QR.proof(10)
    #print QR.formulas[5].top_level_render()._backend
    startingQRProof = proof.from_library(QR.lib)

  def test_assume(self):
    self.assert_proof_yields(formula = QR.formulas[1],
        proof = self.startingQRProof.importt().specific(QR.claim).assume())

  def test_infer_fails(self):
    try:
      self.startingQRProof.importt().specific(QR.claim).infer()
      self.assertTrue(False, "startingQRProof should fail to infer the claim.")
    except UnimportableException as e:
      pass

  def test_induct(self):
    self.assert_proof_yields(formula = QR.formulas[3],
        proof = self.startingQRProof.induct().show(QR.claim, QR.a))



def suite():
  return unittest.TestSuite( [ unittest.makeSuite(SimpleProofTest)
                             , unittest.makeSuite(SmallQRProofsTest)
                             ])
