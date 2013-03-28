# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from extraction.python import utils

# Defining the representations of things:
# rep(Natural(x))     =    a python integer x
# rep(Equal(a, b)     =    the string "=="
# rep(Successor(a, b) =    the string "successor"

eqIdentityRep = (lambda ((one, assumptions), conclusions):
    assumptions(lambda n:
      conclusions("==")))

eqSymmetricRep = (lambda ((one, assumptions), conclusions):
    assumptions(lambda nEqualm:
      conclusions("==")))

eqTransitiveRep = (lambda (((one, assumeAisB), assumeBisC), conclusions):
    assumeAisB(lambda aEqualb:
      assumeBisC(lambda bEqualc:
        conclusions("=="))))

def _testNaturalEquality(n, m):
  assert(n.__class__ == int)
  assert(m.__class__ == int)
  if n == m:
    return (0, (1, "==")) # First clause
  else:
    def _notEqual(equal):
      raise Exception("We should not have been able to conclude that n and m were equal.")
    return (1, _notEqual) # Second clause

eqDiscreteRep = (lambda (((one, assumeN), assumeM), conclusions):
    assumeN(lambda n:
      assumeM(lambda m:
        conclusions(_testNaturalEquality(n, m)))))

eqClaimsRep = utils.repAnd([eqIdentityRep, eqSymmetricRep, eqTransitiveRep, eqDiscreteRep])

zeroIsNaturalRep = 0

successorExistsRep = (lambda ((one, assumptions), conclusions):
    assumptions(lambda n:
      conclusions( ((1, n + 1), "successor") )))

successorUniqueRep = (lambda (((one, assumeAthenN), assumeAthenM), conclusions):
    assumeAthenN(lambda AthenN:
      assumeAthenM(lambda AthenM:
        conclusions("=="))))

successorInjectiveRep = (lambda (((one, assumeNthenB), assumeMthenB), conclusions):
    assumeNthenB(lambda NthenB:
      assumeMthenB(lambda MthenB:
        conclusions("=="))))

def successorNotZeroRep(NthenZero):
  raise Exception("The successor of a natural number N can not be zero")


successorClaimsRep = utils.repAnd(
    [successorExistsRep, successorUniqueRep, successorInjectiveRep, successorNotZeroRep])

def _f(base, middle):
  def _g(k):
    def _u(cur):
      def _h(i):
        def r( (((one, notnotIP1), notnotS), notnotClaimIP1) ):
          assert(1 == one)
          def _r1(IP1):
            assert(i + 1 == IP1)
            def _r2(S):
              assert(S.small == i)
              assert(S.big == IP1)
              def _r3(ClaimIP1):
                return ClaimIP1
              return notnotClaimIP1(_r3)
            return notnotS(_r2)
          return notnotIP1(_r1)
        cur = middle(  (((1, i), cur), r) )
      for i in range(k):
        _h(i)
      return cur
    return _u(base)
  return (lambda ((one, notNotK), notClaimK): notNotK(lambda k:
      notClaimK(_g(k))))

allInductionRep = (lambda (((one, notNotBase), middle), cont):
  notNotBase(lambda base: cont(_f(base, middle))))

startingFormulaRep = utils.repAnd([ zeroIsNaturalRep
                                  , eqClaimsRep
                                  , successorClaimsRep
                                  , allInductionRep ])


