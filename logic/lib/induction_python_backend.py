# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from logic import linear, linear_python_backend, linear_example, linearui_backend_utils
from logic.lib import induction, natural_python_backend

def _f(base, middle):
  def _g(k):
    cur = base
    for i in range(k):
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
    return cur
  return (lambda ((one, notNotK), notClaimK): notNotK(lambda k:
      notClaimK(_g(k))))

inductionRep = (lambda (((one, notNotBase), middle), cont):
  notNotBase(lambda base: cont(_f(base, middle))))

starting_claimRep = linearui_backend_utils.repAnd(
    [ natural_python_backend.increasingRep
    , inductionRep
    , natural_python_backend.successorExistsRep
    , natural_python_backend.transitivityRep
    , natural_python_backend.weakeningRep
    , natural_python_backend.reflexivityRep
    , natural_python_backend.zero_naturalRep ])

sRep = linearui_backend_utils.repAnd(
    [starting_claimRep, natural_python_backend.exists_fiveRep])

def test():
  tProgramTransformation = linear_python_backend.curry_howard(induction.t.translate())
  ending_claimRep = tProgramTransformation(sRep)

  print "ending claim is:"
  print ending_claimRep
