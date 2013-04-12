# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic, enriched, relation, variable, datum, symbol
from lib import common_vars

from sets import Set

natural = variable.StringVariable('N')

natural_less = variable.StringVariable('<')
smaller = variable.StringVariable('smaller')
greater = variable.StringVariable('greater')

natural_successor = variable.StringVariable('S')
before = variable.StringVariable('before')
after = variable.StringVariable('after')

natural_equal = variable.StringVariable('=')
leftSymbol = symbol.StringSymbol('left')
rightSymbol = symbol.StringSymbol('right')

def Natural(n):
  return relation.Holds(natural, datum.Variable(n))

def Equal(a, b):
  return relation.Holds(natural_equal, datum.Record([ (leftSymbol, datum.Variable(a))
                                                    , (rightSymbol, datum.Variable(b))]))

def Successor(a, b):
  return relation.Holds(natural_successor, datum.Record([ (before, datum.Variable(a))
                                                        , (after, datum.Variable(b))]))

def Less(a, b):
  return relation.Holds(natural_less, datum.Record([ (smaller, datum.Variable(a))
                                                   , (greater, datum.Variable(b))]))

n = common_vars.n()
eqIdentitiy = enriched.Forall([n],
    enriched.Implies(
      predicate = Natural(n),
      consequent = Equal(n, n)))


n = common_vars.n()
m = common_vars.m()
eqSymmetric = enriched.Forall([n, m],
    enriched.Implies(
      predicate = Equal(n, m),
      consequent = Equal(m, n)))

a = common_vars.a()
b = common_vars.b()
c = common_vars.c()
eqTransitive = enriched.Forall([a, b, c],
    enriched.Implies(
      predicate = enriched.And([Equal(a, b), Equal(b, c)]),
      consequent = Equal(a, c)))

n = common_vars.n()
m = common_vars.m()
eqDiscrete = enriched.Forall([n, m],
    enriched.Implies(
      predicate = enriched.And([Natural(n), Natural(m)]),
      consequent = enriched.Or([Equal(n,m), Equal(n, m).transpose()])))

eqClaims = [eqIdentitiy, eqSymmetric, eqTransitive, eqDiscrete]

zero = variable.StringVariable('zero')

zeroIsNatural = Natural(zero)

n = common_vars.n()
m = common_vars.m()
successorExists = enriched.Forall([n],
    enriched.Implies(
      predicate = Natural(n),
      consequent = enriched.Exists([m],
        enriched.And([Natural(m), Successor(n, m)]))))

a = common_vars.a()
n = common_vars.n()
m = common_vars.m()
successorUnique = enriched.Forall([a, n, m],
    enriched.Implies(
      predicate = enriched.And([ Successor(a, n), Successor(a, m) ]),
      consequent = Equal(n, m)))

b = common_vars.b()
n = common_vars.n()
m = common_vars.m()
successorInjective = enriched.Forall([b, n, m],
    enriched.Implies(
      predicate = enriched.And([ Successor(n, b), Successor(m, b) ]),
      consequent = Equal(n, m)))

n = common_vars.n()
successorNotZero = enriched.Forall([n],
    enriched.Not(Successor(n, zero)))

def byInduction(claim):
  n = common_vars.n()
  m = common_vars.m()
  k = common_vars.k()
  return enriched.Implies(
      predicate = enriched.And([ claim(zero)
                               , enriched.Forall([n]
                               , enriched.Implies(
                                  predicate = enriched.And([ Natural(n)
                                                           , claim(n)]),
                                  consequent =
                                    enriched.Exists([m],
                                      enriched.And([ Natural(m)
                                                   , Successor(n, m)
                                                   , claim(m)]))))]),
      consequent = enriched.Forall([k],
        enriched.Implies(
          predicate = Natural(k),
          consequent = claim(k))))

successorClaims = [successorExists, successorUnique, successorInjective, successorNotZero]

R = common_vars.R()
allInduction = enriched.Forall([R],
    byInduction(lambda v: relation.Holds(holding = R, held = datum.Variable(v))))

startingFormula = enriched.And([ zeroIsNatural
                               , enriched.And(eqClaims)
                               , enriched.And(successorClaims)
                               , allInduction])

# This is the formula for which extraction engines must give an implementation.
startingFormula = enriched.And([ zeroIsNatural
                               , enriched.And(eqClaims)
                               , enriched.And(successorClaims)
                               , allInduction])

n = common_vars.n()
m = common_vars.m()
t = common_vars.t()
lessVar = common_vars.less()

defLessArrow = enriched.true.forwardIntroduceQuantifier(type = basic.forallType,
        variables = [n, m]).forwardFollow(lambda x:
            x.forwardOnBodyFollow(lambda x:
              x.forwardSingleton(enriched.parType).forwardFollow(lambda x:
                x.forwardAdmit(0, enriched.Not(Natural(m))).forwardFollow(lambda x:
                  x.forwardAdmit(0, enriched.Not(Natural(n)))))))
defLessArrow = defLessArrow.forwardFollow(lambda x:
    x.forwardOnBodyFollow(lambda x:
      x.forwardOnIthFollow(2, lambda one:
        one.forwardAppendDefinition(
          relation = Less(n, m),
          definition = enriched.Or([ Successor(n, m)
                                   , enriched.Exists([t],
                                       enriched.And(
                                         [ Successor(n, t)
                                         , Less(t, m) ]))])))))

defLessArrow.translate()
defLess = defLessArrow.tgt()

# This library wishes to provide as simple as possible a formula for extraction
# engines to implement and as useful a formula for users to start with.
# Therefore, it defines the following preludeArrow for converting the startingFormula
# into a formula more useful for clients of the library.  Proofs using this library should
# simply append their proofs to this preludeArrow.
preludeArrow = startingFormula.forwardAssociateOut(0, 0).forwardFollow(lambda x:
    x.forwardOnIth(0, defLessArrow))

# For debugging purposes.
preludeArrow.translate()

alwaysPreludeArrow = enriched.Always(preludeArrow.src()).forwardOnAlways(preludeArrow)
# This is the formula which users of this library should start with.
preludeFormula = enriched.Always(preludeArrow.tgt())
