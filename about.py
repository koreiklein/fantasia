# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import *

from importables import ClaimsUse

# returns a function suitable for use as the second argument to a call to
# finishImporting (in importables).
def about(variables, desiredIndex = None):
  for variable in variables:
    assert(variable.__class__ == Var)
  def importableToUse(m):
    (known, potential) = _knownAndFunctionClaims(variables, m.claims())
    res = [] # A list of pairs, (a ClaimsUse object, the claim it concludes)
    for (key, claim) in potential:
      # Try all possible ways to substitute in our variables.
      res.extend(_tryAllPerms(variables, key, claim, known))

    # Wierd.  Consider refactoring this function and implementing this differently.
    if desiredIndex is None:
      raise Exception("Available claims: %s"%([claim for (claimsUse, claim) in res]))
    else:
      return res[desiredIndex][0]
  return importableToUse

def _tryAllPerms(variables, key, claim, known):
  res = []
  def _g(p):
    par = claim.forwardEliminateAll(p).tgt()
    assert(par.type() == parType)
    claimsUse = ClaimsUse(Set([key])).forwardFollow(lambda x:
        x.forwardUnsingleton().forwardFollow(lambda x:
          x.forwardEliminateAll(p)))
    # Try to eliminate all the clauses of the par but one.
    claimsUseForClause = _tryEliminateClauses(par, claimsUse, known)
    if claimsUseForClause is not None:
      res.append(claimsUseForClause)
  for p in _perms(variables):
    _g(p)
  return res

# par: a par with a single clause C which is not an enriched Not.
# claimsUse: a ClaimsUse object that produces par.
# known: a list of (key, claim) pairs which claimsUse can import.
# return: (a ClaimsUse object that concludes C, C)
#         , or None if doing so is too difficult.
def _tryEliminateClauses(par, claimsUse, known):
  eliminated = 0
  uneliminatedIndices = []
  for clauseIndex in range(len(par.values()))[::-1]:
    clause = par.values()[clauseIndex]
    if clause.__class__ == Not:
      maybeClaimsUse = _tryEliminateOneClause(par, clauseIndex, clause, claimsUse, known)
      if maybeClaimsUse is not None:
        eliminated += 1
        claimsUse = maybeClaimsUse
      else:
        uneliminatedIndices.append(clauseIndex)
    else:
      uneliminatedIndices.append(clauseIndex)
  if eliminated > 0:
    C = Par( [ par.values()[index] for index in uneliminatedIndices ] )
    if eliminated == len(par.values()) - 1:
      return (claimsUse.forwardFollow(lambda x: x.forwardUnsingleton()), C.values()[0])
    else:
      return (claimsUse, C)
  else:
    # Since we couldn't eliminate any of the clauses in the par, we assume our
    # user would prefer we didn't offer it as an option for something to import.
    return None

def _tryEliminateOneClause(par, clauseIndex, clause, claimsUse, known):
  def _g(key, claim):
    return claimsUse.forwardFollowWithNewClaim(key, lambda parAndClaim1:
        parAndClaim1.forwardRemoveFromPar(1, 0, clauseIndex).forwardFollow(lambda x:
          x.forwardUnsingleton()))
  for (key, claim) in known:
    if claim.translate() == clause.value().translate():
      return _g(key, claim)
  return None

def _knownAndFunctionClaims(variables, claims):
  known = []
  potential = []
  for (key, claim) in claims.items():
    if _claimOf(variables, claim):
      known.append( (key, claim) )
    elif _functionOf(variables, claim):
      potential.append( (key, claim) )
  return (known, potential)

def _uniqueCovariantClaim(par):
  res = None
  for clause in par.values():
    if not (clause.__class__ == Not):
      if res is None:
        res = clause
      else:
        return None # There was more than one covariant claim.
  return res

# return True iff this claim says something "relevant" about these variables.
def _claimOf(variables, claim):
  fv = claim.freeVariables()
  for v in variables:
    if v in fv:
      return True
  return False

def _functionOf(variables, claim):
  return (claim.__class__ == Quantifier
          and claim.type() == forallType
          and len(claim.variables()) == len(variables)
          and claim.body().__class__ == Conj
          and claim.body().type() == parType)

def _perms(xs):
  return _perms_(0, xs)

def _perms_(i, xs):
  if i == len(xs):
    return [[]]
  else:
    ofRest = _perms_(i + 1, xs)
    res = []
    for p in ofRest:
      for j in range(len(xs) - i):
        P = list(p)
        P.insert(j, xs[i])
        res.append(P)
    return res

