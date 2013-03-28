# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import *

from sets import Set

# This class is meant to represent the possible individual claims that could be
# imported into one part of an enriched logical formula from other parts.

class NullFeeder:
  def __init__(self, formula):
    self._formula = formula
  def claims(self):
    return {}
  def formula(self):
    return self._formula
  def importKeySet_feeder(self, keys):
    assert(len(keys) == 0)
    return ( self.formula().forwardSingleton(andType).forwardFollow(lambda x:
      x.forwardAssociateOut(1, 1))
           , {})

def newFeeder(formula):
  if formula.__class__ == Always:
    return AlwaysFeeder(formula)
  elif formula.__class__ == Conj and formula.type() == andType:
    return ConjFeeder(formula)
  else:
    return SingletonFeeder(formula)

# Note: There are three conceivable ways you might want to import
# from an always, you may want to import
#    0) Each claim available in always.value()
#    1) Each claim available in always.value() but wrapped in an Always
#    2) Each claim available in always.value() but wrapped in an Always if it isn't already.
# The current implementation choses option 0.  Perhaps the others will be better suited
# later on.  If you have some examples to justify using a different option, go ahead and change
# the implementation.
class AlwaysFeeder:
  def __init__(self, always):
    assert(always.__class__ == Always)
    self._always = always
    self._childFeeder = newFeeder(always.value())
    self._claims = {}
    for (key, value) in self._childFeeder.claims().items():
      self._claims[('always', key)] = value

  def claims(self):
    return self._claims
  def formula(self):
    return self._always

  # keys: a set of keys into the dict self.claims()
  # return a pair (t, d),
  #   where t is an "importing" arrow on self
  #   that "replaces" self with And([ self', claimsOfKeys])
  #   where claimsOfKeys is an And whose length is the cardinality of keys.
  #   and where d is a dict mapping each key k in keys to an index i such that
  #              claimsOfKeys[i] == self.claims(k)
  def importKeySet_feeder(self, keys):
    childKeys = Set()
    for key in keys:
      assert(key.__class__ == tuple)
      assert(key[0] == 'always')
      childKey = key[1]
      childKeys.add(childKey)
    (t, d) = self._childFeeder.importKeySet_feeder(childKeys)
    T = self.formula().forwardDiagonal().forwardFollow(lambda x:
        x.forwardOnIthFollow(1, lambda x:
          x.forwardUnalways().forwardCompose(t.forwardFollow(lambda x:
            x.forwardForgetAllBut(1)))))
    D = {}
    for (key, index) in d.items():
      D[('always', key)] = index
    return (T, D)

class SingletonFeeder:
  def __init__(self, formula):
    self._formula = formula
    self._claims = {'here' : formula}

  def claims(self):
    return self._claims
  def formula(self):
    return self._formula

  def importKeySet_feeder(self, keys):
    if 'here' in keys:
      assert(len(keys) == 1)
      d = {'here' : 0}
      t = self.formula().forwardSingleton(andType).forwardFollow(lambda x:
          x.forwardSingleton(andType).forwardFollow(lambda x:
            x.forwardAssociateOut(0, 0)))
      return (t, d)
    else:
      assert(len(keys) == 0)
      d = {}
      t = self.formula().forwardSingleton(andType).forwardFollow(lambda x:
          x.forwardAssociateOut(1, 1))
      return (t, d)

class ConjFeeder:
  def __init__(self, formula):
    self._formula = formula
    self._feeders = []
    self._claims = {}
    assert(formula.__class__ == Conj and formula.type() == andType)
    for i in range(len(formula.values())):
      feeder = newFeeder(formula.values()[i])
      self._feeders.append(feeder)
      for (key, value) in feeder.claims().items():
        self._claims[(i, key)] = value

  def claims(self):
    return self._claims

  def formula(self):
    return self._formula

  # keys: a set of keys into the dict self.claims()
  # return a pair (t, d),
  #   where t is an "importing" arrow on self
  #   that "replaces" self with And([ self', claimsOfKeys])
  #   where claimsOfKeys is an And whose length is the cardinality of keys.
  #   and where d is a dict mapping each key k in keys to an index i such that
  #              claimsOfKeys[i] == self.claims(k)
  def importKeySet_feeder(self, keys):
    return _importKeySet_conj(self.formula(), self._feeders, keys)

# conj: an enriched Conj
# feeders: one feeder for each clause of conj
# keys: a list of keys that can be imported at conj.  Each key must be for one of the feeders.
# return: (T, D) where T is an arrow such that:
#   T.src() == conj
#   T.tgt().values()[0] is what's left of conj.values() after the import.
#   T.tgt().values()[1] is a list L of the values extracted from the feeders.
#   D maps each key in keys to the index in L at which you can find the corresponding claim.
def _importKeySet_conj(conj, feeders, keys):
  feeder_keysets = [Set() for x in feeders]
  for (i, key) in keys:
    feeder_keysets[i].add(key)
  # feeder_keysets[i] is now the set of keys to be imported from feeders[i]
  T = conj.identity()
  D = {}
  n = len(T.tgt().values())
  m = n
  newValues = 0
  for i in range(len(feeders)):
    (t, d) = feeders[i].importKeySet_feeder(feeder_keysets[i])
    T = T.forwardFollow(lambda x:
        x.forwardOnIth(i, t).forwardFollow(lambda x:
          x.forwardAssociateIn(i).forwardFollow(lambda x:
            x.forwardShift(i + 1, m - (i + 1)).forwardFollow(lambda x:
              x.forwardAssociateIn(len(x.values()) - 1)))))
    for (key, value) in d.items():
      D[(i, key)] = newValues + value
    m = len(T.tgt().values())
    newValues = m - n
  T = T.forwardFollow(lambda x:
      x.forwardAssociateOut(n, m).forwardFollow(lambda x:
        x.forwardAssociateOut(0, n)))
  return (T, D)

class Intermediate:
  # parent is an Intermediate or an Importable.
  # formula must not be an And, or a Not. It may be a Quantifier, Or, With, or Par.
  # index is none if formula.__class__ == Quantifier, otherwise it is an index into
  #   formula.values() corresponding to an Intermediate or a Importable with self as parent.
  def __init__(self, formula, parent, index = None):
    if index is None:
      assert(formula.__class__ == Quantifier)
    else:
      assert(index is not None)
      assert(formula.__class__ == Conj)
      assert(formula.type() in [orType, withType, parType])
      assert(0 <= index)
      assert(index < len(formula.values()))
    self._formula = formula
    self._parent = parent
    self._index = index
    self._claims = {}
    for (key, value) in self.parent().claims().items():
      self._claims[('parent', key)] = value

  def formula(self):
    return self._formula
  def parent(self):
    return self._parent
  def child(self):
    if self._index is None:
      return self.formula().body()
    else:
      return self.formula().values()[i]
  def topmostParent(self):
    return self.parent().topmostParent()

  def claims(self):
    return self._claims

  # keys: a set of keys into the dict self.claims()
  # return a pair (F, d),
  #   where F takes a function f and returns an "importing" arrow on self.topmostParent()
  #   that "replaces" self.child() with f(And([self.child(), claimsOfKeys])).tgt()
  #   where claimsOfKeys is an And whose length is the cardinality of keys.
  #   and where d is a dict mapping each key k in keys to an index i such that
  #              claimsOfKeys[i] == self.claims(k)
  def importKeySetToChild(self, keys):
    l = []
    for (parentString, key) in keys:
      assert(parentString == 'parent')
      l.append(key)
    (parentF, parentD) = self.parent().importKeySetToChild(Set(l))
    D = {}
    for (parentKey, value) in parentD.items():
      D[('parent', parentKey)] = value
    if self._index is None:
      F = lambda f: parentF(lambda selfAndXs:
        selfAndXs.forwardConjQuantifier(0).forwardFollow(lambda q:
          q.forwardOnBodyFollow(f)))
    else:
      F = lambda f: parentF(lambda selfAndXs:
        selfAndXs.forwardImportToContainedConj(1, 0, self._index).forwardFollow(lambda x:
          x.forwardUnsingleton().forwardFollow(lambda x:
            x.forwardOnIthFollow(self._index, f))))
    return (F, D)

class Importable:
  # importingIndex = -1 iff this is the top level importable
  # parent can be None, an Importable, or an Intermediate.
  # (it can and often should still have a parent), otherwise it is the index
  # at which to find other importables and Intermediates with self as a parent.
  def __init__(self, formula, importingIndex = -1, parent = None):
    assert(formula.__class__ == Conj and formula.type() == andType)
    assert(importingIndex == -1 or 0 <= importingIndex)
    assert(importingIndex < len(formula.values()))
    self._formula = formula
    self._importingIndex = importingIndex
    self._parent = parent
    self._claims = {}
    self._feeders = []
    for i in range(len(formula.values())):
      if i == importingIndex:
        self._feeders.append(NullFeeder(formula.values()[i]))
      else:
        self._feeders.append(newFeeder(formula.values()[i]))
        for (key, value) in self._feeders[i].claims().items():
          self._claims[(i, key)] = value
    if parent is not None:
      for (key, value) in parent.claims().items():
        self._claims[('parent', key)] = value

  def formula(self):
    return self._formula
  def parent(self):
    return self._parent
  def topmostParent(self):
    if self.parent() == None:
      return self
    else:
      return self.parent().topmostParent()

  # return the of claims that can be imported.
  def claims(self):
    return self._claims

  # claimsUse: a ClaimsUse object that specifies which and how the claims of self are to be used.
  # return: a forward arrow on self.topmostParent().formula() which imports
  #         the relevant claims near self.formula() and applied the arrow of
  #         claimsUse to them.
  def use(self, claimsUse):
    (F, D) = self.importKeySet(Set(claimsUse.keys()))
    return F(lambda selfAndXs:
        selfAndXs.forwardOnIthFollow(1, lambda xs:
          _applyPerm(D, claimsUse.keys(), xs).forwardFollow(lambda xs:
            claimsUse.apply(xs))).forwardFollow(lambda x:
            x.forwardAssociateIn(0)))

  def _importFromParentOrNone(self, keys):
    if self.parent() is None:
      assert(len(keys) == 0)
      return ( lambda f: self.formula().forwardSingleton(andType).forwardFollow(lambda x:
        x.forwardAssociateOut(1, 1).forwardFollow(f))
             , {})
    else:
      keysForParent = []
      for (parentString, parentKey) in keys:
        assert(parentString == 'parent')
        keysForParent.append(parentKey)
      (f, d) = self.parent().importKeySetToChild(keysForParent)
      F = f
      D = {}
      for (parentKey, value) in d.items():
        D[('parent', parentKey)] = value
      return (F, D)

  # keys: keys that can be imported at self, not including 'here'
  # return (parentKeys, feederKeys)
  # where parentKeys is a list of the parent parts of the parent keys in keys
  # where feederKeys is a list of the keys which are for feeders.
  def _splitKeys(self, keys):
    parentKeys = Set()
    feederKeys = Set()
    for key in keys:
      assert(not ('here' == key))
      if key[0] == 'parent':
        parentKeys.add(key)
      else:
        feederKeys.add(key)
    return (parentKeys, feederKeys)

  # keys: a set of keys into the dict self.claims()
  # return a pair (F, d),
  #   where F takes a function f and returns an "importing" arrow on self.topmostParent()
  #   that "replaces" self with f(And([self', claimsOfKeys])).tgt()
  #   where claimsOfKeys is an And whose length is the cardinality of keys.
  #   and where d is a dict mapping each key k in keys to an index i such that
  #              claimsOfKeys[i] == self.claims(k)
  def importKeySet(self, keys):
    (parentKeys, feederKeys) = self._splitKeys(keys)
    (F, parentD) = self._importFromParentOrNone(parentKeys)
    (T, feederD) = _importKeySet_conj(self.formula(), self._feeders, feederKeys)
    _l = feederD.items()
    n = len(_l)
    _l.extend([(key, value + n) for (key, value) in parentD.items()])
    D = dict(_l)
    return ( lambda f: F(lambda selfAndPV:
      selfAndPV.forwardOnIth(0, T).forwardFollow(lambda selfAndFV_and_PV:
        # And([ And([ self', feederValues])
        #     , parentValues ])
        selfAndFV_and_PV.forwardAssociateIn(0).forwardFollow(lambda x:
          x.forwardAssociateOut(1, 3).forwardFollow(lambda x:
            x.forwardOnIthFollow(1, lambda x:
              x.forwardAssociateIn(1).forwardFollow(lambda x:
                x.forwardAssociateIn(0))).forwardFollow(f)))))
           , D)

  def importKeySetToChild(self, keys):
    assert(self._importingIndex != -1)
    (F, D) = self.importKeySet(keys)
    return ( lambda f: F(lambda selfAndXs:
      selfAndXs.forwardImportToContainedConj(1, 0, self._importingIndex).forwardFollow(lambda x:
        x.forwardUnsingleton().forwardFollow(lambda x:
          x.forwardOnIthFollow(self._importingIndex, f))))
           , D)

# keys: a list of keys of length n
# conj: an enriched And of length n
# d: a dictionary isomorphism from the keys in keys to the indices of conj.
# return: an arrow a with src conj that permutes it according to d and keys.
#         Explicitly: a.src() == conj
#                     forall i. a.tgt().values()[i] == conj.values()[d[keys[i]]]
# note: This function is essentially an aggrandized sorting function.
#       The current implementation does not attempt to implement an efficient sort.
# note: The fact that fantasia has a function that does this is RIDICULOUS and intuitively
#       ugly.   Consider finding a clever way to make it unnecessary.
def _applyPerm(d, keys, conj):
  res = _applyPermPartial(d, keys, 0, conj)
  return res

# conj: an enriched conj of length N
# n: an integer in [0,N]
# keys: a list of keys of length N
# d: a dictionary isomorphism between keys[n:] and [n:N)
# return: an arrow a such that
#           a.src() == conj
#           a.tgt().values()[i] ==
#                   | conj.values()[i]   when   i < n
#                   | conj.values()[d[keys[i]]]   when   i >= n
def _applyPermPartial(d, keys, n, conj):
  if n == len(keys):
    return conj.identity()
  else:
    i = d[keys[n]]
    D = {}
    for (key, value) in d.items():
      if value > i:
        D[key] = value
      elif value < i:
        D[key] = value + 1
    return conj.forwardShift(i, n - i).forwardFollow(lambda x:
          _applyPermPartial(D, keys, n + 1, x))

def _associateAllButLast(conj):
  return conj.forwardAssociateOut(0, len(conj.values()) - 1)

class ClaimsUse:
  # keys, a list of keys into the claims() dictionaries returned by
  #   Feeders, Intermediates, and Importables
  # arrows has src And([lookup(key) for key in keys]), and an arbitrary tgt.
  def __init__(self, keys, arrowF = lambda x: x.identity()):
    self._keys = keys
    self._arrowF = arrowF

  def forwardFollow(self, f):
    return ClaimsUse(self._keys, lambda x: self._arrowF(x).forwardFollow(f))

  # claimsForKeysObject: an And formula containing one formula for each key is self.keys()
  def apply(self, claimsForKeysObject):
    return self._arrowF(claimsForKeysObject)
  def keys(self):
    return self._keys

  # key: the key for a new claim.
  # f: a function from And([the ultimate tgt of self, lookup(key)]) to an arrow leaving it.
  # return: a new ClaimsUse which gets all the keys, "applies" self, and then "applies" f.
  def forwardFollowWithNewClaim(self, key, f):
    keys = list(self._keys)
    keys.append(key)
    return ClaimsUse(keys, lambda x:
        _associateAllButLast(x).forwardFollow(lambda x:
          x.forwardOnIthFollow(0, self._arrowF)).forwardFollow(f))

# define a critical to be either an Importable or an Intermediate.

# formula: a Quantifier formula
# f: a function taking the body of formula to a function taking m's parent
#      critical to a critical m.
# return: a function returning a critical m when given m's parent critical.
def continueImportingOnBodyFollow(formula, f):
  assert(formula.__class__ == Quantifier)
  return (lambda parent: f(formula.body())(Intermediate(formula = formula, parent = parent)))

# formula: a Conj formula
# i: an index into formula.values()
# f: a function taking the ith child of formula to a function taking a parent
#      critical to a critical.
# return: a function returning the final critical m when given a parent critical.
def continueImportingOnOnIthFollow(formula, i, f):
  assert(formula.__class__ == Conj)
  if formula.type() == andType:
    return (lambda parent: f(formula.values()[i])(Importable( formula = formula
                                                            , parent = parent
                                                            , importingIndex = i)))
  else:
    return (lambda parent: f(formula.values()[i])(Intermediate(formula = formula
                                                              , parent = parent
                                                              , index = i)))

# formula: a Quantifier formula.
# i: an index into formula.values()
# f: a function taking the ith child of formula to a function taking a parent
#      critical to a critical.
# return: a top level critical.
def beginImportingOnIthFollow(formula, i, f):
  assert(formula.__class__ == Conj)
  assert(formula.type() == andType)
  return continueImportingOnOnIthFollow(formula, i, f)(None)

def finishImporting(formula, importableToUseF):
  def res(parent):
    m = Importable(formula = formula, parent = parent)
    return m.use(importableToUseF(m))
  return res

# TODO(koreiklein): The descriptions for the above 4 functions are TERRIBLE.  Fix them.

