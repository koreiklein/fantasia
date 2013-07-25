# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import formula, endofunctor, spec
from calculus.basic import endofunctor as basicEndofunctor

# Instances of this class represent arrows between paths.
class Arrow:
  # src: a path
  # tgt: a path
  # enrichedArrow: an enriched arrow (see calculus.enriched.formula.Arrow) such that
  #      enrichedArrow.src == src.top()
  #      enrichedArrow.tgt == tgt.top()
  def __init__(self, src, tgt, enrichedArrow):
    self.src = src
    self.tgt = tgt
    self.enrichedArrow = enrichedArrow

  # Given two path arrows a, b with a.tgt == b.src:
  #   a.forwardCompose(b) is a path arrow such that
  #   a.forwardCompose(b).src == a.src
  #   a.forwardCompose(b).tgt == a.tgt
  def forwardCompose(self, other):
    return Arrow(src = self.src, tgt = other.tgt,
        enrichedArrow = self.enrichedArrow.forwardCompose(other.enrichedArrow))

  def forwardFollow(self, f):
    return self.forwardCompose(f(self.tgt))

  # return a basic arrow corresponding to self.
  def translate(self):
    return self.enrichedArrow.translate()

# src: a path
# tgt: a path
# basicArrow: a basic arrow (see calculus.basic.formula.Arrow) such that
#   basicArrow.src == src.top().translate()
#   basicArrow.tgt == tgt.top().translate()
# return: a path arrow from src to tgt.
def newArrow(src, tgt, basicArrow):
  return Arrow(src = src, tgt = tgt,
      enrichedArrow = formula.Arrow(src = src.top(), tgt = tgt.top(), basicArrow = basicArrow))

# src: a path
# tgt: a path such that src.top() == tgt.top()
# return: a path arrow from src to tgt.
def newIdentityArrow(src, tgt):
  return newArrow(src = src, tgt = tgt, basicArrow = src.top().translate().identity())

def new_path(formula):
  return Path(formula = formula, endofunctor = endofunctor.identity_functor)

# A path p should be though of as an enriched formula with a distinguished sub-formula.
# For example:
#  Path(endofunctor = And([0 < 2, ____]),
#       formula = 5 == 5) might be visualized as:
#                 **********
#   And([ 0 < 2,  **5 == 5** ])
#                 **********
# For example:
#                            *********
#  Path(endofunctor = And([0 < 2, Or([2 == 2, ____]), 0 < 3]),
#       formula = 1 < 2) might be visualized as:
#   And([ 0 < 2, Or([2 == 2, **1 < 2** ]), 0 < 3])
#                            *********
class Path:
  def __init__(self, formula, endofunctor):
    self.formula = formula
    self.endofunctor = endofunctor

  def __repr__(self):
    def shift(x):
      return '\n'.join(['    ' + s for s in x.split('\n')])
    return "%s PATH:\ntop =\n%s\nbottom =\n%s"%(
        'Covariant' if self.covariant() else 'Contravariant',
        shift(repr(self.top().top_level_render()._backend)),
        shift(repr(self.bottom().top_level_render()._backend)))

  # self.endofunctor must be covariant.
  # spec: a SearchSpec instance. (see calculus.enriched.spec.SearchSpec)
  # return: a list of pairs (B, f) such that spec.valid(B) and
  # f() is a an arrow :
  #   self -> Path(formula = And([B, self.formula]), endofunctor = self.endofunctor)
  def search(self, spec):
    assert(self.endofunctor.covariant())
    return [( B
            , lambda B=B, nt=nt: newArrow(src = self,
              tgt = Path(formula = formula.And([B, self.formula]),
                endofunctor = self.endofunctor),
              basicArrow = nt(self.formula.translate())) )
      for B in self.endofunctor.search(spec)
      for nt in [self.endofunctor.translate().importExactly(B.translate())]]

  # The enriched formula represented by this path.
  def top(self):
    return self.endofunctor.onObject(self.formula)
  # The distinguished sub-formula of self.top()
  def bottom(self):
    return self.formula

  # Return a path arrow from self to self
  def identity(self):
    return newIdentityArrow(src = self, tgt = self)

  # enrichedArrow: an enriched arrow with enrichedArrow.src == self.bottom()
  # return: a path arrow from self to Path(endofunctor = self.endofunctor, formula = enrichedArrow.tgt)
  def onPath(self, enrichedArrow):
    if self.endofunctor.covariant():
      formula = enrichedArrow.tgt
    else:
      formula = enrichedArrow.src
    return newArrow(src = self,
        tgt = Path(formula = formula, endofunctor = self.endofunctor),
        basicArrow = self.endofunctor.translate().onArrow(enrichedArrow.translate()))

  def onPathFollow(self, f):
    return self.onPath(f(self.bottom()))

  # return True iff self.bottom() is in a covariant spot inside self.top()
  def covariant(self):
    return self.endofunctor.covariant()

  def forwardAndTrue(self):
    return self.onPathFollow(lambda x: x.forwardAndTrue()).forwardFollow(lambda p:
        p.advance(0))

  # return: path arrow equivalent to self.retreat(n) in which n is as large as possible.
  def retreatTotally(self):
    return newIdentityArrow(src = self,
        tgt = Path(formula = self.top(), endofunctor = endofunctor.identity_functor))

  # return a path arrow from self to a path with a slightly shorter endofunctor
  # and a slightly larger formula.
  def retreat(self, n = None):
    if n is None:
      (a, b) = self.endofunctor.factor_left()
      return newIdentityArrow(src = self,
          tgt = Path(formula = a.onObject(self.formula), endofunctor = b))
    else:
      a = self.identity()
      for i in range(n):
        a = a.forwardFollow(lambda p: p.retreat())
      return a

  def _factor_for_advance(self, index):
    if index is not None:
      if not(isinstance(self.formula, formula.Conjunction)):
        raise Exception("Can't advance to index %s in a formula of class %s."%(index,
          self.formula.__class__))
      values = list(self.formula.values)
      a = values.pop(index)
      if self.formula.__class__ == formula.And:
        b = endofunctor.And(values = values, index = index)
      else:
        assert(self.formula.__class__ == formula.Or)
        b = endofunctor.Or(values = values, index = index)
      return (a, b)
    elif self.formula.__class__ == formula.Always:
      return (self.formula.value, endofunctor.always_functor)
    elif self.formula.__class__ == formula.Not:
      return (self.formula.value, endofunctor.not_functor)
    elif self.formula.__class__ == formula.Exists:
      return (self.formula.value, endofunctor.Exists(self.formula.bindings))
    elif self.formula.__class__ == formula.WellDefined:
      return (self.formula.value, endofunctor.WellDefinedFunctor(
        variable = self.formula.variable,
        newVariable = self.formula.newVariable,
        equivalence = self.formula.equivalence))
    elif self.formula.__class__ == formula.Holds:
      raise Exception("Can't advance past Holds.")
    elif self.formula.__class__ == formula.Iff:
      raise Exception("Can't advance past Iff.")
    elif self.formula.__class__ == formula.Hidden:
      raise Exception("Can't advance past Hidden.")
    elif self.formula.__class__ == formula.Unique:
      raise Exception("Can't advance past Unique.")
    elif isinstance(self.formula, formula.Conjunction):
      raise Exception("Can't advance past Conjunction without giving an index.")
    else:
      raise Exception("Unknown class %s of formula to advance past."%(self.formula.__class__,))

  # index: an index into self.bottom().values if self.bottom() is an And or Or
  #        None otherwise
  # return: a path arrow with src self, and with tgt a path like self, but with a slightly
  #         larger endofunctor and a slightly smaller formula.
  def advance(self, index = None):
    a, b = self._factor_for_advance(index)
    return newIdentityArrow(src = self,
        tgt = Path(formula = a, endofunctor = b.compose(self.endofunctor)))

  # A more compact way to do multiple advance arrows at once.
  # self.advanceAll([i, j, k]) == self.advance(i).forwardFollow(lambda p:
  #                               p.advance(j).forwardFollow(lambda p:
  #                               p.advance(k)))
  def advanceAll(self, indices):
    a = self.identity()
    for index in indices:
      a = a.forwardFollow(lambda p:
          p.advance(index))
    return a

  # Simplify the bottom of self.
  # return: a path arrow A such that self == A.src and A.tgt.endofunctor == self.endofunctor
  #         and A.tgt.formula is a simplified version of self.formula.
  def simplifyBottom(self):
    if self.covariant():
      return self.onPathFollow(lambda x:
          x.forwardSimplify())
    else:
      return self.onPathFollow(lambda x:
          x.backwardSimplify())

  def heavySimplifyWithin(self, index = None):
    return self.advance(index).forwardFollow(lambda p:
        p.heavySimplify().forwardFollow(lambda p:
          p.retreat()))

  def heavySimplifyWithinAndAtop(self, index = None):
    return self.heavySimplifyWithin(index).forwardFollow(lambda p:
        p.simplifyBottom())

  # self must be contravariant.
  # self.bottom() must be of class formula.Exists quantifying over variables w_i
  # variables: a list of variables v_i
  # return: an arrow from self to Path(endofunctor == self.endofunctor, formula = F)
  #         where F is a copy of self.bottom().value in which each variable w_i has been
  #         replaced by v_i
  #
  # note: This method may raise an exception if one of the variables w_i is
  #       quantified in a bounded manner.  For example:
  #       if self.bottom() == Exists([BoundedVariableBinding(w_0, List)], 0 == 0)
  #       and variables == [v_0]
  #       and it is not possible to export the claim Holds(v_0, List.'),
  #       then instantiateBottomInOrder will raise an exception.
  #
  #       This behavior is desirable because self.bottom() is an existential claim
  #       that only applies to lists, but the user has not proved that v_0 is a list.
  def instantiateBottomInOrder(self, variables):
    assert(not self.covariant())
    assert(self.bottom().__class__ == formula.Exists)
    assert(len(self.bottom().bindings) == len(variables))
    enrichedArrow, newFormula = self.endofunctor.instantiateInOrder(variables = variables, x = self.formula)
    return Arrow(src = self,
        tgt = Path(formula = newFormula, endofunctor = self.endofunctor),
        enrichedArrow = enrichedArrow).forwardFollow(lambda p:
            p.heavySimplify())

  def importAboutGenerally(self, f, g):
    class S(spec.SearchSpec):
      def search_hidden_formula(self, name):
        return True
      def valid(self, e):
        return e.__class__ == formula.Always and f([], e.value)
    importable_claims = self.endofunctor.search(S())
    claim = importable_claims[g(importable_claims)]
    import_arrow = self.endofunctor.importExactly(claim)(self.formula)
    return Arrow(src = self,
        tgt = Path(formula = formula.And([claim, self.formula]), endofunctor = self.endofunctor),
        enrichedArrow = import_arrow)

  # a variant of self.importAbout for use with contravariant paths.
  # (see Path.importAbout)
  def importAboutNegating(self, variables, f, g):
    assert(not self.covariant())
    p = Path(endofunctor = endofunctor.not_functor.compose(self.endofunctor),
        formula = formula.Not(self.formula))
    a = p.importAbout(variables, f, g)
    return self.onPathFollow(lambda x:
        x.backwardUndoubleDual()).forwardCompose(a).forwardFollow(lambda p:
            p.simplifyBottom())

  # variables: a list of variables in scope in self.endofunctor.
  # f: a function from a list of variable bindings and a formula to a boolean.
  # g: a function from a list of formulas to an index into that list.
  #
  # search self.endofunctor for claims at covariant spots of the form:
  #  Forall(xs, Y) such that len(xs) == len(variables) and f(xs, Y) == True
  # pass the list L of substituted formulas to g to get an index I, and return a path
  # arrow with src self, that imports and instantiates to get L[I]
  def importAbout(self, variables, f, g):
    if len(variables) == 0:
      return self.importAboutGenerally(f, g)
    assert(self.endofunctor.covariant())
    # TODO Improve performance once it becomes important.
    class S(spec.SearchSpec):
      def search_hidden_formula(self, name):
        return True
      def valid(self, e):
        result = (e.__class__ == formula.Always
            and e.value.__class__ == formula.Not
            and e.value.value.__class__ == formula.Exists
            and len(e.value.value.bindings) == len(variables)
            and e.value.value.value.__class__ == formula.Not
            and f(e.value.value.bindings, e.value.value.value.value))
        return result
    importable_claims = self.endofunctor.search(S())
    xs = [ claim.value.value.substituteAllVariablesInBody(variables).value
        for claim in importable_claims ]
    index = g(xs)
    claim = importable_claims[index]
    substituted_claim = xs[index]

    import_arrow = self.endofunctor.importExactly(claim)(self.formula)
    larger_functor = endofunctor.not_functor.compose(endofunctor.always_functor).compose(
        endofunctor.And(index = 0, values = [self.formula])).compose(
            self.endofunctor)
    instantiate_arrow, also_substituted_claim = larger_functor.instantiateInOrder(variables, claim.value.value)
    assert(substituted_claim.translate() == also_substituted_claim.value.translate())
    B = formula.Always(formula.Not(formula.Not(substituted_claim)))
    return Arrow(src = self,
        tgt = Path(formula = formula.And([B, self.formula]), endofunctor = self.endofunctor),
        enrichedArrow = import_arrow.forwardCompose(instantiate_arrow))

  def maybeExportBottom(self):
    if self.covariant():
      try:
        basicArrow = self.endofunctor.translate().contradictBottomCovariant(self.bottom().translate())
      except basicEndofunctor.UnimportableException:
        return self.identity()
      return newArrow(src = self,
          tgt = Path(endofunctor = self.endofunctor, formula = formula.Or([])),
          basicArrow = basicArrow)
    else:
      try:
        basicArrow = self.endofunctor.translate().exportBottom(self.bottom().translate())
      except basicEndofunctor.UnimportableException:
        return self.identity()
      return newArrow(src = self,
          tgt = Path(endofunctor = self.endofunctor, formula = formula.And([])),
          basicArrow = basicArrow)

  # (like self.simplifyBottom())
  # return: an arrow that not only simplifies self.bottom(), but also makes every attempt to export
  #         from it and to find contradictions.
  def heavySimplify(self):
    if self.bottom().__class__ == formula.Not:
      return self.heavySimplifyWithinAndAtop()
    elif self.bottom().__class__ == formula.Always:
      if self.bottom().value.__class__ == formula.Holds or self.bottom().value.__class__ == formula.Identical:
        return self.maybeExportBottom()
      else:
        return self.heavySimplifyWithinAndAtop()
    elif self.bottom().__class__ == formula.Holds or self.bottom().__class__ == formula.Identical:
      return self.maybeExportBottom()
    elif self.bottom().__class__ == formula.Exists:
      return self.heavySimplifyWithinAndAtop()
    elif isinstance(self.bottom(), formula.Conjunction):
      return self.heavySimplifyConjunction(0).forwardFollow(lambda p:
          p.simplifyBottom())
    else:
      raise Exception("Unrecognized formula of class %s"%(self.bottom().__class__,))

  # self.bottom() must be a Conjunction instance.
  # i: an index into self.bottom().values.
  # assume that all self.bottom().values[:i] are simplified already.
  # return: a path arrow simplifying the remaining values of the conjunction.
  #         ( but not the conjunction itself )
  def heavySimplifyConjunction(self, i):
    assert(isinstance(self.bottom(), formula.Conjunction))
    if i == len(self.bottom().values):
      return self.identity()
    else:
      return self.heavySimplifyWithin(i).forwardFollow(lambda p:
          p.heavySimplifyConjunction(i+1))


