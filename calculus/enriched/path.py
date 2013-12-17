# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import formula, endofunctor
from calculus.basic import endofunctor as basicEndofunctor

class Arrow:
  def __init__(self, src, tgt, enrichedArrow):
    self.src = src
    self.tgt = tgt
    self.enrichedArrow = enrichedArrow

  def forwardCompose(self, other):
    return Arrow(src = self.src, tgt = other.tgt,
        enrichedArrow = self.enrichedArrow.forwardCompose(other.enrichedArrow))

  def forwardFollow(self, f):
    return self.forwardCompose(f(self.tgt))

  def translate(self):
    return self.enrichedArrow.translate()

def newArrow(src, tgt, basicArrow):
  return Arrow(src = src, tgt = tgt,
      enrichedArrow = formula.Arrow(src = src.top(), tgt = tgt.top(), basicArrow = basicArrow))

def newIdentityArrow(src, tgt):
  return newArrow(src = src, tgt = tgt, basicArrow = src.top().translate().identity())

def new_path(formula):
  return Path(formula = formula, endofunctor = endofunctor.identity_functor)

class Path:
  def __init__(self, formula, endofunctor):
    self.formula = formula
    self.endofunctor = endofunctor

  # self.endofunctor must be covariant.
  # spec: a SearchSpec instance.
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

  def bottom(self):
    return self.formula
  def top(self):
    return self.endofunctor.onObject(self.formula)
  def identity(self):
    return newIdentityArrow(src = self, tgt = self)
  def onPath(self, enrichedArrow):
    if self.endofunctor.covariant():
      formula = enrichedArrow.tgt
    else:
      formula = enrichedArrow.src
    return newArrow(src = self,
        tgt = Path(formula = formula, endofunctor = self.endofunctor),
        basicArrow = self.endofunctor.translate().onArrow(enrichedArrow.translate()))

  def onFormulaAndEndofunctorFollow(self, f):
    enrichedArrow, newFormula = f(self.formula, self.endofunctor)
    return Arrow(src = self,
        tgt = Path(formula = newFormula, endofunctor = self.endofunctor),
        enrichedArrow = enrichedArrow)

  def onPathFollow(self, f):
    return self.onPath(f(self.bottom()))

  def covariant(self):
    return self.endofunctor.covariant()

  def instantiateBottomInOrder(self, variables):
    assert(not self.covariant())
    return self.onFormulaAndEndofunctorFollow(lambda x, e:
        e.instantiateInOrder(variables = variables, x = x))

  def forwardAndTrue(self):
    return self.onPathFollow(lambda x: x.forwardAndTrue()).forwardFollow(lambda p:
        p.advance(0))

  def retreatTotally(self):
    return newIdentityArrow(src = self,
        tgt = Path(formula = self.top(), endofunctor = endofunctor.identity_functor))

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
  def advance(self, index = None):
    a, b = self._factor_for_advance(index)
    return newIdentityArrow(src = self,
        tgt = Path(formula = a, endofunctor = b.compose(self.endofunctor)))

  def advanceAll(self, indices):
    a = self.identity()
    for index in indices:
      a = a.forwardFollow(lambda p:
          p.advance(index))
    return a

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

  def importAboutNegating(self, variables, f, g):
    return self.onFormulaAndEndofunctorFollow(lambda x, e:
        e.importAboutNegating(variables = variables,
          f = f, g = g, x = self.bottom()))

  def importAbout(self, variables, f, g):
    return self.onFormulaAndEndofunctorFollow(lambda x, e:
        e.importAbout(variables = variables,
          f = f, g = g, x = self.bottom()))

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


