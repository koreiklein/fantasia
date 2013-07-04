# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import formula, endofunctor

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

  def bottom(self):
    return self.formula
  def top(self):
    return self.endofunctor.onObject(self.formula)
  def onPath(self, enrichedArrow):
    return newArrow(src = self,
        tgt = Path(formula = enrichedArrow.tgt, endofunctor = self.endofunctor),
        basicArrow = self.endofunctor.translate().onArrow(enrichedArrow.translate()))
  def onPathFollow(self, f):
    return self.onPath(f(self.bottom()))

  def forwardAndTrue(self):
    return self.onPathFollow(lambda x: x.forwardAndTrue()).forwardFollow(lambda p:
        p.advance(0))

  def retreat(self):
    if endofunctor.is_identity_functor(self.endofunctor):
      raise Exception("Can't retreat any more.")
    else:
      (a, b) = self.endofunctor.factor_left()
      return Path(formula = a.onObject(self.formula), endofunctor = b)

  # index: an index into self.bottom().values if self.bottom() is an And or Or
  #        None otherwise
  def advance(self, index = None):
    if index is not None:
      if not(isinstance(self.formula, formula.Conjunction)
          or self.formula.__class__ == formula.Application):
        raise Exception("Can't advance to index %s in a formula of class %s."%(index,
          self.formula.__class__))
      a, b = endofunctor.factor_index(self.formula, index)
      return newIdentityArrow(src = self,
          tgt = Path(formula = a, endofunctor = b.compose(self.endofunctor)))
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
    elif self.formula.__class__ == formula.Application:
      if endofunctor.is_identity_functor(self.formula.endofunctor):
        new_path = Path(formula = self.formula.formula, endofunctor = self.endofunctor)
        return newIdentityArrow(src = self, tgt = new_path).forwardCompose(
            new_path.advance(index))
      else:
        a, b = self.formula.endofunctor.factor_right()
        return newIdentityArrow(src = self,
            tgt = Path(formula = formula.Application(formula = self.formula.formula, endofunctor = a),
              endofunctor = b.compose(self.endofunctor)))
    else:
      raise Exception("Unknown class %s of formula to advance past."%(self.formula.__class__,))

