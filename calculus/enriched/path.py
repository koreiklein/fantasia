# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import formula, endofunctor

class Arrow:
  def __init__(self, src, tgt, enrichedArrow):
    self.src = src
    self.tgt = tgt
    self.enrichedArrow = enrichedArrow

def newArrow(src, tgt, basicArrow):
  return Arrow(src = src, tgt = tgt,
      enrichedArrow = formula.Arrow(src = src.top(), tgt = tgt.top(), basicArrow = basicArrow))

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

  def retreat(self):
    if endofunctor.is_identity_functor(self.endofunctor):
      raise Exception("Can't retreat any more.")
    else:
      (a, b) = self.endofunctor.factor_left()
      return Path(formula = a.onObject(self.formula), endofunctor = b)

  def advance(self):
    if self.formula.__class__ == formula.Holds:
      raise Exception("Can't advance past Holds.")
    elif self.formula.__class__ == formula.Iff:
      raise Exception("Can't advance past Iff.")
    elif self.formula.__class__ == formula.Hidden:
      raise Exception("Can't advance past Hidden.")
    elif self.formula.__class__ == formula.Unique:
      raise Exception("Can't advance past Unique.")
    elif self.formula.__class__ == formula.Conjunction:
      raise Exception("Can't advance past Conjunction.")
    elif self.formula.__class__ == formula.Application:
      if endofunctor.is_identity_functor(self.formula.endofunctor):
        return
    else:
      raise Exception("Unknown class of formula to advance past.")

