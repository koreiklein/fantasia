# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic

class Library:
  def __init__(self, claims):
    self.claims = claims
    self.formula = basic.MultiAnd(self.claims)

  def union(self, other):
    assert(isinstance(other, Library))
    claims = []
    claims.extend(self.claims)
    claims.extend(other.claims)
    return Library(claims)

  def beginProof(self):
    return Proof(formula = self.formula)

class Proof:
  def __init__(self, library, arrow = None):
    self.library = library
    if arrow is None:
      self.arrow = library.formula.identity()
    else:
      assert(arrow.src == library.formula)
      self.arrow = arrow

  def forwardFollow(self, f):
    return Proof(library = self.library, arrow = self.arrow.forwardFollow(f))

