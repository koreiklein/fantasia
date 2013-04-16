# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import constructors

class Library:
  def __init__(self, claims):
    self.claims = claims
    self.formula = constructors.And(claims)

  def union(self, other):
    assert(isinstance(other, Library))
    claims = []
    claims.extend(self.claims)
    claims.extend(other.claims)
    return Library(claims)

  def beginProof(self):
    return Proof(library = self)

class Proof:
  def __init__(self, library, arrow = None):
    self.library = library
    if arrow is None:
      self.arrow = library.formula.identity()
    else:
      assert(arrow.src == library.formula)
      self.arrow = arrow
    self.tgt = self.arrow.tgt

  def forwardFollow(self, f):
    return Proof(library = self.library, arrow = self.arrow.forwardFollow(f))

