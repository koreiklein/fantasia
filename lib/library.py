# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import enriched

import path

class Library:
  def __init__(self, claims, variables):
    self.variables = variables
    self.claims = claims
    self.formula = enriched.Always(enriched.BasicExists(variables,
        enriched.And(claims)))

  def translate(self):
    return Library(claims = [claim.translate() for claim in self.claims],
        variables = [variable.translate() for variable in self.variables])

  def union(self, other):
    assert(isinstance(other, Library))
    claims = []
    variables = []
    claims.extend(self.claims)
    variables.extend(self.variables)
    claims.extend(other.claims)
    variables.extend(other.variables)
    return Library(claims = claims, variables = variables)

  def beginProof(self):
    return Proof(library = self)

class Proof:
  # library: the starting library
  # arrow: a path arrow such that arrow.src.top() == library.formula
  def __init__(self, library, arrow = None):
    self.library = library
    if arrow is None:
      self.arrow = path.new_path(library.formula).advance().forwardFollow(lambda x:
          x.advance().forwardFollow(lambda x:
            x.advance().forwardFollow(lambda x:
              x.forwardOnPathFollow(lambda x:
                x.forwardAndTrue()))))
    else:
      assert(arrow.src.top() == library.formula)
      self.arrow = arrow
    self.tgt = self.arrow.tgt

  def translate(self):
    return Proof(library = self.library.translate(),
        arrow = self.arrow.translate())

  def forwardFollow(self, f):
    return Proof(library = self.library, arrow = self.arrow.forwardFollow(f))

