# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basicConstructors as constructors

class Library:
  def __init__(self, claims, variables):
    self.variables = variables
    self.claims = claims
    self.formula = constructors.Exists(variables,
        constructors.And(claims))

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
  def __init__(self, library, arrow = None):
    self.library = library
    if arrow is None:
      self.arrow = library.formula.forwardOnAlwaysFollow(lambda x:
          x.forwardOnBodyFollow(lambda x:
            x.forwardOnAlwaysFollow(lambda x:
              x.forwardAndTrue())))
    else:
      assert(arrow.src == library.formula)
      self.arrow = arrow
    self.tgt = self.arrow.tgt

  def translate(self):
    return Proof(library = self.library.translate(),
        arrow = self.arrow.translate())

  def forwardFollow(self, f):
    return Proof(library = self.library, arrow = self.arrow.forwardFollow(lambda x:
      x.forwardOnAlwaysFollow(lambda x:
        x.forwardOnBodyFollow(lambda x:
          x.forwardOnAlwaysFollow(lambda x:
            x.forwardOnLeftFollow(lambda x:
              f(x)))))))

