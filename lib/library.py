# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from sets import Set
from calculus.enriched import constructors, path, formula as enrichedFormula

n_libraries = 0

class Library:
  def __init__(self, claims, variables, sub_libraries):
    for claim in claims:
      if not(isinstance(claim, enrichedFormula.Formula)):
        raise Exception("Claim is not an enriched formula %s."%(claim,))
    global n_libraries
    self.id = n_libraries
    n_libraries += 1
    self.variables = variables
    self.claims = claims
    self.sub_libraries = sub_libraries

  def __hash__(self):
    return self.id

  def __eq__(self, other):
    return other.__class__ == Library and self.id == other.id
  def __ne__(self, other):
    return not(self == other)

  def all_libraries_recursively(self):
    libraries = Set()
    for library in self.sub_libraries:
      for l in library.all_libraries_recursively():
        libraries.add(l)
    libraries.add(self)
    return libraries

  def formula(self):
    claims = []
    claims.extend(self.claims)
    for l in self.all_libraries_recursively():
      claims.extend(l.claims)
    return constructors.Always(constructors.Exists(
      [constructors.OrdinaryVariableBinding(v) for v in self.variables],
      constructors.And(claims)))

  def beginProof(self):
    return Proof(library = self)

class Proof:
  # library: the starting library
  # arrow: a path arrow such that arrow.src.top() == library.formula
  def __init__(self, library, arrow = None):
    self.library = library
    if arrow is None:
      self.arrow = path.new_path(library.formula()).advance()
      self.arrow = self.arrow.forwardFollow(lambda p: p.advance())
      for v in self.library.variables:
        self.arrow = self.arrow.forwardFollow(lambda p: p.advance())
    else:
      assert(arrow.src.top() == library.formula)
      self.arrow = arrow
    self.tgt = self.arrow.tgt

  def translate(self):
    return self.arrow.translate()

  def forwardFollow(self, f):
    return Proof(library = self.library, arrow = self.arrow.forwardFollow(f))

