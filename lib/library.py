# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from sets import Set
from calculus.enriched import constructors, path, formula as enrichedFormula

n_libraries = 0

# A Library is defined by
# a list of variables
# claims about those variables
# sub_libraries that it depends on
# possibly a name

# The purpose of libraries is to provide a starting point for proofs.
# To start a proof, a user calls library.beginProof() to get a proof
# p. p assumes library.formula() and concludes library.formula().
# After that, the user can call p.forwardFollow(lambda tgt_path: ....)
# to create a more complex proof out of p.
class Library:
  def __init__(self, claims, variables, sub_libraries, name = None):
    for claim in claims:
      if not(isinstance(claim, enrichedFormula.Formula)):
        raise Exception("Claim is not an enriched formula %s."%(claim,))
    global n_libraries
    self.id = n_libraries
    n_libraries += 1
    self.variables = variables
    self.claims = claims
    self.sub_libraries = sub_libraries
    self.name = name

  def __hash__(self):
    return self.id

  def __eq__(self, other):
    return other.__class__ == Library and self.id == other.id
  def __ne__(self, other):
    return not(self == other)

  def all_libraries_recursively(self):
    libraries = Set()
    for library in self.sub_libraries:
      libraries.add(library)
      for l in library.all_libraries_recursively():
        libraries.add(l)
    return libraries

  def formula(self):
    variables = list(self.variables)
    claims = []
    if self.name is None:
      claims.extend(self.claims)
    else:
      claims.append(constructors.Hidden(constructors.And(self.claims), self.name))
    for l in self.all_libraries_recursively():
      variables.extend(l.variables)
      if l.name is None:
        claims.extend(l.claims)
      else:
        claims.append(constructors.Hidden(constructors.Always(constructors.And(l.claims)), l.name))
    return constructors.Always(constructors.Exists(
      [constructors.OrdinaryVariableBinding(v) for v in variables],
      constructors.And(claims)))

  def beginProof(self):
    return Proof(library = self)

# A Proof p represents a logical argument that assumes
# p.assumption() and concludes p.conclusion()
#
# You can think of a proof p as beginning with a library,
# and ending with some tgt_path such that tgt_path.top() == p.conclusion()
#
# If prf is a proof starting with a library L and ending with
# a path P, a user can construct an extended prf by calling:
#  prf.forwardFollow(lambda P:
#    create_some_interesting_path_arrow_with_src_P(P))
class Proof:
  # library: the starting library
  # arrow: a path arrow such that arrow.src.top() == library.formula
  def __init__(self, library, arrow = None):
    self.library = library
    if arrow is None:
      self.arrow = path.new_path(library.formula()).advance()
      self.arrow = self.arrow.forwardFollow(lambda p: p.advance())
      self.arrow = self.arrow.forwardFollow(lambda p: p.forwardAndTrue())
    else:
      assert(arrow.src.top().translate() == library.formula().translate())
      self.arrow = arrow
    self.tgt = self.arrow.tgt

  def starting_library(self):
    return self.library

  def assumption(self):
    return self.library.formula()
  def conclusion(self):
    return self.arrow.tgt.top()

  def translate(self):
    return self.arrow.translate()

  def forwardFollow(self, f):
    return Proof(library = self.library, arrow = self.arrow.forwardFollow(f))

