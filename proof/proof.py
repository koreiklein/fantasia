# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

class Proof:
  # return: the library that starts this proof.
  def src_library(self):
    raise Exception("Not yet implemented.")

  def src_formula(self):
    return self.src_library().formula()

  # return: the formula at the conclusion of this proof.
  # self.tgt_formula() == self.endofunctor().onObject(self.current_formula())
  def tgt_formula(self):
    raise Exception("Not yet implemented.")

  # return: the formula of interest at the conclusion of this proof.
  def current_formula(self):
    raise Exception("Not yet implemented.")

  # return: the endofunctor surrounding the conclusion of this proof.
  def endofunctor(self):
    raise Exception("Not yet implemented.")

  # n: an integer
  # return: a new proof in which the selection has been moved up
  #   n times.
  def up(self, n = 0):
    raise Exception("Not yet implemented.")

  # i: None or an integer.
  # if i == None there must be a unque obvious way to descend into self.current_formula()
  # otherwise: self.current_formula() must be an AND or an OR formula.
  # return: a new proof in which the path has been moved down.
  def down(self, i = None):
    raise Exception("Not yet implemented.")

  # self.tgt_formula() must be of the form (And([Or(xs), y)])
  # return: a proof in which y has been distributed over Or(xs)
  def distribute(self):
    raise Exception("Not yet implemented.")

  def covariant(self):
    return self.endofunctor().covariant()

  # +++++++++++++++++++++ Extender Methods +++++++++++++++++++++
  def simplify(self):
    return Simplifier(self)
  def importt(self):
    return Importer(self)
  def reduce(self):
    return Reducer(self)
  def instantiate(self):
    return Instantiator(self)
  def induct(self):
    return Inductor(self)
  def define(self):
    return Definer(self)

# Instances of this class represent ways in which a proof may be extended.
# Frontends may wish to organize and present a list of proof extensions as options
# to the user and allow him to pick which one continues his proof the best.
class ProofExtension:
  def src_proof(self):
    raise Exception("Abstract Superclass.")
  def tgt_proof(self):
    raise Exception("Abstract Superclass.")

  # TODO Is the method at all necessary?
  # return an enriched arrow a from
  #   self.src_proof.tgt_formula()
  #  to
  #   self.tgt_proof.tgt_formula()
  def difference(self):
    raise Exception("Abstract Superclass.")

  # TODO Is this method useful?
  # return: a measure of how much simpler this extension makes the proof.
  def simplicity(self):
    raise Exception("Abstract Superclass.")

  # TODO Is this method useful?
  # return: a measure of how much more specific this extension makes the proof.
  def specificity(self):
    raise Exception("Abstract Superclass.")

  # TODO Is this method useful?
  # return: a measure of how much more local power this extension adds to the proof.
  def local_power(self):
    raise Exception("Abstract Superclass.")

  # TODO Is this method useful?
  # return: a measure of the global proof power lost by this extension.
  def global_power(self):
    raise Exception("Abstract Superclass.")

# Instances of this class manage a set of proof extensions.
# Each subclass defines which kinds of proof extensions it will manage
# and defines ways to filter and process those proof extensions before
# picking which one to use to extend the proof.
class Extender:
  # return: the proof that self is extending.
  def proof(self):
    raise Exception("Abstract Superclass.")

  # return: a list of possible extensions to self.proof()
  def extensions(self):
    raise Exception("Abstract Superclass.")

  # return: the proof associated with the ith extension of self.proof()
  def finish(self, i = 0):
    return self.extensions()[i].tgt_proof()

  def current_formula(self):
    return self.proof().current_formula()

  def covariant(self):
    return self.proof().covariant()

# An Extender for producing extensions that increase simplicity and do
# not decrease global power.
class Simplifier(Extender):
  def __init__(self, proof):
    self._proof = proof
  def proof(self):
    return self._proof
  def extensions(self):
    return [self.light(), self.heavy()]

  # return: a proof extension that applies
  #   local arrows to produce an equally globally and locally powerfull yet possibly
  #   simpler self.current_formula()
  def light(self):
    raise Exception("Not yet implemented.")

  # return: a proof extension that
  #   applies local arrows
  #   and performs exports
  #   and makes universal choices (e.g. picking the right side of an Or in a contravariant spot
  #                                     when it can infer that the left side is false)
  #   to produce an equally globally powerfull yet possibly simpler self.current_formula()
  def heavy(self):
    raise Exception("Not yet implemented.")

# This extender is for generating proof extensions that move a formula
# close to self.current_formula().
class Importer(Extender):
  def __init__(self, proof):
    raise Exception("Not yet implemented.")

  # return: an importer which imports a formula x iff:
  #         x is of the form Or(xs)
  #         x is importable from self
  def cases(self):
    raise Exception("Not yet implemented.")

  # return: an importer importing all formulas of self which can be imported safely.
  #   [An import is safe if the imported formula can be copied so as not to disappear
  #    from its original location.  Safe imports are typically imports of formulas
  #    that occur within an Always].
  def safe(self):
    raise Exception("Not yet implemented.")

  # formula: an enriched formula
  # return: a specific importer for formula
  def specific(self, formula):
    return SpecificImporter(proof, formula)

  # i: None or an integer
  # return: an importer importing all formulas of self in which
  #         exactly N variables are existentially quantified within a single Not
  #         and
  #         either i == N, or i is None and N > 0
  def universal(self, i):
    raise Exception("Not yet implemented.")

  # variables: a set of variables
  # return: an importer importing all formulas of self in which all of the variables
  #         in variables are free.
  def involvingVariables(self, variables):
    raise Exception("Not yet implemented.")

  # name: a string
  # return: an importing importing all formulas of self which come from a formula
  #         hidden by name.
  #  This method should be most useful for things like importing a formula that the user
  #  knows comes from a particular library.
  def hiddenBy(self, name):
    raise Exception("Not yet implemented.")

  # f: a function from formulas to booleans.
  # return: an importing importing all formulas x of self such that f(x) == True
  def filterWithFunction(self, f):
    raise Exception("Not yet implemented.")

  # variables: a list of variables in scope at self.
  # return: an importer importing a formula x iff there exists a formula y
  #         importable in self such that x is obtained from y by instantiating y
  #         with variables in a reasonable way.
  # e.g. if n is a variable in scope at self such that (n : Natural) and (n > 2)
  #      are the only interesting properties n is known to possess,
  #      self.about([n]) should return an importer that imports formulas that say something
  #      interesting about n that follows from n being natural and/or n being greater than 2.
  # Note: The above description intentionally does not totally specify the behavior of about.
  #       The implementer of about is therefore burdened with a certain amount of freedom
  #       in choosing an implementation.
  def about(self, variables):
    raise Exception("Not yet implemented.")

# This Extender is for importing one particular formula.
class SpecificImporter(Extender):
  def __init__(self, proof, formula):
    self._proof = proof
    self._formula = formula

  # return: the formula that self will attempt to import.
  def formula(self):
    return self._formula

  def proof(self):
    return self._proof

  def extensions(self):
    if self.available():
      return [self.infer(), self.assume()]
    else:
      return [self.assume()]

  # return: True iff self.formula() can be imported.
  #   self.available() == True iff self.infer() doesn't throw an exception.
  def available(self):
    raise Exception("Not yet implemented.")

  # return: a proof extension importing self.formula()
  #         or throw a calculus.basic.endofunctor.UnimportableException
  #         if self.formula() can't be imported.
  def infer(self):
    raise Exception("Not yet implemented.")

  # assume is meant to be used when self.formula() is not importable.
  # return: a proof extension which adds self.formula() by assuming it.
  def assume(self):
    raise Exception("Not yet implemented.")

# This Extender is for choosing a proof extension that instantiates
# the variables of self.current_formula() with other variables that
# are in scope.
class Instantiator(Extender):
  # return: a list of variables that need to be assigned.
  def unassigned_variables(self):
    raise Exception("Not yet implemented.")

  # a, b: variables
  # return: an instantiator like self that instantiates a to b.
  def assign(self, a, b):
    raise Exception("Not yet implemented.")

# This Extender is for making use of mathematical induction.
class Inductor(Extender):
  # self must be covariant.
  # self.current_formula() must be an Exists
  # a: a variable quantified as a natural by self.current_formula()
  # return: a proof extension that reduces self.current_formula()
  #         to a base case and a step case.
  #  Note: This method is for use on a self.current_formula() that we
  #        are attempting to CONTRADICT.
  def reduce(self, a):
    raise Exception("Not yet implemented.")

  # self must be covariant.
  # formula: a universal formula.
  # a: a variable quantified as a natural by formula.
  # return: a proof extension that appends the claim that formula
  #         follows from a base case and a step case.
  def show(self, formula, a):
    raise Exception("Not yet implemented.")

# This Extender is for adding definitions to self.proof()
class Definer(Extender):
  pass

# This Extender is for replacing self.current_formula() with a more
# specific claim which may make the proof globally weaker.
# In covariant spots, a Reducer finds things that follow from self.current_formula().
# In contravariant spots, a Reducer finds things that imply self.current_formula().
class Reducer(Extender):
  # return a reducer that reduces only with the reductions of self which
  #   are invertible.
  def equialences(self):
    raise Exception("Not yet implemented.")

