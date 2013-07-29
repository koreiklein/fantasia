# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from extenders.definer import Definer
from extenders.importer import Importer, CasesImporter
from extenders.inductor import Inductor
from extenders.instantiator import Instantiator
from extenders.reducer import Reducer

class Proof:
  # return: the library that starts this proof.
  def src_library(self):
    raise Exception("Not yet implemented.")

  def src_formula(self):
    return self.src_library().formula()

  # return: the formula at the conclusion of this proof.
  def tgt_formula(self):
    raise Exception("Not yet implemented.")

  # return: the formula at the conclusion of this proof.
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

  # +++++++++++++++++++++ Extender Methods +++++++++++++++++++++
  def importt(self):
    return Importer(self)
  def reduce(self):
    return Reducer(self)
  def instantiate(self):
    return Instantiator(self)
  def cases(self):
    return CasesImporter(self)
  def induct(self):
    return Inductor(self)
  def define(self):
    return Definer(self)

class ProofExtension:
  def src_proof(self):
    raise Exception("Not yet implemented.")
  def tgt_proof(self):
    raise Exception("Not yet implemented.")
  # return an enriched arrow a from
  #   self.src_proof.tgt_formula()
  #  to
  #   self.tgt_proof.tgt_formula()
  def difference(self):
    raise Exception("Not yet implemented.")

  # TODO Is this method usefull?
  # return: a measure of how much simpler this extension makes the proof.
  def simplicity(self):
    raise Exception("Not yet implemented.")

  # TODO Is this method usefull?
  # return: a measure of how much more specific this extension makes the proof.
  def specificity(self):
    raise Exception("Not yet implemented.")

  # TODO Is this method usefull?
  # return: a measure of how much more local power this extension adds to the proof.
  def local_power(self):
    raise Exception("Not yet implemented.")

  # TODO Is this method usefull?
  # return: a measure of the global proof power lost by this extension.
  def global_power(self):
    raise Exception("Not yet implemented.")

