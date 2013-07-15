# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from misc import *

class FinishedInstantiatingException(Exception):
  pass

class Instantiator:
  def instantiate(self, variable, endofunctor, formula):
    raise Exception("Abstract superclass.")
  def exportSide(self, formula, endofunctor):
    raise Exception("Abstract superclass.")

# Statefull.
class InOrderInstantiator(Instantiator):
  def __init__(self, variables):
    self.variables = variables
    self.i = 0
    self.just_exported = False
    self.exports = 0

  def complete(self):
    return self.i == len(self.variables)

  # May throw FinishedInstantiatingException
  def instantiate(self, variable, endofunctor, formula):
    if self.complete():
      raise FinishedInstantiatingException()
    else:
      result = self.variables[self.i]
      self.i += 1
      self.just_exported = False
      return result

  # May throw FinishedInstantiatingException
  def exportSide(self, formula, endofunctor):
    if self.just_exported:
      raise FinishedInstantiatingException()
    else:
      self.just_exported = True
      self.exports += 1
      return left

