# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from mark import markable

from sets import Set

n_variables = 0
class Variable(markable.Markable):
  def __init__(self):
    self._generate_id()
    self.initMarkable([])

  def _generate_id(self):
    global n_variables
    self._id = n_variables
    n_variables += 1

  def assertEqual(self, other):
    if not(self == other):
      raise Exception("Unequal variables %s != %s"%(self, other))

  def updateVars(self):
    return Variable()

  # enriched variables and basic variables share the same representation.
  def translate(self):
    return self

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self._id == other._id
  def __ne__(self, other):
    return not(self == other)
  def __hash__(self):
    return hash(self._id)

  def __repr__(self):
    return "<abstract variable %s>"%(self._id,)

  def substituteVariable(self, a, b):
    if self == a:
      return b
    else:
      return self

  def freeVariables(self):
    return Set([self])

class StringVariable(Variable):
  def __init__(self, name):
    self._generate_id()
    self._name = name
    self.initMarkable([])

  def name(self):
    return self._name

  def __repr__(self):
    return self.name()

  def updateVars(self):
    return StringVariable(self.name())
