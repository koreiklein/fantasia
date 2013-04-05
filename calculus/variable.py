# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

n_variables = 0
class Variable:
  def __init__(self):
    self._generate_id()

  def _generate_id(self):
    global n_variables
    self._id = n_variables
    n_variables += 1

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self._id == other._id
  def __ne__(self, other):
    return not(self == other)
  def __hash__(self):
    return hash(self._id)

  def __repr__(self):
    return "<abstract variable %s>"%(self._id,)

class StringVariable(Variable):
  def __init__(self, name):
    self._generate_id()
    self._name = name

  def name(self):
    return self._name

  def __repr__(self):
    return self.name()
