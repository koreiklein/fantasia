# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

class Instantiator(Extender):
  # return: a list of variables that need to be assigned.
  def unassigned_variables(self):
    raise Exception("Not yet implemented.")

  # a, b: variables
  # return: an instantiator like self that instantiates a to b.
  def assign(self, a, b):
    raise Exception("Not yet implemented.")

