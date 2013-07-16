# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from misc import *

class FinishedInstantiatingException(Exception):
  pass

class Instantiator:
  def instantiate(self, variable, endofunctor, formula):
    raise Exception("Abstract superclass.")
  def exportSide(self, formula, endofunctor):
    raise Exception("Abstract superclass.")

