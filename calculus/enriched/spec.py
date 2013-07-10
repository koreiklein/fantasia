# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

class Spec:
  def valid(self, formula):
    raise Exception("Abstract superclass.")

class SimpleSearchSpec(Spec):
  def __init__(self, f):
    self.f = f

  def valid(self, formula):
    return self.f(formula)
