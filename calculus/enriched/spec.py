# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

class SearchSpec:
  def definitons_only(self):
    return False
  def valid(self, formula):
    raise Exception("Abstract superclass.")
  def search_hidden_formula(self, name):
    raise Exception("Abstract superclass.")

class SimpleSearchSpec(SearchSpec):
  def __init__(self, f):
    self.f = f

  def valid(self, formula):
    return self.f(formula)

  def search_hidden_formula(self, name):
    return True

def equal_translates_search_spec(formula):
  t = formula.translate()
  return SimpleSearchSpec(lambda x: t == x.translate())

