# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

class Extender:
  def __init__(self, proof):
    raise Exception("Abstract Superclass.")

  # return: the proof that self is extending.
  def proof(self):
    raise Exception("Abstract Superclass.")

  # return: a list of possible extensions to self.proof()
  def extensions(self):
    raise Exception("Abstract Superclass.")

  # return: the proof associated with the ith extension of self.proof()
  def finish(self, i = 0):
    return self.extensions()[i].tgt_proof()
