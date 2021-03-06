# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

projection = 'projection'
coinjection = 'coinjection'

# This class is used to represent the "symbols" involved in limits and colimits.
# Symbols can be rendered and tested for equality.  They importantly have little
# additional structure.  They need not be string symbols.
n_symbols = 0
class Symbol:
  def __init__(self, type):
    self._generate_id()
    self.type = type

  def _generate_id(self):
    global n_symbols
    self._id = n_symbols
    n_symbols += 1

  def __eq__(self, other):
    return self.__class__ == other.__class__ and self._id == other._id
  def __ne__(self):
    return not(self == other)
  def __hash__(self):
    return hash(self._id)

  def __repr__(self):
    return "<abstract symbol %s>"%(self._id,)

class StringSymbol(Symbol):
  def __init__(self, s, type, infix = None):
    self._generate_id()
    self._string = s
    self.type = type
    self.infix = infix

  def __repr__(self):
    return self._string

