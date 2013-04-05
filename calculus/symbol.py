# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>


# This class is used to represent the "symbols" involved in limits and colimits.
# Symbols can be rendered and tested for equality.  They importantly have little
# additional structure.  They need not be string symbols.
n_symbols = 0
class Symbol:
  def __init__(self):
    self._generate_id()

  def _generate_id(self):
    global symbol_id
    self._id = n_symbols
    n_symbols += 1

  def __eq__(self):
    return self.__class__ == other.__class__ and self._id == other._id
  def __ne__(self):
    return not(self == other)
  def __hash__(self):
    return hash(self._id)

  def __repr__(self):
    return "<abstract symbol %s>"%(self._id,)

class StringSymbol(Symbol):
  def __init__(self, s):
    self._generate_id()
    self._string = s

  def __repr__(self):
    return self._s

