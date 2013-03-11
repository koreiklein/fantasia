# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import types
from copy import copy

# A list of Markables.
# The Path is either
#   an upwards path: in which case each Markable contains the previous one
#   a downwards path: in which case each Markable contains the next one
class Path:
  # return True iff this path is of length 1.
  def singleton(self):
    raise Exception("Abstract Superclass")
  # return the first element of this path.  It always exists.
  def first(self):
    raise Exception("Abstract Superclass")
  # return the last element of this path.  It always exists.
  def last(self):
    raise Exception("Abstract Superclass")
  # This must be a downward path.
  # return a new path formed by following mark one step from the end of this path.
  def follow(self, mark):
    raise Exception("Abstract Superclass")
  # This must be a downward path.
  # return a new path formed by following name one step from the end of this path.
  def followName(self, name):
    raise Exception("Abstract Superclass")
  # return True iff this path is a downwards path
  def verifyDownwards(self):
    raise Exception("Abstract Superclass")
  # return True iff this path is an upwards path
  def verifyUpwards(self):
    raise Exception("Abstract Superclass")

class MultiplePath(Path):
  def __init__(self, first, name, rest):
    self._first = first
    self._name = name
    self._rest = rest
  def singleton(self):
    return False
  def first(self):
    return self._first
  # return the rest of this path.
  def rest(self):
    return self._rest
  def last(self):
    return self.rest().last()
  def name(self):
    return self._name
  def follow(self, mark):
    assert(self.verifyDownwards())
    return MultiplePath(first = self.first(), name = self.name(), rest = self.rest().follow(mark))
  def followName(self, name):
    assert(self.verifyDownwards())
    return MultiplePath(first = self.first(), name = self.name(), rest = self.rest().followName(mark))
  def verifyDownwards(self):
    return self.first().followName(self._name) == self.rest().first() and self.rest().verifyDownwards()
  def verifyUpwards(self):
    return self.rest().first().followName(self._name) == self.first() and self.rest().verifyUpwards()
  # return a path like this one but with the last element deleted.
  def retreat(self):
    if self.rest().singleton():
      return SingletonPath(self.first())
    else:
      return MultiplePath(first = self.first(), name = self.name(), rest = self.rest().retreat())
  def __repr__(self):
    return str(self.first()) + "::" + str(self.rest())

class SingletonPath(Path):
  def __init__(self, value):
    self._value = value
  def singleton(self):
    return True
  def first(self):
    return self._value
  def last(self):
    return self._value
  def follow(self, mark):
    assert(self.first().containsMark(mark))
    name = self.first().nameFromMark(mark)
    return self.followName(name)
  def followName(self, name):
    return MultiplePath(first = self.first(), name = name, rest = SingletonPath(self.first().followName(name)))
  def verifyUpwards(self):
    return True
  def verifyDownwards(self):
    return True
  def __repr__(self):
    return str(self.first())

class Markable:
  # Subclasses must call this method as part of __init__.
  # methodNames must be a list of the string names of the methods
  # of this class which can contain marked data.
  # each of those methods must take no arguments and return a markable.
  def initMarkable(self, methodNames):
    self._methodNames = methodNames
    self._descendantMarks = []
    self._marksHere = []
    self._followMark = {} # a dictionary mapping each element of _descendantMarks to the
                          # name of the method which takes you to that mark.
    for name in methodNames:
      child = getattr(self, name)()
      for mark in child._allMarks:
        self._descendantMarks.append(mark)
        self._followMark[mark] = name
    self._allMarks = [] # The union of _marksHere and _descendantMarks
    self._allMarks.extend(self._marksHere)
    self._allMarks.extend(self._descendantMarks)

  def generateMethodNamesForList(self, name, values):
    names = []
    def g(i):
      def f(self):
        return values[i]
      namei = name + str(i)
      self.__dict__[namei] = types.MethodType(f, self)
      names.append(namei)
    for i in range(len(values)):
      g(i) # g is necessary for closure conversion to work properly in python.
    return names

  def marks(self):
    return self._marksHere

  def nameFromMark(self, mark):
    return self._followMark[mark]

  def followName(self, name):
    return getattr(self, name)()

  def follow(self, mark):
    assert(mark in self._descendantMarks)
    name = self._followMark[mark]
    return self.followName(name)

  # return True iff self is marked with mark.
  def markedHere(self, mark):
    return mark in self._marksHere

  # return True iff self or any descendant is marked with mark
  def containsMark(self, mark):
    return mark in self._allMarks

  # self.containsMark(mark) must be true
  # return the downward path from self to mark.
  def getPath(self, mark):
    assert(self.containsMark(mark))
    if self.markedHere(mark):
      return SingletonPath(self)
    else:
      name = self.nameFromMark(mark)
      return MultiplePath(first = self, name = name, rest = self.followName(name).getPath(mark))

  # self must not be marked with mark.
  # return a copy of self, but with mark added.
  def addMark(self, mark):
    assert(mark not in self.marks())
    self = copy(self)
    self._marksHere.append(mark)
    self._allMarks.append(mark)
    return self

  # return a copy of self that is marked with mark.
  def unionMark(self, mark):
    if mark in self.marks:
      return self
    else:
      return self.addMark(mark)

  # return a copy of self marked with the union of the marks of self and other.
  def unionMarksOf(self, other):
    for mark in other.marks():
      self = self.unionMark(mark)

  # self must be marked with mark.
  # return a copy of self that is not marked with mark.
  def removeMark(self, mark):
    self = copy(self)
    assert(mark in self._marksHere)
    assert(mark in self._allMarks)
    self._marksHere.remove(mark)
    self._allMarks.remove(mark)
    return self

