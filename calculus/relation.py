# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import symbol
from calculus import variable
from calculus import limit
from calculus import enriched

class Holds(enriched.Logic):
  # holding: a variable.Variable
  # held: a variable.Variable or a limit.Limit
  def __init__(self, holding, held):
    assert(isinstance(holding, variable.Variable))
    assert(limit.isLimitOrVariable(held))
    self._holding = holding
    self._held = held

  def holding(self):
    return self._holding
  def held(self):
    return self._held

# These are the standard symbols to be used for functions.
inputSymbol = symbol.StringSymbol('input')
outputSymbol = symbol.StringSymbol('output')

# Special "function" holds objects can be constructed with this function.
def FunctionHolds(functionVariable, input, output):
  assert(isLimitOrVariable(input))
  assert(isLimitOrVariable(output))
  return Holds(holding = functionVariable,
      held = limit.newLimit([ (inputSymbol, input)
                            , (outputSymbol, output)]))

# OLD CODE SECTION

# FROM enriched

# A formula stating that some arbitrary relation holds of some variables.
class Holds(Logic):
  def __init__(self, **kwargs):
    self._d = kwargs
    for (key, value) in kwargs.items():
      self.__dict__[key] = types.MethodType(lambda self: value, self)
    self.initMarkable([])

  def __getitem__(self, x):
    return self._d[x]

  def __repr__(self):
    s = ''
    for (key, value) in self._d.items():
      s += "%s : %s, "%(key, value)
    return s

  def __eq__(self, other):
    if other.__class__ != Holds:
      return False
    else:
      for (key, value) in self._d.items():
        if (not other._d.has_key(key) ) or other[key] != value:
          return False
      for (key, value) in other._d.items():
        if (not self._d.has_key(key) ) or self[key] != value:
          return False
      return True

  def __ne__(self, other):
    return not (self == other)

  def substituteVar(self, a, b):
    _d = {}
    for (key, value) in self._d.items():
      if value == a:
        _d[key] = b
      else:
        _d[key] = value
    return Holds(**_d)

  def translate(self):
    d = {}
    for (key, value) in self._d.items():
      d[key] = value.translate()
    return basic.Holds(**d)

  def transposeIsNot(self):
    return True

  # return a set of the free variables in self.
  def freeVariables(self):
    return self._d.values()


n_vars = 0

class Var(markable.Markable):
  def __init__(self, name):
    self._base = basic.Var(name)
    self.initMarkable([])

  def translate(self):
    return self._base

  def name(self):
    return self.translate().name()

  def __repr__(self):
    return self.name()

  def __eq__(self, other):
    return other.__class__ == Var and self._base == other._base
  def __ne__(self, other):
    return not (self == other)

  def __hash__(self):
    return hash(self._base)

# FROM Basic

class Var:
  def __init__(self, name):
    global n_vars
    self._id = n_vars
    n_vars += 1
    self._name = name

  def name(self):
    return self._name

  def assertEqual(self, other):
    if other.__class__ != Var:
      raise Exception("basic Var unequal to some other object %s of class %s"%(other, other.__class__))
    if self != other:
      raise Exception("Unequal var %s != %s"%(self, other))

  def __repr__(self):
    return self.name()

  def __eq__(self, other):
    return other.__class__ == Var and self._id == other._id
  def __ne__(self, other):
    return not (self == other)

  def __hash__(self):
    return hash(self._id)

class Holds(PrimitiveObject):
  def __init__(self, **kwargs):
    self._d = kwargs
    for (key, value) in kwargs.items():
      self.__dict__[key] = types.MethodType(lambda self: value, self)

  def __getitem__(self, x):
    return self._d[x]

  def __repr__(self):
    return "Holds : %s"%(self._d)

  def __eq__(self, other):
    if other.__class__ != Holds:
      return False
    else:
      for (key, value) in self._d.items():
        if (not other._d.has_key(key) ) or other[key] != value:
          return False
      for (key, value) in other._d.items():
        if (not self._d.has_key(key) ) or self[key] != value:
          return False
      return True

  def assertEqual(self, other):
    assert(other.__class__ == Holds)
    for (key, value) in self._d.items():
      assert(other[key] == value)
    for (key, value) in other._d.items():
      assert(self[key] == value)

  def __ne__(self, other):
    return not (self == other)

  def updateVars(self):
    return self

  def substituteVar(self, a, b):
    _d = {}
    for (key, value) in self._d.items():
      if value == a:
        _d[key] = b
      else:
        _d[key] = value
    return Holds(**_d)
