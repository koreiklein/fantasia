# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

class Formula:
  def translate(self):
    raise Exception("Abstract superclass.")

class VariableBinding:
  def __init__(self, variable, unique, welldefined):
    self.variable = variable
    self.unique = unique
    self.welldefined = welldefined

class Exists(Formula):
  pass

class Conjunction(Formula):
  pass

class Not(Formula):
  pass

class Always(Formula):
  pass

class Welldefined(Formula):
  pass

class Iff(Formula):
  def __init__(self, left, right):
    self.left = left
    self.right = right
  def __repr__(self):
    return "Iff(\n%s\n<==>\n%s\n)"%(self.left, self.right)
  def __eq__(self, other):
    return other.__class__ == Iff and self.left == other.left and self.right == other.right
  def __ne__(self, other):
    return not(self == other)
  def translate(self):
    return ExpandIff(self.left.translate(), self.right.translate())
  def updateVariables(self):
    return Iff(left = self.left.updateVariables(),
        right = self.right.updateVariables())
  def substituteVariable(self, a, b):
    return Iff(left = self.left.substituteVariable(a, b),
        right = self.right.substituteVariable(a, b))
  def freeVariables(self):
    return self.left.freeVariables().union(self.right.freeVariables())

class Hidden(Formula):
  def __init__(self, base, name):
    self.base = base
    self.name = name

  def __eq__(self, other):
    return other.__class__ == Hidden and self.base == other.base
  def __ne__(self, other):
    return not(self == other)
  # f is a function taking each object B to a list ys
  # return a list of all pairs (a, X) such that
  #   a is an arrow self -> B|self
  #   X is in f(B)
  #   B == Always(C) for some C
  def produceFiltered(self, f):
    # Hidden(X) --> X --> B|X --> B|Hidden(X)
    return [(self.forwardUnhide().forwardCompose(a).forwardFollow(lambda x:
                  x.forwardOnRightFollow(lambda x: x.forwardHide(self.name))), X)
            for a, X in self.base.produceFiltered(f)]

    return self.base.produceFiltered(f)
  def translate(self):
    return self.base.translate()
  def updateVariables(self):
    return Hidden(base = self.base.updateVariables(), name = self.name)
  def substituteVariable(self, a, b):
    return Hidden(base = self.base.substituteVariable(a, b), name = self.name)
  def freeVariables(self):
    return self.base.freeVariables()
  def forwardUnhide(self):
    return Hide(src = self.base, tgt = self).invert()

