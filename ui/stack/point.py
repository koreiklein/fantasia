# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from OpenGL.GL import *

class Point:
  def __init__(self, x, y, z = 0.0):
    self._x = x
    self._y = y
    self._z = z

  def transpose(self):
    return Point(x = self._y, y = self._x, z = self._z)

  def translate(self, dimension, amount):
    if dimension == 0:
      return Point(x = self._x + amount, y = self._y, z = self._z)
    else:
      assert(dimension == 1)
      return Point(x = self._x, y = self._y + amount, z = self._z)

  def render(self):
    glVertex(self._x, self._y, self._z)
