# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from OpenGL.GL import *

class Color:
  def __init__(self, r, g, b, a = 1.0):
    self._r = r
    self._g = g
    self._b = b
    self._a = a

  def render(self):
    glColor(self._r, self._g, self._b, self._a)
