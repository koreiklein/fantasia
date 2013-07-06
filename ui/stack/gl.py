# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from OpenGL.GL import *
from OpenGL.GLU import *
from OpenGL.GLUT import *

from ui.stack import stack

class GLBackend(stack.Backend):
  def __init__(self, render):
    self._render = render

  def render(self):
    return self._render()

  def flip(self):
    def f():
      glScale(-1.0, -1.0, 1.0)
      self.render()
      glScale(-1.0, -1.0, 1.0)
    return GLBackend(f)

  def below(self, other):
    assert(other.__class__ == GLBackend)
    def render():
      self.render()
      other.render()
    return GLBackend(render)

  def shift(self, offset):
    # No 4-Dimensional GLBackends allowed.
    assert(len(offset) <= 3)
    t = [0 for i in range(3)]
    for i in range(len(offset)):
      t[i] = offset[i]
    def render():
      glTranslate(t[0], t[1], t[2])
      self.render()
      glTranslate(-t[0], -t[1], -t[2])
    return GLBackend(render)

  @staticmethod
  def null():
    return GLBackend(lambda: None)

def newGLStack(widths, render):
  return stack.Stack(widths, GLBackend(render))

# TODO: Figure out the correct value to use for this constant.
max_GLUT_STROKE_ROMAN_height = 100.0

def newTextualGLStack(color, string):
  widths = [0 for i in range(3)]
  for x in string:
    widths[0] += glutStrokeWidth(GLUT_STROKE_ROMAN, ord(x))
  widths[1] = max_GLUT_STROKE_ROMAN_height
  def render():
    color.render()
    glPushMatrix()
    for c in string:
      glutStrokeCharacter(GLUT_STROKE_ROMAN, ord(c))
    glPopMatrix()
  return newGLStack(widths, render)

nullStack = newGLStack([0, 0, 0], lambda: None)
