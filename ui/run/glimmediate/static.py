# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from OpenGL.GL import *
from OpenGL.GLU import *
from OpenGL.GLUT import *

from ui.render.gl.render_immediate import render

from ui.stack import gl

import random

startingStack = None

w = 1340
h = 680

scale = 0.15

def display():
  global startingStack
  glClear(GL_COLOR_BUFFER_BIT)
  startingStack.shift([0, 0, 0])._backend.render()
  glFlush()

def run(proof):
  global startingStack
  glutInit()
  glutInitWindowSize(w, h)
  glutCreateWindow("Demo")
  glutDisplayFunc(display)
  glutInitDisplayMode(GLUT_DOUBLE | GLUT_RGBA)
  glEnable(GL_BLEND)
  glBlendFunc(GL_ONE_MINUS_DST_ALPHA, GL_DST_ALPHA)
  glClearColor(1.0,1.0,1.0,0.0)
  glColor3f(0.0,0.0, 0.0)
  glMatrixMode(GL_PROJECTION)
  glLoadIdentity()
  glOrtho(0.0, w + 0.0, 0.0, h + 0.0, -1.0, 1.0)
  glScale(scale, scale, scale)
  startingStack = render(proof.tgt)
  glutMainLoop()
