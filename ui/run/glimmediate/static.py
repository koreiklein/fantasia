# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from OpenGL.GL import *
from OpenGL.GLU import *
from OpenGL.GLUT import *

from ui.stack import gl

import random

startingStack = None

w = 1340
h = 680

scale = 0.12

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
  glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)
  glClearColor(1.0,1.0,1.0,0.0)
  glColor3f(0.0,0.0, 0.0)
  glMatrixMode(GL_PROJECTION)
  glLoadIdentity()
  glOrtho(0.0, w + 0.0, 0.0, h + 0.0, -1.0, 1.0)
  glScale(scale, scale, scale)
  startingStack = proof.tgt.top().top_level_render()
  glutMainLoop()
