# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from OpenGL.GL import *
from OpenGL.GLU import *
from OpenGL.GLUT import *

from logic import gl_render
from logic.lib import induction

from stack import gl

import random

startingStack = None

w = 1340
h = 680

scale = 0.18

def init():
  global startingStack
  glutInit()
  glutInitWindowSize(w, h)
  glutCreateWindow("Demo")
  glutDisplayFunc(display)
  glutInitDisplayMode(GLUT_DOUBLE | GLUT_RGBA)
  glClearColor(1.0,1.0,1.0,0.0)
  glColor3f(0.0,0.0, 0.0)
  glMatrixMode(GL_PROJECTION)
  glLoadIdentity()
  gluOrtho2D(0.0, w + 0.0, 0.0, h + 0.0)
  glScale(scale, scale, scale)
  startingStack = gl_render.render(induction.ending_claim)
  glutMainLoop()

def display():
  global startingStack
  glClear(GL_COLOR_BUFFER_BIT)
  startingStack._backend.render()
  glFlush()

def run():
  init()
