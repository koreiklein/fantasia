# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from OpenGL.GL import *
from OpenGL.GLU import *
from OpenGL.GLUT import *

from ui.render.gl.render_immediate import render

from ui.stack import gl

import random

currentStack = None
remainingClaims = None

w = 1340
h = 680

scale = 0.14

def display():
  global currentStack
  glClear(GL_COLOR_BUFFER_BIT)
  currentStack._backend.render()
  glutSwapBuffers()

def keyboard(key, x, y):
  global currentStack
  global remainingClaims
  remainingClaims.pop(0)
  if key == 'q' or len(remainingClaims) == 0:
    exit()
  else:
    currentStack = render(remainingClaims[0])
    glutPostRedisplay()

def run(claims):
  if len(claims) == 0:
    print "No claims to render in sildeshow."
    return

  global currentStack
  global remainingClaims
  glutInit()
  glutInitWindowSize(w, h)
  glutCreateWindow("Demo")
  glutInitDisplayMode(GLUT_DOUBLE | GLUT_RGBA)
  glutDisplayFunc(display)
  glutKeyboardFunc(keyboard)
  glClearColor(1.0,1.0,1.0,0.0)
  glColor3f(0.0,0.0, 0.0)
  glMatrixMode(GL_PROJECTION)
  glLoadIdentity()
  gluOrtho2D(0.0, w + 0.0, 0.0, h + 0.0)
  glScale(scale, scale, scale)
  currentStack = render(claims[0])
  remainingClaims = claims
  glutMainLoop()
