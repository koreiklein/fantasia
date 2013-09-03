# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import unittest
from calculus import variable
from calculus.enriched import constructors, endofunctor, bifunctor
from lib import common_vars, common_symbols


class CommonObjects:
  def _and(self, formula):
    return endofunctor.And(values = [formula], index = 1)
  def and_(self, formula):
    return endofunctor.And(values = [formula], index = 0)

  def add_common_objects(self):
    self.a = common_vars.a()
    self.b = common_vars.b()
    self.c = common_vars.c()
    self.d = common_vars.d()
    self.e = common_vars.e()
    self.x = common_vars.x()

    self.A = constructors.Always(constructors.Holds(self.a, self.a))
    self.B = constructors.Always(constructors.Holds(self.b, self.b))

    self.W = constructors.Always(constructors.Holds(self.a, self.b))
    self.X = constructors.Always(constructors.Holds(self.a, self.c))
    self.Y = constructors.Always(constructors.Holds(self.a, self.d))
    self.Z = constructors.Always(constructors.Holds(self.a, self.e))

    self.a_in_domain_b = constructors.Always(constructors.Holds(self.a,
      variable.ApplySymbolVariable(self.b, common_symbols.domainSymbol)))

    self.and_W = self.and_(self.W)
    self.W_and = self._and(self.W)
    self.and_X = self.and_(self.X)
    self.X_and = self._and(self.X)
    self.and_Y = self.and_(self.Y)
    self.Y_and = self._and(self.Y)
    self.and_Z = self.and_(self.Z)
    self.Z_and = self._and(self.Z)

    self.X_and_and_Y = endofunctor.And(values = [self.X, self.Y], index = 1)

    self._and_ = bifunctor.And(values = [], rightIndex = 1, leftIndex = 0)
    self._and__Z_and = self._and_.precomposeRight(self.Z_and)

    self.exists_ = (lambda variables, value:
      constructors.Exists([constructors.OrdinaryVariableBinding(v) for v in variables], value))

    self.W_and_X = constructors.And([self.W, self.X])
    self.X_and_Y_and_Z = constructors.Always(constructors.And([self.X, self.Y, self.Z]))
    self.W_AND_X_and_Y_and_Z = constructors.And([self.W, self.X_and_Y_and_Z])

    self.exists_a_in_domain_b_X_and_Y_and_Z = constructors.Exists(
        [constructors.BoundedVariableBinding(self.a, self.b)], self.X_and_Y_and_Z)

    self.exists_wd_a_in_domain_b_X_and_Y_and_Z = constructors.Exists(
        [constructors.WelldefinedVariableBinding(self.a, self.b)], self.X_and_Y_and_Z)

    self.exists_a = endofunctor.Exists([constructors.OrdinaryVariableBinding(self.a)])
    self.exists_d = endofunctor.Exists([constructors.OrdinaryVariableBinding(self.d)])
    self.exists_d_Y = constructors.Exists(
        bindings = [constructors.OrdinaryVariableBinding(self.d)],
        value = self.Y)
    self.exists_e = endofunctor.Exists([constructors.OrdinaryVariableBinding(self.e)])
    self.exists_d_e = endofunctor.Exists([ constructors.OrdinaryVariableBinding(self.d)
                                         , constructors.OrdinaryVariableBinding(self.e)])

    self.W_or_X = constructors.Or([self.W, self.X])
    self.W_or_X_or_Y = constructors.Or([self.W, self.X, self.Y])
    self.W_or_X_or_Y_or_Z = constructors.Or([self.W, self.X, self.Y, self.Z])

    self.if_W_then_X = constructors.Implies([self.W], self.X)
    self.if_Y_then_X = constructors.Implies([self.Y], self.X)
    self.if_Z_then_Y = constructors.Implies([self.Z], self.Y)

