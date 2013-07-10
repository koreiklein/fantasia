# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import unittest
from calculus import variable
from calculus.enriched import constructors, endofunctor
from lib import common_vars, common_symbols


class CommonObjects:
  def add_common_objects(self):
    self.a = common_vars.a()
    self.b = common_vars.b()
    self.c = common_vars.c()
    self.d = common_vars.d()
    self.e = common_vars.e()

    self.A = constructors.Always(constructors.Holds(self.a, self.a))
    self.B = constructors.Always(constructors.Holds(self.b, self.b))

    self.W = constructors.Always(constructors.Holds(self.a, self.b))
    self.X = constructors.Always(constructors.Holds(self.a, self.c))
    self.Y = constructors.Always(constructors.Holds(self.a, self.d))
    self.Z = constructors.Always(constructors.Holds(self.a, self.e))

    self.a_in_domain_b = constructors.Always(constructors.Holds(self.a,
      variable.ApplySymbolVariable(self.b, common_symbols.domainSymbol)))

    self.and_W = endofunctor.And(values = [self.W], index = 0)
    self.W_and = endofunctor.And(values = [self.W], index = 1)
    self.X_and_and_Y = endofunctor.And(values = [self.X, self.Y], index = 1)

    self.W_and_X = constructors.And([self.W, self.X])
    self.X_and_Y_and_Z = constructors.Always(constructors.And([self.X, self.Y, self.Z]))
    self.W_AND_X_and_Y_and_Z = constructors.And([self.W, self.X_and_Y_and_Z])

    self.exists_a_in_domain_b_X_and_Y_and_Z = constructors.Exists(
        [constructors.BoundedVariableBinding(self.a, self.b)], self.X_and_Y_and_Z)

    self.exists_wd_a_in_domain_b_X_and_Y_and_Z = constructors.Exists(
        [constructors.WelldefinedVariableBinding(self.a, self.b)], self.X_and_Y_and_Z)

    self.exists_d = endofunctor.Exists([constructors.OrdinaryVariableBinding(self.d)])
    self.exists_e = endofunctor.Exists([constructors.OrdinaryVariableBinding(self.e)])
    self.exists_d_e = endofunctor.Exists([ constructors.OrdinaryVariableBinding(self.d)
                                         , constructors.OrdinaryVariableBinding(self.e)])

