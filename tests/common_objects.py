# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import variable
from calculus.basic import formula, endofunctor
from lib import common_vars

class CommonObjects:
  def add_common_objects(self):
    self.a = common_vars.a()
    self.b = common_vars.b()
    self.c = common_vars.c()
    self.d = common_vars.d()
    self.e = common_vars.e()
    self.b_of_a = formula.Always(formula.Holds(self.a, self.b))
    self.a_of_b = formula.Always(formula.Holds(self.b, self.a))
    self.a_of_a = formula.Always(formula.Holds(self.a, self.a))
    self.b_of_c = formula.Always(formula.Holds(self.c, self.b))
    self.d_of_c = formula.Always(formula.Holds(self.c, self.d))
    self.e_of_e = formula.Always(formula.Holds(self.e, self.e))
    self.and_b_of_a_functor = endofunctor.And(side=endofunctor.left,
                                       other=self.b_of_a)
    self.or_d_of_c_functor = endofunctor.Or(side=endofunctor.left,
                                     other=self.d_of_c)
    self.exists_a_functor = endofunctor.Exists(variable=self.a)
    self.exists_b_functor = endofunctor.Exists(variable=self.b)
    self.exists_c_functor = endofunctor.Exists(variable=self.c)
    self.exists_d_functor = endofunctor.Exists(variable=self.d)
    self.equivalence = variable.StringVariable('equiv')

