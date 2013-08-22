# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import endofunctor, bifunctor

# covariant: a boolean
# return: an endofunctor constraint
#  { (F, F) | F is a endofunctor with endofunctor.covariant() == covariant }
def variance(covariant):
  raise Exception("Not yet implemented.")

# covariant: a boolean
# return: a bifunctor constraint
#  { (B, B) | B is a bifunctor with bifunctor.right_covariant() == covariant }
def right_variance(covariant):
  raise Exception("Not yet implemented.")

# formula: a formula
# return: the formula constraint { (formula, formula) }
def exact(formula):
  raise Exception("Not yet implemented.")

# variables: a list of variables
# return: the formula constraint
#         { (X, X) | for v in variables: v is free in X }
def involving_all(variables):
  raise Exception("Not yet implemented.")

# variables: a list of variables
# return: the formula constraint
#         { (X, (X, involved))
#         | involved != []
#         , for v in involved: (v is free in X and v in variables) }
def involving_any(variables):
  raise Exception("Not yet implemented.")

# formula_constraint: a formula constraint
# ef_constraint: an endofunctor constraint
# f: a function
# return: the formula constraint
# { (F(Y), f(formula = F(Y), a = f, b = y)) | (F, f) in ef_constraint, (Y, y) in formula_costraint }
def apply(formula_costraint, ef_constraint, f):
  raise Exception("Not yet implemented.")

# formula_constraint: a formula constraint
# bi_constraint: a bifunctor constraint
# f: a function
# return: the endofunctor constraint
# { (B(., X), f(endofunctor = B(., X), a = b, b = x)) |
#   (B, b) in bi_constraint, (X, x) in formula_costraint }
def apply_right(formula_constraint, bi_constraint, f):
  raise Exception("Not yet implemented.")

# formula_constraint: a formula constraint
# covariant: a boolean
# allowed_variables: a list of variables
# f: a function
# return the formula constraint
#        { (X, f(original = X, arrow = A, substitutions = pairs, y = y)
#        | (Y, y) in formula_constraint
#        , if covariant then (A : X --> Y) else (A : Y --> X)
#        , A is an instantiation arrow making the substitution
#        a --> a' iff (a, a') in pairs and a' in allowed_variables }
def formula_replace(formula_constraint, covariant, allowed_variables, f):
  raise Exception("Not yet implemented.")

# ef_constraint: an endofunctor constraint
# endofunctor: an endofunctor
# return: an iterator through all values c such that ((endofunctor, c) in ef_constraint)
def ef_match(ef_constraint, endofunctor):
  raise Exception("Not yet implemented.")

