# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import endofunctor, bifunctor, formula as enrichedFormula


# PRIVATE

# endofunctor: an endofunctor
# yield all pairs bi, x with bi.onRight(x) == endofunctor
def _all_endofunctor_factorizations(endofunctor):
  if endofunctor.is_identity_functor():
    return
  else:
    a, b = endofunctor.factor_left()
    for bi, x in _all_endofunctor_factorizations_of_small_endofunctor(a):
      yield bi.compose(b), x
    for bi, x in _all_endofunctor_factorizations(b):
      yield bi.precomposeLeft(a), x

# ef: a "small" endofunctor.
# yield all pairs bi, x with bi.onRight(x) == endofunctor
def _all_endofunctor_factorizations_of_small_endofunctor(ef):
  if isinstance(ef, endofunctor.Conjunction):
    if ef.__class__ == endofunctor.And:
      bi = bifunctor.And
    else:
      assert(ef.__class__ == endofunctor.Or)
      bi = bifunctor.Or
    for i in range(len(ef.values)):
      values = list(ef.values)
      x = values.pop(i)
      return bi(values = values,
          leftIndex = endofunctor.index - 1 if i < endofunctor.index else endofunctor.index,
          rightIndex = i if i < endofunctor.index else i + 1
          ), x
  else:
    return

# formula: a formula
# yield all pairs ef, x) with ef.onObject(x) == formula
def _all_formula_factorizations(formula):
  for f, y in _all_small_formula_factorizations(formula):
    yield f, y
    for F, Y in _all_formula_factorizations(y):
      yield F.compose(f), Y

# formula: an enriched formula
# yield all pairs F, Y such that F(Y) == formula, and F is "small".
def _all_small_formula_factorizations(formula):
  if formula.__class__ == enrichedFormula.Always:
    yield endofunctor.always_functor, formula.value
  elif formula.__class__ == enrichedFormula.Not:
    yield endofunctor.not_functor, formula.value
  elif formula.__class__ == enrichedFormula.Holds:
    return
  elif formula.__class__ == enrichedFormula.Exists:
    if len(formula.bindings) == 0:
      yield endofunctor.Exists([]), formula.value
    else:
      yield formula.bindings[0], enrichedFormula.Exists(
          bindings = formula.bindings[1:], value = formula.value)
  elif formula.__class__ == enrichedFormula.Hidden:
    yield endofunctor.Hidden(name = formula.name), formula.base
  elif isinstance(formula, enrichedFormula.Conjunction):
    for i in range(len(formula.values)):
      if formula.__class__ == enrichedFormula.And:
        ef = endofunctor.And
      else:
        assert(formula.__class__ == enrichedFormula.Or)
        ef = endofunctor.Or
      values = list(formula.values)
      x = values.pop(i)
      yield ef(values = values, index = i), x
  elif formula.__class__ == enrichedFormula.Iff:
    yield endofunctor.AppendIffRight(formula.right), formula.left
    yield endofunctor.AppendIffLeft(formula.left), formula.right
  else:
    raise Exception("Unrecognized formula class %s"%(formula.__class__,))

class _FormulaConstraint:
  def match(self, formula):
    raise Exception("Abstract superclass.")

  # f: a function f(formula = F(Y), a = f, b = y)
  # note: This method can be super inefficient.  Rewrite it
  #       for a potentially big performance boost.
  #       Consider implementing a separate match_within_formula method for
  #       each subclass of _FormulaConstraint.
  def match_within_formula(self, formula, ef_constraint, f):
    for ef, x in _all_formula_factorizations(formula): # This call is potentially unnecessary.
      # FIXME Remove this.
      assert(ef.onObject(x) == formula)
      for a in self.match(x):
        for b in ef_constraint.match(ef):
          yield f(formula = formula, a = a, b = b)

  # f: a function f(endofunctor = B(., X), a = b, b = x)
  def match_within_ef(self, endofunctor, bi_constraint, f):
    for bi, x in _all_endofunctor_factorizations(endofunctor):
      for b in self.match(x):
        for a in bi_constraint.match(bi):
          yield f(endofunctor = endofunctor, a = a, b = b)

class _Exact(_FormulaConstraint):
  def __init__(self, formula):
    self.formula = formula

  def match(self, formula):
    if formula == self.formula:
      yield formula

class _InvolvingAll(_FormulaConstraint):
  def __init__(self, variables):
    self.variables = variables

  def match(self, formula):
    free = formula.freeVariables()
    for v in self.variables:
      if v not in free:
        return
    yield formula

class _InvolvingAny(_FormulaConstraint):
  def __init__(self, variables):
    self.variables = variables

  def match(self, formula):
    free = formula.freeVariables()
    involved = [v for v in self.variables if v in free]
    if len(involved) != 0:
      yield (formula, involved)

class _AllFormulaConstraints(_FormulaConstraint):
  def __init__(self, formula_constraints, combiner):
    self.formula_constraints = formula_constraints
    self.combiner = combiner

  # Note: This implementation can be terrible for performance.
  #       Rewrite this function for a huge performance increase.
  def match(self, formula):
    def _loop(constraints):
      if len(constraints) == 0:
        yield []
      else:
        first = formula_constraints[0]
        rest = formula_constraints[1:]
        for matched in first.match(formula_constraint):
          for others in _loop(rest):
            result = [matched]
            result.extend(others)
            yield result
    for values in _loop(constraints):
      yield self.combiner(values)

class _Apply(_FormulaConstraint):
  # f: a function f(formula = F(Y), a = f, b = y)
  def __init__(self, formula_constraint, ef_constraint, f):
    self.formula_constraint = formula_constraint
    self.ef_constraint = ef_constraint
    self.f = f

  def match(self, formula):
    return self.formula_constraint.match_within_formula(formula, self.ef_constraint, self.f)

class _EndofunctorConstraint:
  def match(self, endofunctor):
    raise Exception("Abstract superclass.")

class _EndofunctorVariance(_EndofunctorConstraint):
  def __init__(self, covariant):
    self.covariant = covariant

  def match(self, endofunctor):
    if endofunctor.covariant() == self.covariant:
      yield endofunctor

class _ApplyRight(_EndofunctorConstraint):
  def __init__(self, formula_constraint, bi_constraint, f):
    self.formula_constraint = formula_constraint
    self.bi_constraint = bi_constraint
    self.f = f

  def match(self, endofunctor):
    return self.formula_constraint.match_within_ef(endofunctor, bi_constraint, f)

class _BifunctorConstraint:
  def match(self, bifunctor):
    raise Exception("Abstract superclass.")

class _RightVariance(_BifunctorConstraint):
  def __init__(self, covariant):
    self.covariant = covariant

  def match(self, endofunctor):
    if endofunctor.right_covariant() == self.covariant:
      yield endofunctor

# PUBLIC

# The essential objects in the implementation of the factor module will be
# the formula constraints, the endofunctor constraints and the bifunctor constraints.

# Each constraint should be thought of as a possibly infinite set of pairs
#  (B, b) where B is a {formula, endofunctor, bifunctor} and b is any object.

# The factor module provides an interface with 3 kinds of methods:
#   0) Methods for constructing simple constraints.
#   1) Methods for combining constraints in simple ways into complex constraints.
#   2) A match method (called at "the end of the day") for finding all the ways
#   an endofunctor matches an endofunctor constraint.

# covariant: a boolean
# return: an endofunctor constraint
#  { (F, F) | F is a endofunctor with endofunctor.covariant() == covariant }
def variance(covariant):
  return _EndofunctorVariance(covariant)

# covariant: a boolean
# return: a bifunctor constraint
#  { (B, B) | B is a bifunctor with bifunctor.right_covariant() == covariant }
def right_variance(covariant):
  return _RightVariance(covariant)

# formula: a formula
# return: the formula constraint { (formula, formula) }
def exact(formula):
  return _Exact(formula)

# variables: a list of variables
# return: the formula constraint
#         { (X, X) | for v in variables: v is free in X }
def involving_all(variables):
  return _InvolvingAll(variables)

# variables: a list of variables
# return: the formula constraint
#         { (X, (X, involved))
#         | involved != []
#         , for v in involved: (v is free in X and v in variables) }
def involving_any(variables):
  return _InvolvingAny(variables)

# formula_constraint: a formula constraint
# ef_constraint: an endofunctor constraint
# f: a function
# return: the formula constraint
# { (F(Y), f(formula = F(Y), a = f, b = y)) | (F, f) in ef_constraint, (Y, y) in formula_costraint }
def apply(formula_constraint, ef_constraint, f):
  return _Apply(formula_constraint, ef_constraint, f)

# formula_constraints: a list of formula constraints
# f: a function
# return: the formula constraint
#   { (X, c)
#   | exists (X, c0) in formula_constraints[0]
#   , exists (X, c1) in formula_constraints[1]
#   ....
#   , exists (X, c(n-1) in formula_constraints[n-1]
#   , c == f([c0, c1, .... c(n-1)])
def all_formula_constraints(formula_constraints, f):
  return _AllFormulaConstraints(formula_constraints, f)

# formula_constraint: a formula constraint
# bi_constraint: a bifunctor constraint
# f: a function
# return: the endofunctor constraint
# { (B(., X), f(endofunctor = B(., X), a = b, b = x)) |
#   (B, b) in bi_constraint, (X, x) in formula_costraint }
def apply_right(formula_constraint, bi_constraint, f):
  return _ApplyRight(formula_constraint, bi_constraint, f)

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
  return ef_constraint.match(endofunctor)

# bf_constraint: a bifunctor constraint
# bifunctor: a bifunctor
# return: an iterator through all values c such that ((bifunctor, c) in bf_constraint)
def bf_match(bf_constraint, bifunctor):
  return bf_constraint.match(bifunctor)

# formula_constraint: a formula constraint
# formula: a formula
# return: an iterator through all values c such that ((formula, c) in formula_constraint)
def formula_match(formula_constraint, formula):
  return formula_constraint.match(formula)
