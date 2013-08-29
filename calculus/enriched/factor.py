# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import endofunctor, bifunctor, formula as enrichedFormula
from calculus.basic.endofunctor import Always, Not


# PRIVATE

# endofunctor: an endofunctor
# yield all pairs bi, x with bi.onRight(x) == endofunctor
def _all_endofunctor_factorizations(ef):
  if endofunctor.is_identity_functor(ef):
    return
  else:
    a, b = ef.factor_left()
    for bi, x in all_endofunctor_factorizations_of_small_endofunctor(a):
      for f, y in _all_formula_factorizations(x):
        yield bi.compose(b).precomposeRight(f), y
    for bi, x in _all_endofunctor_factorizations(b):
      yield bi.precomposeLeft(a), x

# ef: a "small" endofunctor.
# yield all pairs bi, x with bi.onRight(x) == endofunctor
def all_endofunctor_factorizations_of_small_endofunctor(ef):
  if isinstance(ef, endofunctor.Conjunction):
    if ef.__class__ == endofunctor.And:
      bi = bifunctor.And
    else:
      assert(ef.__class__ == endofunctor.Or)
      bi = bifunctor.Or
    for i in range(len(ef.values)):
      values = list(ef.values)
      x = values.pop(i)
      yield bi(values = values,
          leftIndex = ef.index - 1 if i < ef.index else ef.index,
          rightIndex = i if i < ef.index else i + 1
          ), x
  else:
    return

# formula: a formula
# yield all pairs (ef, x) with ef.onObject(x) == formula
def _all_formula_factorizations(formula):
  yield endofunctor.identity_functor, formula
  for f, y in _all_small_formula_factorizations(formula):
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

  # x: a formula
  # covariant: a boolean
  # allowed_variables: a list of variables
  # f: a function
  # return the formula constraint
  #        { (X, f(original = X, arrow = A, substitutions = pairs, y = y)
  #        | (Y, y) in self
  #        , if covariant then (A : X --> Y) else (A : Y --> X)
  #        , A is an instantiation arrow making the substitution
  #        a --> a' iff (a, a') in pairs and a' in allowed_variables }
  def match_replacing(self, x, covariant, allowed_variables, f):
    raise Exception("Abstract superclass.")

  # x: a formula
  # replaceable: a list of variables
  # replacements: a list of variables
  # f: a function
  # return: an iterator over
  #   { f(a = b, pairs = pairs)
  #   | (B, b) in self
  #     B = x.substitute(<a->b for (a,b) in pairs>)
  #     pairs is any list of pairs of variables (a, b) with a in replaceable and b in replacements }
  def match_substituting(self, x, replaceable, replacements, f):
    # FIXME Implement this in subclasses.
    raise Exception("Abstract superclass.")

  # f: a function f(formula = F(Y), a = f, b = y)
  # note: This method can be super inefficient.  Rewrite it
  #       for a potentially big performance boost.
  #       Consider implementing a separate match_within_formula method for
  #       each subclass of _FormulaConstraint.
  def match_within_formula(self, formula, ef_constraint, f):
    for ef, x in _all_formula_factorizations(formula): # This call is potentially unnecessary.
      for a in self.match(x):
        for b in ef_constraint.match(ef):
          yield f(formula = formula, a = a, b = b)

  # f: a function f(endofunctor = B(., X), a = b, b = x)
  def match_within_ef(self, endofunctor, bi_constraint, f):
    for bi, x in _all_endofunctor_factorizations(endofunctor):
      for a in self.match(x):
        for b in bi_constraint.match(bi):
          yield f(endofunctor = endofunctor, a = a, b = b)

class _FormulaReplace(_FormulaConstraint):
  # formula_constraint: a formula constraint
  # covariant: a boolean
  # allowed_variables: a list of variables
  # f: a function
  # construct: the formula constraint
  #        { (X, f(original = X, arrow = A, substitutions = pairs, y = y)
  #        | (Y, y) in formula_constraint
  #        , if covariant then (A : X --> Y) else (A : Y --> X)
  #        , A is an instantiation arrow making the substitution
  #        a --> a' iff (a, a') in pairs and a' in allowed_variables }
  def __init__(self, formula_constraint, covariant, allowed_variables, f):
    self.formula_constraint = formula_constraint
    self.covariant = covariant
    self.allowed_variables = allowed_variables
    self.f = f

  def match_substituting(self, x, replaceable, replacements, f):
    raise Exception("substituting unimplemented in a replace constraint.")

  def match(self, formula):
    return self.formula_constraint.match_replacing(
        x = formula,
        covariant = self.covariant,
        allowed_variables = self.allowed_variables,
        f = self.f)

class _NoFormulaConstraint(_FormulaConstraint):
  def match(self, formula):
    yield formula

  def match_substituting(self, x, replaceable, replacements, f):
    yield f(a = x, pairs = [])

  # x: a formula
  # covariant: a boolean
  # allowed_variables: a list of variables
  # f: a function
  #        { (X, f(original = X, arrow = A, substitutions = pairs, y = y)
  #        | (Y, y) in self
  #        , if covariant then (A : X --> Y) else (A : Y --> X)
  #        , A is an instantiation arrow making the substitution
  #        a --> a' iff (a, a') in pairs and a' in allowed_variables }
  def match_replacing(self, x, covariant, allowed_variables, f):
    yield f(x, x.identity(), [], x)

class _Exact(_FormulaConstraint):
  def __init__(self, formula):
    self.formula = formula

  def match(self, formula):
    if formula == self.formula:
      yield formula

  # x: a formula
  # replaceable: a list of variables
  # replacements: a list of variables
  # f: a function
  # return: an iterator over
  #   { f(a = b, pairs = pairs)
  #   | (B, b) in self
  #     B = x.substitute(<a->b for (a,b) in pairs>)
  #     pairs is any list of pairs of variables (a, b) with a in replaceable and b in replacements }
  def match_substituting(self, x, replaceable, replacements, f):
    pairs = _pairs_to_convert(a = x, b = self.formula)
    if pairs is not None:
      for a, b in pairs:
        if a not in replaceable:
          return
        if b not in replacements:
          return
      yield f(a = self.formula, pairs = pairs)

  # x: a formula
  # covariant: a boolean
  # allowed_variables: a list of variables
  # f: a function
  # return the formula constraint
  #        { (X, f(original = X, arrow = A, substitutions = pairs, y = y)
  #        | (Y, y) in self
  #        , if covariant then (A : X --> Y) else (A : Y --> X)
  #        , A is an instantiation arrow making the substitution
  #        a --> a' iff (a, a') in pairs and a' in allowed_variables }
  def match_replacing(self, x, covariant, allowed_variables, f):
    if (x.__class__ == formula.Exists and not covariant
        and all([b.__class__ == endofunctor.OrdinaryVariableBinding for b in x.bindings])):
      for r in self.match_substituting(
          x = x.value,
          replaceable = [b.variable for b in x.bindings],
          replacements = allowed_variables,
          f = (lambda a, pairs: f(
              original = x,
              arrow = x.backwardInstantiateAll(pairs),
              substitutions = pairs,
              y = a))
          ):
        yield r
    else:
      return

# a, b: formulas
# return: a list of pairs of variables that need to be substituted in a to get b
#         or None if no such list exists.
def _pairs_to_convert(a, b):
  c = a.__class__
  if c == b.__class__:
    if c == enrichedFormula.Exists:
      if (len(a.bindings) == len(b.bindings)
          and all([a.bindings[i] == b.bindings[i] for i in range(len(a.bindings))])):
        return _pairs_to_convert(a.value, b.value)
    elif c == enrichedFormula.Holds:
      pairs = []
      if a.holding != b.holding:
        pairs.append( (a.holding, b.holding) )
      if a.held != b.held:
        pairs.append( (a.held, b.held) )
      return pairs
    elif isinstance(c, enrichedFormula.Conjunction):
      if len(a.values) == len(b.values):
        pairs = []
        for i in range(len(a.values)):
          pairs.extend(_pairs_to_convert(a.values[i], b.values[i]))
    elif c == enrichedFormula.Not:
      return _pairs_to_convert(a.value, b.value)
    elif c == enrichedFormula.Always:
      return _pairs_to_convert(a.value, b.value)
  return None

class _InvolvingAll(_FormulaConstraint):
  def __init__(self, variables):
    self.variables = variables

  def match_substituting(self, x, replaceable, replacements, f):
    # FIXME Implement
    raise Exception("Not yet implemented.")

  def match(self, formula):
    free = formula.freeVariables()
    for v in self.variables:
      if v not in free:
        return
    yield formula

  # x: a formula
  # covariant: a boolean
  # allowed_variables: a list of variables
  # f: a function
  # return the formula constraint
  #        { (X, f(original = X, arrow = A, substitutions = pairs, y = y)
  #        | (Y, y) in self
  #        , if covariant then (A : X --> Y) else (A : Y --> X)
  #        , A is an instantiation arrow making the substitution
  #        a --> a' iff (a, a') in pairs and a' in allowed_variables }
  def match_replacing(self, x, covariant, allowed_variables, f):
    # FIXME Implement this.
    raise Exception("Not yet implemented.")

class _InvolvingAny(_FormulaConstraint):
  def __init__(self, variables):
    self.variables = variables

  def match_substituting(self, x, replaceable, replacements, f):
    # FIXME Implement
    raise Exception("Not yet implemented.")

  def match(self, formula):
    free = formula.freeVariables()
    involved = [v for v in self.variables if v in free]
    if len(involved) != 0:
      yield (formula, involved)

  # x: a formula
  # covariant: a boolean
  # allowed_variables: a list of variables
  # f: a function
  # return the formula constraint
  #        { (X, f(original = X, arrow = A, substitutions = pairs, y = y)
  #        | (Y, y) in self
  #        , if covariant then (A : X --> Y) else (A : Y --> X)
  #        , A is an instantiation arrow making the substitution
  #        a --> a' iff (a, a') in pairs and a' in allowed_variables }
  def match_replacing(self, x, covariant, allowed_variables, f):
    # FIXME Implement this.
    raise Exception("Not yet implemented.")

class _AllFormulaConstraints(_FormulaConstraint):
  def __init__(self, formula_constraints, combiner):
    self.formula_constraints = formula_constraints
    self.combiner = combiner

  def match_substituting(self, x, replaceable, replacements, f):
    # FIXME Implement
    raise Exception("Not yet implemented.")

  # Note: This implementation can be terrible for performance.
  #       Rewrite this function for a huge performance increase.
  def match(self, formula):
    def _loop(constraints):
      if len(constraints) == 0:
        yield []
      else:
        first = constraints[0]
        rest = constraints[1:]
        for matched in first.match(formula):
          for others in _loop(rest):
            result = [matched]
            result.extend(others)
            yield result
    for values in _loop(self.formula_constraints):
      yield self.combiner(values)

  # x: a formula
  # covariant: a boolean
  # allowed_variables: a list of variables
  # f: a function
  # return the formula constraint
  #        { (X, f(original = X, arrow = A, substitutions = pairs, y = y)
  #        | (Y, y) in self
  #        , if covariant then (A : X --> Y) else (A : Y --> X)
  #        , A is an instantiation arrow making the substitution
  #        a --> a' iff (a, a') in pairs and a' in allowed_variables }
  def match_replacing(self, x, covariant, allowed_variables, f):
    # FIXME Implement this.
    raise Exception("Not yet implemented.")

class _Apply(_FormulaConstraint):
  # f: a function f(formula = F(Y), a = f, b = y)
  def __init__(self, formula_constraint, ef_constraint, f):
    self.formula_constraint = formula_constraint
    self.ef_constraint = ef_constraint
    self.f = f

  def match_substituting(self, x, replaceable, replacements, f):
    # FIXME Implement
    raise Exception("Not yet implemented.")

  def match(self, formula):
    return self.formula_constraint.match_within_formula(formula, self.ef_constraint, self.f)

  # x: a formula
  # covariant: a boolean
  # allowed_variables: a list of variables
  # f: a function
  # return the formula constraint
  #        { (X, f(original = X, arrow = A, substitutions = pairs, y = y)
  #        | (Y, y) in self
  #        , if covariant then (A : X --> Y) else (A : Y --> X)
  #        , A is an instantiation arrow making the substitution
  #        a --> a' iff (a, a') in pairs and a' in allowed_variables }
  def match_replacing(self, x, covariant, allowed_variables, f):
    for ef, y in _all_formula_factorizations(x): # This call is potentially unnecessary.
      for a, pairs in self.formula_constraint.match_substituting(
          x = y,
          replaceable = ef.quantified(not covariant), # Those variables quantified in ef.
          replacements = allowed_variables,
          f = (lambda a, pairs:
            (a, pairs))):
        for nt, b in self.ef_constraint.match_replacing_ef(ef, pairs, covariant):
          yield f(original = x,
              arrow = nt(y),
              substitutions = pairs,
              y = self.f(
                formula = x,
                a = a,
                b = b))

class _EndofunctorConstraint:
  def match(self, endofunctor):
    raise Exception("Abstract superclass.")

  # ef: an endofunctor
  # pairs: a list of variables pairs
  # covariant: a boolean
  # yield all pairs nt, b such that:
  #    nt : (if covariant then (ef --> F) else (F --> ef))
  #    (F, b) in self
  def match_replacing_ef(self, ef, pairs, covariant):
    raise Exception("Abstract superclass.")

class _EndofunctorVariance(_EndofunctorConstraint):
  def __init__(self, covariant):
    self.covariant = covariant

  def match(self, endofunctor):
    if endofunctor.covariant() == self.covariant:
      yield endofunctor

  # ef: an endofunctor
  # pairs: a list of variables pairs
  # covariant: a boolean
  # yield all pairs nt, b such that:
  #    nt : (if covariant then (ef --> F) else (F --> ef))
  #    (F, b) in self
  def match_replacing_ef(self, ef, pairs, covariant):
    F, nt = ef.instantiate(covariant, pairs)
    for b in self.match(F):
      yield nt, b

class _ExactEndofunctor(_EndofunctorConstraint):
  def __init__(self, f):
    self.f = f

  def match(self, endofunctor):
    if self.f(endofunctor):
      yield endofunctor

class _ApplyRight(_EndofunctorConstraint):
  def __init__(self, formula_constraint, bi_constraint, f):
    self.formula_constraint = formula_constraint
    self.bi_constraint = bi_constraint
    self.f = f

  def match(self, endofunctor):
    return self.formula_constraint.match_within_ef(endofunctor, self.bi_constraint, self.f)

class _BifunctorConstraint:
  def match(self, bifunctor):
    raise Exception("Abstract superclass.")

class _RightVariance(_BifunctorConstraint):
  def __init__(self, covariant):
    self.covariant = covariant

  def match(self, bifunctor):
    if bifunctor.right_covariant() == self.covariant:
      yield bifunctor

class _LeftVariance(_BifunctorConstraint):
  def __init__(self, covariant):
    self.covariant = covariant

  def match(self, bifunctor):
    if bifunctor.left_covariant() == self.covariant:
      yield bifunctor

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

# Exact endofunctor constraints matching a set of size 1:

# { (Always, Always) }
is_always = _ExactEndofunctor(lambda ef:
    ef.__class__ == endofunctor.DirectTranslate
    and ef.basicEndofunctor.__class__ == Always)
# { (Not, Not) }
is_not = _ExactEndofunctor(lambda ef:
    ef.__class__ == endofunctor.DirectTranslate
    and ef.basicEndofunctor.__class__ == Not)


# The formula constraint { (X, X) | X is any formula }
no_formula_constraint = _NoFormulaConstraint()

# covariant: a boolean
# return: a bifunctor constraint
#  { (B, B) | B is a bifunctor with bifunctor.right_covariant() == covariant }
def right_variance(covariant):
  return _RightVariance(covariant)

# covariant: a boolean
# return: a bifunctor constraint
#  { (B, B) | B is a bifunctor with bifunctor.left_covariant() == covariant }
def left_variance(covariant):
  return _LeftVariance(covariant)

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
  return _FormulaReplace(
      formula_constraint = formula_constraint,
      covariant = covariant,
      allowed_variables = allowed_variables,
      f = f)

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
