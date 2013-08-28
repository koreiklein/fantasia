# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from sets import Set

from misc import *
import misc
from calculus.variable import ApplySymbolVariable, ProductVariable, StringVariable, Variable
from calculus.enriched import spec, formula as formula
from calculus.basic import formula as basicFormula
from calculus.basic import endofunctor as basicEndofunctor
from calculus.basic import bifunctor as basicBifunctor
from calculus.basic import instantiator
from lib import common_symbols, common_vars
from lib.common_symbols import leftSymbol, rightSymbol, relationSymbol, domainSymbol

from ui.render.text import primitives, colors, distances
from ui.stack import stack

def combine_variances(a, b):
  return a if b else not a

def Maps(a, b, f):
  return basicFormula.Holds(
      ProductVariable([ (common_symbols.inputSymbol, a)
                               , (common_symbols.outputSymbol, b)]),
      ApplySymbolVariable(f, common_symbols.functionPairsSymbol))

class Endofunctor:
  # return a basic endofunctor
  def translate(self):
    raise Exception("Abstract superclass.")
  def covariant(self):
    raise Exception("Abstract superclass.")

  # return: F, a natural transform instantiating a->b for (a, b) in pairs
  #         if covariant it goes self --> F
  #         otherwise it goes    F --> self
  def instantiate(self, covariant, pairs):
    return (self, lambda x: self.onObject(x).identity())

  def is_and_functor(self):
    return False

  def updateVariables(self):
    raise Exception("Abstract superclass.")

  def onObject(self, x):
    raise Exception("Abstract superclass.")

  # spec: a SearchSpec instance.
  # return: if self.covariant(): a list of claims importable at self matching spec
  #         otherwise:  a list of claims exportable at self matching spec
  def search(self, spec):
    raise Exception("Abstract superclass.")

  # replace all existentially quantified and free variables a in self with b.
  def replace(self, a, b):
    return self

  # return: the set of variables quantified at certain spots in this endofunctor.
  #         Only use covariant spots iff covariant, otherwise use contravariant spots.
  def quantified(self, covariant):
    return Set([])

  # self must not be the identity functor.
  # return a pair of endofunctors (a, b) such that a.compose(b) == self, a is non-trivial
  # and a is "as small as possible".
  def factor_left(self):
    return (self, identity_functor)

  # self must not be the identity functor.
  # return a pair of endofunctors (a, b) such that a.compose(b) == self, b is non-trivial
  # and b is "as small as possible".
  def factor_right(self):
    return (identity_functor, self)

  def onArrow(self, arrow):
    if self.is_identity():
      return arrow
    else:
      basicArrow = self.translate().onArrow(arrow.translate())
      if self.covariant():
        src = self.onObject(arrow.src)
        tgt = self.onObject(arrow.tgt)
      else:
        src = self.onObject(arrow.tgt)
        tgt = self.onObject(arrow.src)
      return formula.Arrow(src = src, tgt = tgt, basicArrow = basicArrow)

  def compose(self, other):
    if other.is_identity():
      return self
    elif self.is_identity():
      return other
    else:
      return Composite(self, other)

  def is_identity(self):
    return is_identity_functor(self)

  # self must be contravariant
  # formula: an Exists formula.
  # variables: a list of variable in scope in self.
  # return: a pair (arrow, value) such that arrow.tgt == self.onObject(value) and arrow instantiates the exists formula
  #         with the given variables.
  def instantiateInOrder(self, variables, x):
    assert(not self.covariant())
    assert(x.__class__ == formula.Exists)
    assert(len(variables) == len(x.bindings))
    value = fully_substituted(variables, x)
    ins = InOrderInstantiator(variables)
    basicArrow = self.translate().exportRecursively(ins, x.translate())
    if not ins.complete():
      raise Exception("Instantiation did not complete.")
    result = formula.Arrow(src = self.onObject(x),
        tgt = self.onObject(value),
        basicArrow = basicArrow)
    return result, value

  def exportAutomaticallFromAnd(self, x):
    assert(not self.covariant())
    def try_export(y):
      if y.__class__ == basicFormula.Always:
        return y.value.__class__ == basicFormula.Holds
      else:
        return y.__class__ == basicFormula.Holds
    xs, basicArrow = self.translate().exportNestedAnd(x.translate(), len(x.values), try_export)
    newValues = []
    for i in range(len(x.values)):
      if xs[i] == False:
        newValues.append(x.values[i])
    newX = formula.And(newValues)
    result = formula.Arrow(src = self.onObject(x), tgt = self.onObject(newX),
        basicArrow = basicArrow)
    return result, newX

  def importExactly(self, B):
    assert(self.covariant())
    return (lambda x:
        formula.Arrow(src = self.onObject(x),
          tgt = self.onObject(formula.And([B, x])),
          basicArrow = self.translate().importExactly(B.translate())(x.translate())))

class Substitute(Endofunctor):
  def __init__(self, oldVariable, newVariable):
    self.oldVariable = oldVariable
    self.newVariable = newVariable

  def translate(self):
    return basicEndofunctor.SubstituteVariable(
        oldVariable = self.oldVariable,
        newVariable = self.newVariable)
  def covariant(self):
    return True
  def is_and_functor(self):
    return False
  def updateVariables(self):
    return self
  def onObject(self, x):
    return x.substituteVariable(self.oldVariable, self.newVariable)
  def replace(self, a, b):
    if a == self.newVariable:
      return Substitute(self.oldVariable, b)
    else:
      return self
def fully_substituted(variables, x):
  assert(x.__class__ == formula.Exists)
  value = x.value
  for i in range(len(variables)):
    value = value.substituteVariable(x.bindings[i].variable, variables[i])
  return value

class Composite(Endofunctor):
  # if right is covariant, self will represent (left o right)
  # otherwise secod is contravariant, and self will represent (oppositeFunctor(left) o right)
  def __init__(self, left, right):
    assert(isinstance(left, Endofunctor))
    assert(isinstance(right, Endofunctor))
    self.left = left
    self.right = right

  def instantiate(self, covariant, pairs):
    F, nt0 = self.left.instantiate(combine_variances(covariant, self.right.covariant()), pairs)
    G, nt1 = self.right.instantiate(covariant, pairs)
    # Horizontal composite.  I'm somewhat certain it works in all 8 cases, but we should test
    # to be sure.
    return (F.compose(G), lambda x:
        (lambda a, b: a.forwardCompose(b) if covariant else b.forwardCompose(a))(
            a = self.right.onArrow(nt0(x)),
            b = nt1(F.onObject(x))))

  def quantified(self, covariant):
    a = self.right.quantified(covariant)
    b = self.left.quantified(combine_variances(covariant, self.right.covariant()))
    return a.union(b)

  def replace(self, a, b):
    return self.left.replace(a, b).compose(self.right.replace(a, b))

  def search(self, spec):
    # Note: It surprising how simple the below code needs to be.
    # koreiklein was able to conclude that this implementation was correct only after reasoning
    # through all 4 possible combinations of variances of left and right.
    result = list(self.right.search(spec))
    result.extend(self.left.search(spec))
    return result

  def onObject(self, object):
    return self.right.onObject(self.left.onObject(object))

  def onArrow(self, arrow):
    return self.right.onArrow(self.left.onArrow(arrow))

  def __repr__(self):
    return "%s o\n%s"%(self.left, self.right)

  def is_and_functor(self):
    return self.right.is_and_functor()

  def factor_left(self):
    if is_identity_functor(self.right):
      return self.left.factor_left()
    elif is_identity_functor(self.left):
      return self.right.factor_left()
    else:
      a, b = self.left.factor_left()
      return (a, b.compose(self.right))

  def factor_right(self):
    if is_identity_functor(self.right):
      return self.left.factor_right()
    elif is_identity_functor(self.left):
      return self.right.factor_right()
    else:
      a, b = self.right.factor_right()
      return (self.left.compose(a), b)

  def translate(self):
    return self.left.translate().compose(self.right.translate())
  def covariant(self):
    if self.left.covariant():
      return self.right.covariant()
    else:
      return not self.right.covariant()

class VariableBinding(Endofunctor):
  # return: an endofunctor representing existential quantification
  #         over this variable.
  def translate(self):
    raise Exception("Abstract superclass.")
  def covariant(self):
    raise Exception("Abstract superclass.")
  def updateVariables(self):
    raise Exception("Abstract superclass.")
  def replace(self, a, b):
    raise Exception("Abstract superclass.")
  def onObject(self, x):
    assert(x.__class__ == formula.Exists)
    bindings = [self]
    bindings.extend(x.bindings)
    return formula.Exists(bindings = bindings, value = x.value)
  def is_and_functor(self):
    return False
  def is_identity_functor(self):
    return False
  
  def quantified(self, covariant):
    if covariant:
      return Set([self.variable])
    else:
      return Set([])

  def render(self, context):
    return primitives.newTextStack(colors.variableColor, repr(self))
  def is_ordinary(self):
    return False

  def assertBoundedNatural(self):
    assert(self.__class__ == BoundedVariableBinding)
    assert(self.relation == common_vars.natural)

  # other: a VariableBinding instance.
  # return: an arrow representing a basic natural transform: self o other --> other o self
  def commute(self, other):
    if self.__class__ == BoundedVariableBinding and other.__class__ == BoundedVariableBinding:
      # E v . A | (E w . B | C) --> E v . (E w . A | (B | C))
      # --> E v . E w . A | (C | B) --> E v . E w . (A | C) | B --> E v . E w . B | (A | C)
      # --> E w . E v . B | (A | C) --> E w . B | (E v . A | C)
      return (lambda x:
          other.translate().onObject(self.translate().onObject(x)).forwardOnBodyFollow(lambda x:
            x.forwardAndPastExists().forwardFollow(lambda x:
              x.forwardOnBodyFollow(lambda x:
                x.forwardOnRightFollow(lambda x:
                  x.forwardCommute()).forwardFollow(lambda x:
                    x.forwardAssociateOther().forwardFollow(lambda x:
                      x.forwardCommute()))))).forwardFollow(lambda x:
                        x.forwardCommuteExists()).forwardFollow(lambda x:
                          x.forwardOnBodyFollow(lambda x:
                            x.forwardExistsPastAnd())))
    elif self.__class__ == BoundedVariableBinding and other.__class__ == OrdinaryVariableBinding:
      # E v . E w . B | C --> E w . E v . B | C --> E w . (B | E v . C)
      return (lambda x:
          other.translate().onObject(self.translate().onObject(x)).forwardCommuteExists().forwardFollow(lambda x:
            x.forwardOnBodyFollow(lambda x:
              x.forwardExistsPastAnd())))
    elif self.__class__ == OrdinaryVariableBinding and other.__class__ == BoundedVariableBinding:
      # E v . A | (E w . C) --> E v . E w . A | C --> E w . E v . A | C
      return (lambda x:
          other.translate().onObject(self.translate().onObject(x)).forwardOnBodyFollow(lambda x:
            x.forwardAndPastExists()).forwardFollow(lambda x:
              x.forwardCommuteExists()))
    else:
      raise Exception("Unrecognized pair of bindings (%s, %s)"%(self, other))


  # spec: a SearchSpec instance
  # return: a list of claims importable from the translation of self.
  def search(self, spec):
    raise Exception("Abstract superclass.")

class BoundedVariableBinding(VariableBinding):
  def __init__(self, variable, relation):
    self.variable = variable
    self.relation = relation
    self.domain = ApplySymbolVariable(self.relation, common_symbols.domainSymbol)
    self.inDomain = formula.Always(formula.Holds(held = self.variable,
      holding = self.domain))

  # return: F, a natural transform instantiating a->b for (a, b) in pairs
  #         if covariant it goes self --> F
  #         otherwise it goes    F --> self
  def instantiate(self, covariant, pairs):
    if not covariant:
      for a, b in pairs:
        if a == self.variable:
          F = Substitute(a, b).compose(
              And(values = [self.inDomain.substituteVariable(a, b)], index = 1))
          nt = (lambda x: formula.Arrow(tgt = self.onObject(x),
            src = formula.And([self.inDomain, x]).substituteVariable(a, b),
            basicArrow = self.onObject(x).translate().backwardIntroExists(b)))
          return F, nt
    return (self, lambda x: self.onObject(x).identity())

  def replace(self, a, b):
    return BoundedVariableBinding(
        variable = self.variable.substituteVariable(a, b),
        relation = self.relation.substituteVariable(a, b))

  def updateVariables(self):
    return BoundedVariableBinding(variable = self.variable.updateVariables(),
        relation = self.relation)

  def __repr__(self):
    return "%s : %s"%(self.variable, self.relation)

  def translate(self):
    return basicEndofunctor.And(side = right,
                                other = self.inDomain.translate()).compose(
            basicEndofunctor.Exists(self.variable))
  def covariant(self):
    return True

  def search(self, spec):
    return [claim for claim in [self.inDomain] if spec.valid(claim)]

  def render(self, context):
    return (renderBoundedVariableBinding(self.variable, self.domain), context)

def renderBoundedVariableBinding(variable, domain):
  middleStack = primitives.newTextStack(colors.variableColor, ":")
  return variable.render().stack(0, middleStack,
      spacing = distances.variable_binding_spacing).stackCentered(0, domain.render(),
          spacing = distances.variable_binding_spacing)

class OrdinaryVariableBinding(VariableBinding):
  def __init__(self, variable):
    self.variable = variable

  # return: F, a natural transform instantiating a->b for (a, b) in pairs
  #         if covariant it goes self --> F
  #         otherwise it goes    F --> self
  def instantiate(self, covariant, pairs):
    if not covariant:
      for a, b in pairs:
        if a == self.variable:
          return (Substitute(a,b),
              lambda x: formula.Arrow(tgt = self.onObject(x),
                src = x.substituteVariable(a, b),
                basicArrow = self.onObject(x).translate().backwardIntroExists(b)))
    return (self, lambda x: self.onObject(x).identity())

  def __repr__(self):
    return repr(self.variable)

  def replace(self, a, b):
    return OrdinaryVariableBinding(self.variable.substituteVariable(a, b))

  def is_ordinary(self):
    return True

  def updateVariables(self):
    return OrdinaryVariableBinding(self.variable.updateVariables())

  def covariant(self):
    return True

  def translate(self):
    return basicEndofunctor.Exists(self.variable)

  def render(self, context):
    return (self.variable.render(), context)

  def search(self, spec):
    return []

class Hidden(Endofunctor):
  def __init__(self, name):
    self.name = name
  def translate(self):
    return basicEndofunctor.identity_functor
  def covariant(self):
    return True
  def updateVariables(self):
    return self
  def onObject(self, x):
    return formula.Hidden(self.name, x)

class AppendIffRight(Endofunctor):
  def __init__(self, x):
    assert(x.__class__ == formula.Not)
    assert(x.value.__class__ == formula.And)
    assert(len(x.value.values) == 2)
    assert(x.value.values[1].__class__ == formula.Not)
    self.formula = x
    self.coformula = formula.Not(
        formula.And([x.value.values[1].value,
          formula.Not(x.values.values[0])]))

  def translate(self):
    return basicEndofunctor.And(side = left,
        other = self.coformula.translate())
  def covariant(self):
    return True
  def updateVariables(self):
    return AppendIffRight(self.formula.updateVariables())
  def onObject(self, x):
    assert(x == self.coformula)
    return formula.Iff(left = x, right = self.formula)

class AppendIffLeft(Endofunctor):
  def __init__(self, x):
    assert(x.__class__ == formula.Not)
    assert(x.value.__class__ == formula.And)
    assert(len(x.value.values) == 2)
    assert(x.value.values[1].__class__ == formula.Not)
    self.formula = x
    self.coformula = formula.Not(
        formula.And([x.value.values[1].value,
          formula.Not(x.values.values[0])]))

  def translate(self):
    return basicEndofunctor.And(side = right,
        other = self.coformula.translate())
  def covariant(self):
    return True
  def updateVariables(self):
    return AppendIffLeft(self.formula.updateVariables())
  def onObject(self, x):
    assert(x == self.coformula)
    return formula.Iff(left = self.formula, right = x)

class WelldefinedVariableBinding(VariableBinding):
  # variable: a variable
  # relation: an equivalence relation
  def __init__(self, variable, relation):
    self.variable = variable
    self.relation = relation
    self.inDomain = formula.InDomain(self.variable, self.relation)

  def __repr__(self):
    return "%s wd in %s"%(self.variable, self.relation)

  def translate(self):
    newVariable = Variable()
    andInDomain = basicEndofunctor.And(side = right, other = self.inDomain.translate())
    existsV = basicEndofunctor.Exists(self.variable)
    wd = formula.ExpandWellDefined(self.variable, newVariable, self.relation)

    return andInDomain.compose(wd).compose(existsV)

  def render(self, context):
    # TODO Render in a clearer way.
    return (self.variable.render(), context)

  def search(self, spec):
    # TODO consider allow to search for more.
    return [claim for claim in [self.inDomain]
        if spec.valid(claim)]

class Exists(Endofunctor):
  def __init__(self, bindings):
    self.bindings = bindings

  def instantiate(self, covariant, pairs):
    if covariant:
      return (self, lambda x: self.onObject(x).identity())
    else:
      # FIXME This code fails for BoundedVariableBindings.
      #       The call to backwardInstantiateAll doesn't even yet work if some
      #       of the variables are part of BoundedVariableBindings.
      pairs_to_use_here = []
      remaining_bindings = []
      for binding in self.bindings:
        for a, b in pairs:
          if binding.variable == a:
            pairs_to_use_here.append( (a, b))
          else:
            remaining_bindings.append(binding)
      return (Exists(remaining_bindings),
          lambda x: self.onObject(x).backwardInstantiateAll(pairs_to_use_here))

  def quantified(self, covariant):
    if covariant:
      return Set([b.variable for b in self.bindings])
    else:
      return Set([])

  def replace(self, a, b):
    return Exists([binding.replace(a, b) for binding in self.bindings])

  def __repr__(self):
    return "Exists%s"%(self.bindings,)

  def onObject(self, object):
    return formula.Exists(bindings = self.bindings, value = object)

  def covariant(self):
    return True

  def translate(self):
    result = basicEndofunctor.identity_functor
    for binding in self.bindings[::-1]:
      result = result.compose(binding.translate())
    return result

  def search(self, spec):
    result = []
    for binding in self.bindings:
      result.extend(binding.search(spec))
    return result

class DirectTranslate(Endofunctor):
  def __init__(self, basicEndofunctor, _onObject):
    self.basicEndofunctor = basicEndofunctor
    self._onObject = _onObject
  def __repr__(self):
    return "direct(%s)"%(self.basicEndofunctor,)
  def translate(self):
    return self.basicEndofunctor
  def search(self, spec):
    return []
  def covariant(self):
    return self.basicEndofunctor.covariant()
  def onObject(self, object):
    return self._onObject(object)
  def factor_left(self):
    if is_identity_functor(self):
      raise Exception("Can't factor the identity functor.")
    else:
      return (self, identity_functor)
  def factor_right(self):
    if is_identity_functor(self):
      raise Exception("Can't factor the identity functor.")
    else:
      return (identity_functor, self)

  def updateVariables(self):
    return self

always_functor = DirectTranslate(basicEndofunctor.always_functor,
    _onObject = formula.Always)
not_functor = DirectTranslate(basicEndofunctor.not_functor,
    _onObject = formula.Not)
identity_functor = DirectTranslate(basicEndofunctor.identity_functor,
    _onObject = lambda x: x)

def is_identity_functor(f):
  return f.__class__ == DirectTranslate and f.basicEndofunctor.__class__ == basicEndofunctor.Id

class Conjunction(Endofunctor):
  def __init__(self, values, index):
    self.values = values
    self.index = index
    self.first = values[:index]
    self.rest = values[index:]

  def replace(self, a, b):
    return self.__class__(values = [value.replace(a, b) for value in self.values],
        index = self.index)

  def __repr__(self):
    values = [repr(value) for value in self.values]
    values.insert(self.index, '.')
    result = self.name() + "[ " + ','.join(values) + " ]"
    return result

  def covariant(self):
    return True

  def onObject(self, object):
    newValues = list(self.values)
    newValues.insert(self.index, object)
    return self.multiOp()(newValues)

  def translate(self):
    # e.g.
    # self.values = [a, b, c, d]
    # self.index = 2
    # self.rest = [c, d]
    # self.first = [a, b]
    # [a, b, ., c, d] -> a|(b|(.|(c|(d|1))))
    if len(self.rest) > 0:
      back = self.multiOp()(self.rest).translate()
      result = self.basicEndofunctor()(side = left, other = back)
    else:
      result = basicEndofunctor.identity_functor
    for value in self.first[::-1]:
      result = result.compose(self.basicEndofunctor()(side = right, other = value.translate()))
    return result

class And(Conjunction):
  def is_and_functor(self):
    return True

  def name(self):
    return 'AND'

  def basicEndofunctor(self):
    return basicEndofunctor.And
  def multiOp(self):
    return formula.And

  def search(self, spec):
    result = []
    for value in self.values:
      result.extend(value.search(spec))
    return result

class Or(Conjunction):
  def name(self):
    return 'OR'
  def basicEndofunctor(self):
    return basicEndofunctor.Or
  def multiOp(self):
    return formula.Or

  def search(self, spec):
    return []

class WellDefinedFunctor(Endofunctor):
  def __init__(self, variable, newVariable, equivalence):
    self.variable = variable
    self.newVariable = newVariable
    self.equivalence = equivalence
    self.expanded = formula.ExpandWellDefined(variable, newVariable, equivalence)

  def search(self, spec):
    inDomain = formula.InDomain(self.variable, self.equivalence)
    return [claim for claim in [inDomain] if spec.valid(claim)]

  def onObject(self, object):
    return formula.WellDefined(
        variable = self.variable,
        newVariable = self.newVariable,
        equivalence = self.equivalence,
        value = object)

  def covariant(self):
    return True
  def translate(self):
    return self.expanded

def same_structure(x, y):
  if x.__class__ == formula.Always:
    return y.__class__ == formula.Always and same_structure(x.value, y.value)
  elif x.__class__ == formula.Not:
    return y.__class__ == formula.Not and same_structure(x.value, y.value)
  elif isinstance(x, formula.Conjunction):
    return (y.__class__ == x.__class__
        and len(x.values) == len(y.values)
        and all([same_structure(x.values[i], x.values[i]) for i in range(len(x.values))]))
  elif x.__class__ == formula.Identical:
    return y.__class__ == formula.Identical
  elif x.__class__ == formula.Holds:
    return y.__class__ == formula.Holds
  else:
    return False

class DefinitionSearchSpec(spec.SearchSpec):
  def __init__(self, x):
    self.x = x
  def valid(self, y):
    if y.__class__ == formula.Always:
      if y.value.__class__ == formula.Not:
        if y.value.value.__class__ == formula.Exists:
          if y.value.value.value.__class__ == formula.Not:
            body = y.value.value.value.value
            if body.__class__ == formula.Iff:
              left = body.left
              if same_structure(left, self.x):
                return True
    return False
  def definitons_only(self):
    return True
  def search_hidden_formula(self, name):
    return True

# Statefull.
class InOrderInstantiator(instantiator.Instantiator):
  def __init__(self, variables):
    self.variables = variables
    self.i = 0
    self.just_exported = False
    self.exports = 0

  def complete(self):
    return self.i == len(self.variables)

  # May throw FinishedInstantiatingException
  def instantiate(self, variable, endofunctor, formula):
    if self.complete():
      raise instantiator.FinishedInstantiatingException()
    else:
      result = self.variables[self.i]
      self.i += 1
      self.just_exported = False
      return result

  # May throw FinishedInstantiatingException
  def exportSide(self, formula, endofunctor):
    if self.just_exported:
      raise instantiator.FinishedInstantiatingException()
    else:
      self.just_exported = True
      self.exports += 1
      return left

