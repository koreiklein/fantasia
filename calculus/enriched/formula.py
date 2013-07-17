# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import misc
from misc import *

from calculus import variable
from calculus.variable import Variable
from calculus.basic import formula as basicFormula, endofunctor as basicEndofunctor, bifunctor as basicBifunctor
from lib.common_symbols import leftSymbol, rightSymbol, relationSymbol, domainSymbol
from ui.stack import stack
from ui.render.text import primitives, distances, colors

from sets import Set

class Formula:
  def translate(self):
    if self.__dict__.has_key('_cached_translate'):
      return self._cached_translate
    else:
      self._cached_translate = self._translate()
      return self._cached_translate

  def _translate(self):
    raise Exception("Abstract superclass.")

  def forwardGatherExistentials(self):
    arrow, bindings, value = self._forwardGatherExistentials()
    return Arrow(src = self, tgt = Exists(bindings, value),
        basicArrow = arrow)

  # return: a triplet (arrow, bindings, value) where
  #         arrow is a basic arrow with arrow.src == self.translate()
  #         arrow.tgt == Exists(bindings, value).translate()
  # attempt to keep bindings as long as possible.
  def _forwardGatherExistentials(self):
    return self.translate().identity(), [], self

  # spec: a SearchSpec instance.
  # return: a list of claims importable from self matching spec
  def search(self, spec):
    return []

  def forwardSimplify(self):
    return self.identity()
  def backwardSimplify(self):
    return self.identity()

  def __eq__(self, other):
    return isinstance(other, Formula) and self.translate() == other.translate()
  def __ne__(self, other):
    return not (self == other)

  def top_level_render(self):
    return self.render(RenderingContext(covariant = True))

  def render(self, context):
    return primitives.newTextStack(colors.genericColor, repr(self))

  def substituteVariable(self, a, b):
    raise Exception("Abstract superclass.")

  def applied_variables(self):
    raise Exception("Abstract superclass.")

  def updateVariables(self):
    raise Exception("Abstract superclass.")

  def is_and(self):
    return False

  def compress(self):
    return self

  def backwardUndoubleDual(self):
    src = Not(Not(self))
    return Arrow(tgt = self,
        src = src,
        basicArrow = src.translate().forwardUndoubleDual())

  def forwardAndTrue(self):
    values = [And([])]
    if self.is_and():
      values.extend(self.values)
    else:
      values.append(self)
    return Arrow(src = self,
        tgt = And(values),
        basicArrow = self.translate().forwardAndTrue())

  def identity(self):
    return Arrow(src = self, tgt = self, basicArrow = self.translate().identity())

class Arrow:
  def __init__(self, src, tgt, basicArrow):
    self.src = src
    self.tgt = tgt
    self.basicArrow = basicArrow
    if not(basicArrow.src == src.translate()):
      raise Exception("basicArrow.src =\n%s\nsrc.translate() =\n%s"%(basicArrow.src, src.translate()))
    if not(basicArrow.tgt == tgt.translate()):
      raise Exception("basicArrow.tgt =\n%s\ntgt.translate() =\n%s"%(basicArrow.tgt, tgt.translate()))

  def translate(self):
    return self.basicArrow

  def compress(self):
    return Arrow(src = self.src,
        tgt = self.tgt,
        basicArrow = self.basicArrow.compress())

  def invert(self):
    return Arrow(src = self.tgt, tgt = self.src, basicArrow = self.basicArrow.invert())

  def forwardCompose(self, arrow):
    return Arrow(src = self.src, tgt = arrow.tgt,
        basicArrow = self.basicArrow.forwardCompose(arrow.basicArrow))

  def backwardCompose(self, arrow):
    return Arrow(src = arrow.src, tgt = self.tgt,
        basicArrow = self.basicArrow.backwardCompose(arrow.basicArrow))

  def forwardFollow(self, f):
    return self.forwardCompose(f(self.tgt))

  def backwardFollow(self, f):
    return self.backwardCompose(f(self.src))

class Holds(Formula):
  def __init__(self, held, holding):
    self.held = held
    self.holding = holding

  def applied_variables(self):
    return self.held.applied_variables().union(self.holding.applied_variables())

  def __repr__(self):
    return "%s : %s"%(self.held, self.holding)

  def _translate(self):
    return basicFormula.Holds(held = self.held,
        holding = self.holding)

  def render(self, context):
    infix = getInfix(self)
    if infix is not None:
      holds = variable.renderInfix(productVariable = self.held,
          infixSymbols = infix, infixVariable = self.holding)
    else:
      holds = stack.stackAll(0, [ self.held.render()
                                , primitives.holds()
                                , self.holding.render()],
                                spacing = distances.holdsSpacing)
    if context.covariant:
      return holds
    else:
      return primitives.surroundWithNot(holds)

  def substituteVariable(self, a, b):
    return Holds(held = self.held.substituteVariable(a, b),
        holding = self.holding.substituteVariable(a, b))

  def updateVariables(self):
    return self

def _isUnit(x):
  return isinstance(x, Conjunction) and len(x.values) == 0

class Not(Formula):
  def __init__(self, value):
    self.value = value

  def applied_variables(self):
    return self.value.applied_variables()

  def forwardSimplify(self):
    arrow = self.value.backwardSimplify()
    value = arrow.src
    result = Arrow(src = self,
          tgt = Not(value),
          basicArrow = basicFormula.OnNot(arrow.basicArrow))
    if value.__class__ == Not:
      return result.forwardFollow(lambda x:
          Arrow(src = x, tgt = x.value.value,
            basicArrow = x.translate().forwardUndoubleDual()))
    elif _isUnit(value):
      if value.__class__ == And:
        return result.forwardFollow(lambda x:
            Arrow(src = x, tgt = Or([]),
              basicArrow = basicFormula.notTrueIsFalse))
      else:
        assert(value.__class__ == Or)
        return result.forwardFollow(lambda x:
            Arrow(src = x, tgt = And([]),
              basicArrow = x.forwardNotFalseIsTrue()))
    else:
      return result

  def backwardSimplify(self):
    arrow = self.value.forwardSimplify()
    value = arrow.tgt
    result = Arrow(tgt = self, src = Not(value),
        basicArrow = basicFormula.OnNot(arrow.basicArrow))
    if value.__class__ == Not:
      return result.backwardFollow(lambda x:
          Arrow(src = x.value.value, tgt = x,
            basicArrow = x.translate().backwardDoubleDual()))
    elif _isUnit(value):
      if value.__class__ == And:
        return result.backwardFollow(lambda x:
            Arrow(tgt = x, src = Or([]),
              basicArrow = x.backwardFalseIsNotTrue()))
      else:
        assert(value.__class__ == Or)
        return result.backwardFollow(lambda x:
            Arrow(tgt = x, src = And([]),
              basicArrow = basicFormula.trueIsNotFalse))
    else:
      return result

  def forwardUndoubleDual(self):
    assert(self.value.__class__ == Not)
    return Arrow(src = self, tgt = self.value.value,
        basicArrow = self.translate().forwardUndoubleDual())

  def backwardDoubleDual(self):
    assert(self.value.__class__ == Not)
    return Arrow(tgt = self, src = self.value.value,
        basicArrow = self.translate().backwardDoubleDual())

  def __repr__(self):
    return "~%s"%(self.value,)
  def _translate(self):
    return basicFormula.Not(self.value.translate())
  def render(self, context):
    return self.value.render(context.negate())
  def substituteVariable(self, a, b):
    return Not(self.value.substituteVariable(a, b))
  def updateVariables(self):
    return Not(self.value.updateVariables())

class Exists(Formula):
  def __init__(self, bindings, value):
    self.bindings = bindings
    self.value = value

  def _forwardGatherExistentials(self):
    arrow, bindings, value = self.value._forwardGatherExistentials()
    newBindings = list(self.bindings)
    newBindings.extend(bindings)
    return self._endofunctor_translate().onArrow(arrow), newBindings, value

  def applied_variables(self):
    return self.value.applied_variables()

  def updateVariables(self):
    pairs = [ (binding.variable, binding.updateVariables()) for binding in self.bindings ]
    value = self.value
    for variable, binding in pairs[::-1]:
      value = value.substituteVariable(variable, binding.variable)
    return Exists([binding for variable, binding in pairs], value.updateVariables())

  def substituteVariable(self, a, b):
    for binding in self.bindings:
      assert(binding.variable not in a.freeVariables())
      assert(binding.variable not in b.freeVariables())
    return Exists(self.bindings, self.value.substituteVariable(a, b))
  def substituteAllVariablesInBody(self, variables):
    assert(len(self.bindings) == len(variables))
    result = self.value
    for i in range(len(self.bindings)):
      result = result.substituteVariable(self.bindings[i].variable, variables[i])
    return result
  def forwardSimplify(self):
    arrow = self.value.forwardSimplify()
    return Arrow(src = self, tgt = Exists(bindings = self.bindings, value = arrow.tgt),
        basicArrow = self._endofunctor_translate().onArrow(arrow.basicArrow))
  def backwardSimplify(self):
    arrow = self.value.backwardSimplify()
    return Arrow(src = Exists(bindings = self.bindings, value = arrow.src), tgt = self,
        basicArrow = self._endofunctor_translate().onArrow(arrow.basicArrow))
  def __repr__(self):
    return "Exists(%s) . %s"%(self.bindings, self.value)
  def _endofunctor_translate(self):
    result = basicEndofunctor.identity_functor
    for binding in self.bindings[::-1]:
      result = result.compose(binding.translate())
    return result
  def _translate(self):
    return self._endofunctor_translate().onObject(self.value.translate())
  def forwardSplit(self, i):
    return Arrow(src = self, tgt = Exists(bindings = self.bindings[:i],
      value = Exists(bindings = self.bindings[i:], value = self.value)),
      basicArrow = self.translate().identity())

  def forwardPushAndSplit(self, i):
    assert(0 <= i)
    assert(i < len(self.bindings))
    a = self.identity()
    while i+1 < len(self.bindings):
      a = a.forwardFollow(lambda e:
          e.forwardPush(i))
      i += 1
    a = a.forwardFollow(lambda e:
        e.forwardSplit(len(self.bindings) - 1))
    return a

  # i: an index such that self.bindings[i] and self.bindings[i+1] both exist.
  # return: an enriched arrow commuting self.bindings[i] with self.bindings[i+1]
  def forwardPush(self, i):
    A = self.bindings[:i]
    b = self.bindings[i]
    c = self.bindings[i+1]
    D = self.bindings[i+2:]
    bindings = []
    bindings.extend(A)
    bindings.append(c)
    bindings.append(b)
    bindings.extend(D)
    x = self.value.translate()
    for binding in D[::-1]:
      x = binding.translate().onObject(x)
    a = c.commute(b)(x)
    for binding in A[::-1]:
      a = binding.translate().onArrow(a)
    return Arrow(src = self, tgt = Exists(bindings, self.value),
        basicArrow = a)

  def render(self, context):
    quantifierStackingDimension = _dimension_for_variance(context.covariant)
    variableStackingDimension = primitives._dual_dimension(quantifierStackingDimension)
    if len(self.bindings) == 0:
      variablesStack = primitives.nullStack
    else:
      variablesStack, context = self.bindings[0].render(context)
      for binding in self.bindings[1:]:
        rendered_binding, context = binding.render(context)
        variablesStack = variablesStack.stack(variableStackingDimension,
            rendered_binding,
            spacing = distances.quantifier_variables_spacing)
    kid = self.value.render(context)
    divider = primitives.quantifierDivider(context.covariant,
        max(kid.widths()[variableStackingDimension],
          variablesStack.widths()[variableStackingDimension]))
    return variablesStack.stack(quantifierStackingDimension, divider,
        spacing = distances.quantifier_before_divider_spacing).stack(
        quantifierStackingDimension, kid,
        spacing = distances.quantifier_after_divider_spacing)

class Always(Formula):
  def __init__(self, value):
    self.value = value
  def applied_variables(self):
    return self.value.applied_variables()
  def search(self, spec):
    result = []
    if spec.valid(self):
      result.append(self)
    result.extend(self.value.search(spec))
    return result
  def forwardJoin(self):
    assert(self.value.__class__ == Always)
    return Arrow(src = self, tgt = self.value,
        basicArrow = self.translate().forwardUnalways())
  def forwardSimplify(self):
    arrow = self.value.forwardSimplify()
    result = Arrow(src = self, tgt = Always(arrow.tgt),
        basicArrow = basicFormula.OnAlways(arrow.translate()))
    if arrow.tgt.__class__ == Always:
      return result.forwardFollow(lambda x:
          x.forwardJoin())
    elif arrow.tgt.__class__ in [And, Or] and len(arrow.tgt.values) == 0:
      return result.forwardFollow(lambda x:
          x.forwardUnalways())
    else:
      return result
  def backwardCojoin(self):
    assert(self.value.__class__ == Always)
    return Arrow(tgt = self, src = self.value,
        basicArrow = self.value.translate().forwardCojoin())
  def backwardSimplify(self):
    arrow = self.value.backwardSimplify()
    result = Arrow(src = Always(arrow.src), tgt = self,
        basicArrow = basicFormula.OnAlways(arrow.basicArrow))
    if arrow.src.__class__ == Always:
      return result.backwardFollow(lambda x:
          x.backwardCojoin())
    elif arrow.src.__class__ == And and len(arrow.src.values) == 0:
      return result.backwardFollow(lambda x:
          Arrow(tgt = x, src = x.value,
            basicArrow = basicFormula.trueAlways))
    else:
      return result
  def forwardUnalways(self):
    return Arrow(src = self, tgt = self.value,
        basicArrow = self.translate().forwardUnalways())
  def __repr__(self):
    return "!%s"%(self.value,)
  def _translate(self):
    return basicFormula.Always(self.value.translate())
  def render(self, context):
    return renderWithBackground(self.value.render(context),
        distances.exponential_border_width,
        colors.exponentialColor(context.covariant))
  def substituteVariable(self, a, b):
    return Always(self.value.substituteVariable(a, b))
  def updateVariables(self):
    return Always(self.value.updateVariables())

class WellDefined(Formula):
  def __init__(variable, newVariable, equivalence, value):
    self.variable = variable
    self.newVariable = newVariable
    self.equivalence = equivalence
    self.value = value
  def forwardSimplify(self):
    arrow = self.value.forwardSimplify()
    return Arrow(src = self, tgt = WellDefined(variable = self.variable,
      newVariable = self.newVariable, equivalence = self.equivalence, value = arrow.tgt),
      basicArrow = self.getBasicFunctor().onArrow(arrow.basicArrow))
  def backwardSimplify(self):
    arrow = self.value.backwardSimplify()
    return Arrow(src = WellDefined(variable = self.variable,
      newVariable = self.newVariable, equivalence = self.equivalence, value = arrow.src),
      tgt = self,
      basicArrow = self.getBasicFunctor().onArrow(arrow.basicArrow))
  def _translate(self):
    return self.getBasicFunctor().onObject(self.value.translate())
  def getBasicFunctor(self):
    return ExpandWellDefined(self.variable, self.newVariable,
      self.equivalence)
  def render(self, context):
    # TODO render a well defined formula more clearly?
    return self.value.render(context)
  def substituteVariable(self, a, b):
    return WellDefined(variable = self.variable.substituteVariable(a, b),
        newVariable = self.newVariable.substituteVariable(a, b),
        equivalence = self.equivalence.substituteVariable(a, b),
        value = self.value.substituteVariable(a, b))
  def updateVariables(self):
    return WellDefined(variable = self.variable,
        newVariable = self.newVariable,
        equivalence = self.equivalence,
        value = self.value.updateVariables())

def ExpandWellDefined(variable, newVariable, equivalence):
  isEqual = basicFormula.And(
        InDomain(newVariable, equivalence).translate(),
        Equal(newVariable, variable, equivalence).translate())
  F = basicEndofunctor.SubstituteVariable(variable, newVariable).compose(
      basicEndofunctor.not_functor.compose(
        basicEndofunctor.And(side = right, other = isEqual)).compose(
          basicEndofunctor.Exists(newVariable)).compose(
            basicEndofunctor.not_functor))
  return basicBifunctor.and_functor.precomposeRight(F).join()

class Conjunction(Formula):
  def __init__(self, values):
    for i in range(len(values)):
      value = values[i]
      if not(isinstance(value, Formula)):
        raise Exception("%s at index %s is not an enriched formula."%(value, i))
    self.values = values
    self.basicBinop = self.basicBinop()
  def __repr__(self):
    return "%s%s"%(self.name(), self.values)
  def _translate(self):
    return basicFormula.multiple_conjunction(conjunction = self.basicBinop,
        values = [value.translate() for value in self.values])
  def applied_variables(self):
    result = Set([])
    for value in self.values:
      result.union_update(value.applied_variables())
    return result
  def forwardSimplify(self):
    if len(self.values) == 0:
      return self.identity()
    else:
      arrows = [v.forwardSimplify() for v in self.values]
      result = Arrow(src = self, tgt = self.__class__(values = [a.tgt for a in arrows]),
          basicArrow = self.forwardOnArrows(arrows))
      return result.forwardFollow(lambda x:
          x.forwardSimplifyConjunction())

  # all of self.values must already by simplified
  # return an arrow that performs further top level simplifications.
  def forwardSimplifyConjunction(self):
    for i in range(len(self.values)):
      value = self.values[i]
      if isinstance(value, Conjunction) and len(value.values) == 0 and value.__class__ != self.__class__:
        return self.forwardTotalCollapse(i)
    return self.forwardRemoveUnits().forwardFollow(lambda x:
        x.forwardMaybeUnsingleton())

  def forwardMaybeUnsingleton(self):
    if len(self.values) == 1:
      return Arrow(src = self, tgt = self.values[0],
          basicArrow = self.translate().identity())
    else:
      return self.identity()

  def backwardMaybeUnsingleton(self):
    if len(self.values) == 1:
      return Arrow(tgt = self, src = self.values[0],
          basicArrow = self.translate().identity())
    else:
      return self.identity()

  def backwardSimplify(self):
    if len(self.values) == 0:
      return self.identity()
    else:
      arrows = [v.backwardSimplify() for v in self.values]
      result = Arrow(tgt = self, src = self.__class__(values = [a.src for a in arrows]),
          basicArrow = self.forwardOnArrows(arrows))
      return result.backwardFollow(lambda x:
          x.backwardSimplifyConjunction())

  def backwardSimplifyConjunction(self):
    for i in range(len(self.values)):
      value = self.values[i]
      if isinstance(value, Conjunction) and len(value.values) == 0 and value.__class__ != self.__class__:
        return self.backwardTotalCollapse(i)
    return self.backwardIntroduceUnits().backwardFollow(lambda x:
            x.backwardMaybeUnsingleton())

  def myUnit(self, x):
    return x.__class__ == self.__class__ and len(x.values) == 0

  def forwardRemoveUnits(self):
    if len(self.values) == 0:
      return self.identity()
    elif len(self.values) == 1:
      if self.myUnit(self.values[0]):
        return Arrow(src = self, tgt = self.values[0],
            basicArrow = self.translate().identity())
      elif self.values[0].__class__ == self.__class__:
        return self.forwardMaybeUnsingleton()
      else:
        return self.identity()
    else:
      arrow = self.__class__(self.values[1:]).forwardRemoveUnits()
      tgt_values = arrow.tgt.values
      for value in tgt_values:
        if not(value.__class__ != self.__class__):
          raise Exception("values contains another copy like %s self %s"%(self.__class__, tgt_values,))
      if self.values[0].__class__ == self.__class__:
        if len(self.values[0].values) == 0:
          if self.__class__ == And:
            forgettingArrow = self.translate().simplifyOnce()
          else:
            assert(self.__class__ == Or)
            forgettingArrow = self.translate().simplifyOnce()
          return Arrow(src = self, tgt = arrow.tgt,
              basicArrow = forgettingArrow.forwardCompose(arrow.translate()))
        else:
          def f(i):
            if i == len(self.values[0].values) - 1:
              return (lambda x: x.identity())
            else:
              return (lambda x:
                  x.forwardAssociate().forwardFollow(lambda x:
                    x.forwardOnRightFollow(f(i+1))))
          values = list(self.values[0].values)
          values.extend(tgt_values)
          return Arrow(src = self, tgt = self.__class__(values),
              basicArrow = self.translate().forwardOnRight(arrow.translate()).forwardFollow(f(0)))
      else:
        values = [self.values[0]]
        values.extend(tgt_values)
        return Arrow(src = self, tgt = self.__class__(values),
            basicArrow = self.translate().forwardOnRight(arrow.translate()).forwardFollow(lambda x:
              x.forwardRemoveRightIfUnit()))

  def backwardIntroduceUnits(self):
    return self.forwardRemoveUnits().invert()

  def forwardMoveBack(self, i, amount):
    values = list(self.values)
    a = values.pop(i)
    values.insert(i - amount, a)
    return self.__class__(values).forwardMoveForward(i - amount, amount).invert()

  def forwardMoveForward(self, i, amount):
    values = list(self.values)
    a = values.pop(i)
    values.insert(i + amount, a)
    def f(j, x):
      if j == i:
        def g(k, x):
          if k == amount:
            return x.identity()
          else:
            if i + amount == len(self.values) - 1 and k+1 == amount:
              return x.forwardCommute()
            else:
              return x.forwardAssociateOther().forwardFollow(lambda x:
                  x.forwardOnLeftFollow(lambda x:
                    x.forwardCommute()).forwardFollow(lambda x:
                      x.forwardAssociate().forwardFollow(lambda x:
                        x.forwardOnRightFollow(lambda x:
                          g(k+1, x)))))

        return g(0, x)
      else:
        return x.forwardOnRightFollow(lambda x: f(j+1, x))
    return Arrow(src = self, tgt = self.__class__(values),
        basicArrow = f(0, self.translate()))

  def forwardOnArrows(self, arrows):
    assert(len(arrows) > 0)
    def f(i):
      if i == len(arrows) - 1:
        return arrows[i].basicArrow
      else:
        leftArrow = arrows[i].basicArrow
        rightArrow = f(i + 1)
        return basicFormula.OnConjunction(leftArrow = leftArrow, rightArrow = rightArrow,
            src = self.basicBinop(leftArrow.src, rightArrow.src),
            tgt = self.basicBinop(leftArrow.tgt, rightArrow.tgt))
    return f(0)

  def substituteVariable(self, a, b):
    return self.__class__(values = [v.substituteVariable(a, b) for v in self.values])

  def updateVariables(self):
    return self.__class__(values = [v.updateVariables() for v in self.values])

  def render(self, context):
    dimension = 0
    if not context.covariant:
      dimension += 1
    if self.__class__ == Or:
      dimension += 1
    dimension = dimension % 2
    other_dimension = primitives._dual_dimension(dimension)

    length = distances.min_unit_divider_length
    values = []
    for kid in self.values:
      s = kid.render(context)
      length = max(length, s.widths()[other_dimension])
      values.append(s)
    return stack.stackAll(dimension,
        misc._interleave(self.renderDivider(context.covariant, length), values),
        spacing = distances.divider_spacing)

class And(Conjunction):
  def is_and(self):
    return True

  def search(self, spec):
    result = []
    for value in self.values:
      result.extend(value.search(spec))
    return result

  # return: a triplet (arrow, bindings, value) where
  #         arrow is a basic arrow with arrow.src == self.translate()
  #         arrow.tgt == Exists(bindings, value).translate()
  # attempt to keep bindings as long as possible.
  def _forwardGatherExistentials(self):
    def f(i):
      # return And(self.values[i:])._forwardGatherExistentials()
      if i == len(self.values):
        return And([]).translate().identity(), [], And([])
      elif i == len(self.values) - 1:
        arrow, bindings, value = self.values[i]._forwardGatherExistentials()
        return arrow, bindings, And([value])
      else:
        rest_arrow, rest_bindings, rest_value = f(i+1)
        first_arrow, first_bindings, first_value = self.values[i]._forwardGatherExistentials()
        bindings = list(first_bindings)
        bindings.extend(rest_bindings)
        all_values = [first_value]
        all_values.extend(rest_value.values)
        arrow = basicFormula.OnAnd(first_arrow, rest_arrow).forwardCompose(
            And([Exists(first_bindings, first_value), Exists(rest_bindings, rest_value)]).liftBasicExistsBothSides())
        return arrow, bindings, And(all_values)
    return f(0)

  # self == And([Exists(xs, X), Exists(ys, Y)])
  # return: an arrow self.translate() --> Exists(xs..ys, X|Y).translate()
  def liftBasicExistsBothSides(self):
    assert(len(self.values) == 2)
    left_exists = self.values[0]
    X = left_exists.value.translate()
    right_exists = self.values[1]
    Y = right_exists.value.translate()
    left_functor = left_exists._endofunctor_translate()
    # And([Exists(xs, X), Exists(ys, Y)]) --> Exists(xs, And([X, Exists(ys, Y)]))
    return left_functor._importOther(right_exists.translate())(X).forwardCompose(
        # Exists(xs, And([X, Exists(ys, Y)])) --> Exists(xs, Exists(ys, And([X, Y])))
        left_functor.onArrow(right_exists._endofunctor_translate()._import(X)(Y)))

  # distribute i over j
  def forwardDistribute(self, i, j):
    assert(i != j)
    assert(self.values[j].__class__ == Or)
    if i < j:
      return self.forwardMoveForward(i, j - (i+1)).forwardFollow(lambda x:
          x.forwardDistributeToNext(j - 1))
    else:
      assert(i > j)
      return self.forwardMoveBack(i, i - j).forwardFollow(lambda x:
          x.forwardDistributeToNext(j))

  # distribute i over i+1
  def forwardDistributeToNext(self, i):
    assert(self.values[i+1].__class__ == Or)
    n_or_values = len(self.values[i+1].values)
    assert(n_or_values > 0)
    def f(k, x):
      if k == i:
        def g(k, x):
          if k == n_or_values - 1:
            return x.identity()
          else:
            return x.forwardDistibute().forwardFollow(lambda x:
                x.forwardOnRightFollow(lambda x: g(k+1, x)))
        return x.forwardAssociateOther().forwardFollow(lambda x:
            x.forwardOnLeftFollow(lambda x: g(0, x)))
      else:
        return x.forwardOnRightFollow(lambda x: f(k+1, x))
    values = list(self.values)
    a = values.pop(i)
    values[i] = Or([And([a, b]) for b in values[i].values])
    return Arrow(src = self, tgt = And(values), basicArrow = f(0, self.translate()))

  def name(self):
    return 'And'

  def basicBinop(self):
    return basicFormula.And
  def basicUnit(self):
    return basicFormula.true

  def renderDivider(self, covariant, length):
    return primitives.andDivider(covariant)(length)

  def forwardTotalCollapse(self, index):
    assert(self.values[index].translate() == basicFormula.false)
    def f(i, x):
      if i == index:
        if i == len(self.values) - 1:
          return x.identity()
        else:
          return x.forwardForgetRight()
      else:
        return x.forwardForgetLeft().forwardFollow(lambda x:
            f(i+1, x))
    return Arrow(src = self, tgt = Or([]),
        basicArrow = f(0, self.translate()))

  def forwardCommutePair(self):
    assert(len(self.values) == 2)
    return Arrow(src = self, tgt = And([self.values[1], self.values[0]]),
        basicArrow = self.translate().forwardCommute())

  def forwardDistributePair(self):
    assert(len(self.values) == 2)
    assert(self.values[1].__class__ == Or)
    assert(len(self.values[1].values) == 2)
    return Arrow(src = self, tgt = Or([And([self.values[0], value]) for value in self.values[1].values]),
        basicArrow = self.translate().forwardDistibute())

  def forwardDistributePairOther(self):
    return self.forwardCommutePair().forwardFollow(lambda x:
        x.forwardDistributePair())

  def backwardTotalCollapse(self, index):
    assert(self.values[index].translate() == basicFormula.false)
    return Arrow(tgt = self, src = Or([]),
        basicArrow = basicFormula.falseIsNotTrue.forwardFollow(lambda x:
          x.forwardOnNotFollow(lambda x:
            Not(self).translate().forwardCollapse())).forwardFollow(lambda x:
              x.forwardUndoubleDual()))

class Or(Conjunction):
  def basicBinop(self):
    return basicFormula.Or
  def name(self):
    return 'Or'
  def renderDivider(self, covariant, length):
    return primitives.orDivider(covariant)(length)

  def backwardAdmitRight(self):
    assert(len(self.values) == 2)
    return Arrow(tgt = self, src = self.values[0],
        basicArrow = self.translate().backwardAdmitRight())

  def backwardAdmitLeft(self):
    assert(len(self.values) == 2)
    return Arrow(tgt = self, src = self.values[1],
        basicArrow = self.translate().backwardAdmitLeft())

  def basicUnit(self):
    return basicFormula.false

  def forwardTotalCollapse(self, index):
    assert(self.values[index].translate() == basicFormula.true)
    return Arrow(src = self, tgt = And([]),
        basicArrow = self.translate().forwardCollapse())

  def backwardTotalCollapse(self, index):
    assert(self.values[index].translate() == basicFormula.true)
    def f(i, x):
      if i == index:
        return x.backwardAdmitRight()
      else:
        return x.backwardAdmitLeft().backwardFollow(lambda x:
            f(i+1, x))
    return Arrow(tgt = self, src = And([]),
        basicArrow = f(0, self.translate()))


true = And([])
false = Or([])

class Iff(Formula):
  def __init__(self, left, right):
    self.left = left
    self.right = right
  def applied_variables(self):
    return self.left.applied_variables().union(self.right.applied_variables())
  def __repr__(self):
    return "Iff(\n%s\n<==>\n%s\n)"%(self.left, self.right)
  def _translate(self):
    return basicFormula.ExpandIff(self.left.translate(), self.right.translate())
  def updateVariables(self):
    return Iff(left = self.left.updateVariables(),
        right = self.right.updateVariables())
  def substituteVariable(self, a, b):
    return Iff(left = self.left.substituteVariable(a, b),
        right = self.right.substituteVariable(a, b))

  def forwardLeftToRight(self):
    return Arrow(src = self,
        tgt = Always(Not(And([self.left, Not(self.right)]))),
        basicArrow = self.translate().forwardForgetRight())

  def forwardRightToLeft(self):
    return Arrow(src = self,
        tgt = Always(Not(And([self.right, Not(self.left)]))),
        basicArrow = self.translate().forwardForgetLeft())

  def render(self, context):
    kid_context = context.as_covariant()
    res = self.left.render(kid_context).stack(0,
        primitives.iff(),
        spacing = distances.iffSpacing).stack(0,
            self.right.render(kid_context),
            spacing = distances.iffSpacing)
    if context.covariant:
      return res
    else:
      return primitives.surroundWithNot(res)

class Hidden(Formula):
  def __init__(self, base, name):
    self.base = base
    self.name = name

  def applied_variables(self):
    return self.base.applied_variables()

  def search(self, spec):
    if spec.search_hidden_formula(self.name):
      return self.base.search(spec)
    else:
      return []

  def __repr__(self):
    return "<<" + self.name + ">>"
  def _translate(self):
    return self.base.translate()
  def updateVariables(self):
    return Hidden(base = self.base.updateVariables(), name = self.name)
  def substituteVariable(self, a, b):
    return Hidden(base = self.base.substituteVariable(a, b), name = self.name)

class Identical(Formula):
  def __init__(self, left, right):
    self.left = left
    self.right = right
  def forwardSimplify(self):
    if self.left == self.right:
      return 
  def applied_variables(self):
    return self.left.applied_variables().union(self.right.applied_variables())
  def __repr__(self):
    return "%s = %s"%(self.left, self.right)
  def _translate(self):
    return basicFormula.Identical(self.left, self.right)
  def updateVariables(self):
    return self
  def substituteVariable(self, a, b):
    return Identical(left = self.left.substituteVariable(a, b),
        right = self.right.substituteVariable(a, b))
  def render(self, context):
    return self.left.render().stack(0, primitives.identical(context.covariant)).stack(0,
        self.right.render())
  def forwardSimplify(self):
    if self.left == self.right:
      return Arrow(src = self, tgt = And([]),
          basicArrow = basicFormula.IdenticalReflexive(src = self.translate(),
            tgt = basicFormula.true))
    else:
      return self.identity()
  def backwardSimplify(self):
    if self.left == self.right:
      return Arrow(tgt = self, src = And([]),
          basicArrow = basicFormula.IdenticalReflexive(src = self.translate(),
            tgt = basicFormula.true).invert())
    else:
      return self.identity()

def InDomain(x, e):
  return Always(Holds(x, variable.ApplySymbolVariable(e, domainSymbol)))

def Equal(a, b, e):
  return Always(Holds(
      variable.ProductVariable([(leftSymbol, a), (rightSymbol, b)]),
      variable.ApplySymbolVariable(e, relationSymbol)))

class Unique(Formula):
  def __init__(self, variable, equivalence, formula, newVariable = None):
    self.variable = variable
    self.equivalence = equivalence
    self.formula = formula
    if newVariable is None:
      self.newVariable = Variable()
    else:
      self.newVariable = newVariable

  def _translate(self):
    formulaTranslate = self.formula.translate()
    all_others_are_equal = basicFormula.Not(
        basicFormula.Exists(self.newVariable,
          basicFormula.And(basicFormula.And(
            InDomain(self.newVariable, self.equivalence),
            formulaTranslate.substituteVariable(self.variable, self.newVariable)),
            basicFormula.Not(Equal(self.newVariable, self.variable, self.equivalence)))))
    return basicFormula.And(formulaTranslate, all_others_are_equal)

  def substituteVariable(self, a, b):
    assert(b != self.newVariable)
    assert(a != self.newVariable)
    return Unique(variable = self.variable.substituteVariable(a, b),
        equivalence = self.equivalence.substituteVariable(a, b),
        formula = self.formula.substituteVariable(a, b),
        newVariable = self.newVariable)

  def updateVariables(self):
    return Unique(variable = self.variable,
        equivalence = self.equivalence,
        formula = self.formula.updateVariables(),
        newVariable = self.newVariable.updateVariables())

  def render(self, context):
    return gl.newTextualGLStack(colors.variableColor,
        "%s ! in %s . "%(self.variable, self.equivalence)).stack(0,
            self.formula.render(context))


class RenderingContext:
  def __init__(self, covariant):
    self.covariant = covariant

  def negate(self):
    return RenderingContext(covariant = not self.covariant)

  def as_covariant(self):
    return self if self.covariant else self.negate()

# holds: a basic.Holds
# return: the pair of infix symbols, or None of no such symbols exist.
def getInfix(holds):
  if holds.held.__class__ != variable.ProductVariable:
    return None
  v = holds.holding
  if v.__class__ == variable.StringVariable and v.infix is not None:
    return v.infix
  elif v.__class__ == variable.ApplySymbolVariable and v.symbol.infix is not None:
    return v.symbol.infix
  else:
    return None

def renderWithBackground(s, border_width, color):
  return s
  widths = [x + 2 * border_width for x in s.widths()]
  return primitives.solidSquare(color, widths).stackCentered(2, s,
      spacing = distances.epsilon )

def _dimension_for_variance(covariant):
  if covariant:
    return 0
  else:
    return 1

