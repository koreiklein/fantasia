# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import basic
from lib import common_vars

class Endofunctor:
  # Return a basic endofunctor
  def translate(self):
    return self
  def variables(self):
    raise Exception("Abstract superclass.")
  # self must be covariant()
  # f takes each object x to a list f(x)
  # return a list of all triples [(B, nt, y)] such that
  #   nt is a natural transform self -> (B|.) o self
  #   y is in f(B)
  def importFiltered(self, f):
    return []
  # self must not be covariant()
  # f takes each object x to a list f(x)
  # return a list of all triples [(B, nt, y)] such that
  #   nt is a natural transform (B|.) o self -> self
  #   y is in f(B)
  def exportFiltered(self, f):
    return []
  # self must be covariant()
  # return a function representing a natural transform: F o (B|.) --> (B|.) o F
  def _import(self, B):
    raise Exception("Abstract superclass.")
  # self must not be covariant()
  # return a function representing some natural transform: (B|.) o F o (B|.) --> F
  def _export(self, B):
    raise Exception("Abstract superclass.")

  # return a (its tgt, function represention some natural transform:
  #   (Exists variable .) o F -> G o (Exists variable .) o H such that
  #   G o H = F and H is as small as reasonably possible.)
  def liftExists(self, variable):
    (extent, x) = self._liftExists(variable)
    if extent == 'partial':
      return x
    else:
      assert(extent == 'full')
      nt = x
      return (self.compose(Exists(variable)), nt)

  # return either:
  #   ('full', nt) for a full lift
  #   ('partial', (tgt, nt)) for a partial lift
  def _liftExists(self, variable):
    return ('partial', ( Exists(variable).compose(self)
                       , lambda x: self.onObject(basic.Exists(variable, x)).identity()))

  def onObject(self, object):
    raise Exception("Abstract superclass.")
  def onArrow(self, arrow):
    raise Exception("Abstract superclass.")
  def negations(self):
    raise Exception("Abstract superclass.")
  def covariant(self):
    return 0 == (self.negations() % 2)
  # Return a pair of functors (F, G) such that self == F.compose(G), F is non-trivial,
  # and F is "as simple as possible".
  def pop(self):
    return (self, identity_functor)
  def compose(self, other):
    if self.__class__ == Id:
      return other
    elif other.__class__ == Id:
      return self
    else:
      return Composite(left = self, right = other)

def new_path(object):
  return Path(identity_functor, object)

class Path:
  def __init__(self, functor, object):
    self.functor = functor
    self.object = object

  def simplify(self):
    arrow = self.top().simplify()
    return Arrow(src = self, tgt = new_path(arrow.tgt), arrow = arrow)

  def __repr__(self):
    if self.covariant():
      variance = "Covariant"
    else:
      variance = "Contravariant"
    return "%s PATH:\nBEGIN_WITH: %s\nAPPLY_FUNCTOR:\n%s"%(variance, self.object, self.functor)

  def __eq__(self, other):
    return self.bottom() == other.bottom() and self.top() == other.top()

  # self must be covariant.
  # self.bottom() must be an exists.
  # return: a path arrow that lifts the exists as far as possible.
  def liftExists(self):
    assert(self.covariant())
    assert(self.object.__class__ == basic.Exists)
    (tgt, nt) = self.functor.liftExists(self.object.variable)
    return Arrow(src = self, tgt = Path(object = self.object.value, functor = tgt),
        arrow = nt(self.object.value))

  def variables(self):
    return self.functor.variables()
  def top(self):
    return self.functor.onObject(self.object)
  def bottom(self):
    return self.object

  def covariant(self):
    return self.functor.covariant()

  def translate(self):
    return Path(functor = self.functor.translate(), object = self.object.translate())

  def toPathArrowList(self):
    return self.identity().toPathArrowList()

  # return a path arrow that uses the indexth import available from self.importFiltered(f)
  def doImportFiltered(self, f, index):
    l = self.importFiltered(f)
    if index < len(l):
      (B, nt) = l[index]
      bAnd = And(side = right, other = B)
      a = nt(self.object)
      return Arrow(src = self,
          tgt = Path(functor = self.functor, object = basic.And(B, self.object)),
          arrow = a)
    else:
      raise Exception("Failed to import because the index %s does not exist in %s"%(index, l))

  # self must be covariant
  # return a list of (B, a function representing some natural transform: F --> (B|.) o F)
  # such that f(B) == True.
  def importFiltered(self, f):
    return self.functor.importFiltered(f)

  # self must be covariant
  # return a list of (B, a path arrow to self.onObject((B|self.object)))
  # such that f(B) == True
  def importFilteredArrow(self, f):
    def g(x):
      if f(x):
        return ['dummy']
      else:
        return []
    return [(B, Arrow(src = self,
      tgt = Path(functor = self.functor, object = basic.And(B, self.object)),
      arrow = nt(self.object)))
      for B, nt, X in self.importFiltered(g)]

  # self must be contravariant
  # return: a list of path arrows : self --> self.functor.onObject(basic.true)
  def exportBottom(self):
    assert(not self.functor.covariant())
    # x F --> (x|1) F = 1 ((x|.) o F) --> 1F
    result =  [Arrow(src = self, tgt = Path(functor = self.functor, object = basic.true),
                  arrow = self.functor.onArrow(
                    self.object.backwardForgetRight(basic.true)).forwardCompose(nt(basic.true)))
               for B, nt, X in self.functor.exportFiltered(lambda x:
                 [e for e in ['dummy'] if x == self.object])]
    return result

  # self must be contravariant.
  # return a path arrow "which exports as much as possible from nested Ands at the bottom".
  def exportConjunctively(self):
    assert(not self.functor.covariant())
    trial = self.exportBottom()
    if len(trial) > 0:
      return trial[0]
    elif self.bottom().__class__ == basic.And:
      def maybeBackwardIntroduceUnit(x):
        if x.__class__ == basic.And and x.left == basic.true:
          return x.right.forwardAndTrue()
        elif x.__class__ == basic.And and x.right == basic.true:
          return x.left.forwardAndTrue().forwardFollow(lambda x:
              x.forwardCommute())
        else:
          return x.identity()
      return self.advanceLeft().forwardFollow(lambda x:
          x.exportConjunctively().forwardFollow(lambda x:
            x.retreat().forwardFollow(lambda x:
              x.advanceRight().forwardFollow(lambda x:
                x.exportConjunctively().forwardFollow(lambda x:
                  x.retreat().forwardFollow(lambda x:
                    x.forwardOnPathFollow(lambda x:
                      maybeBackwardIntroduceUnit(x))))))))
    else:
      return self.identity()

  def _forwardIdentityArrow(self, tgt):
    return Arrow(src = self, tgt = tgt, arrow = self.top().identity())

  def identity(self):
    return self._forwardIdentityArrow(tgt = self)

  def retreat(self):
    assert(self.functor.__class__ == Composite)
    (a, b) = self.functor.pop()
    return self._forwardIdentityArrow(Path(functor = b, object = a.onObject(self.object)))

  def advanceTwice(self):
    return self.advance().forwardFollow(lambda p: p.advance())
  def advance(self):
    if self.object.__class__ == basic.Always:
      p = Path(functor = always_functor.compose(self.functor),
          object = self.object.value)
    elif self.object.__class__ == basic.Not:
      p = Path(functor = not_functor.compose(self.functor),
          object = self.object.value)
    elif self.object.__class__ == basic.Exists:
      p = Path(functor = Exists(variable = self.object.variable).compose(self.functor),
          object = self.object.value)
    elif self.object.__class__ == basic.Exists:
      p = Path(functor = Exists(variable = self.object.variable,
        domains = self.object.domains).compose(self.functor),
        object = self.object.value)
    else:
      raise Exception("Can't advance path: %s\npast object: %s:"%(self,self.bottom()))
    return self._forwardIdentityArrow(p)
  def advanceLeft(self):
    return self.advanceToSide(left)
  def advanceRight(self):
    return self.advanceToSide(right)
  def advanceToSide(self, side):
    object = _getSide(side, self.object)
    other = _getSide(_swapSide(side), self.object)
    if self.object.__class__ == basic.And:
      p = Path(functor = And(side = side, other = other).compose(self.functor),
          object = object)
    else:
      assert(self.object.__class__ == basic.Or)
      p = Path(functor = Or(side = side, other = other).compose(self.functor),
          object = object)
    return self._forwardIdentityArrow(p)

  def forwardOnPath(self, arrow):
    assert(isinstance(arrow, basic.Arrow))
    if self.covariant():
      assert(self.object == arrow.src)
      x = arrow.tgt
    else:
      assert(self.object == arrow.tgt)
      x = arrow.src
    return Arrow(src = self,
        tgt = Path(functor = self.functor, object = x),
        arrow = self.functor.onArrow(arrow))
  def forwardOnPathFollow(self, f):
    return self.forwardOnPath(f(self.bottom()))

  # return: A path arrow from self to a path p like self in which p.object == basic.true
  def newUnit(self):
    if self.object == basic.true:
      a = self.identity()
    else:
      if self.covariant():
        return self.forwardOnPathFollow(lambda x:
            x.forwardAndTrue()).forwardFollow(lambda p:
                p.advanceLeft())
      else:
        return self.forwardOnPathFollow(lambda x:
            x.backwardForgetLeft(basic.true)).forwardFollow(lambda p:
                p.advanceLeft())

  # return a simple list of the universal things that can be claimed about variables.
  def importables_universalIn(self, variables):
    return [a.tgt.bottom() for a in self.universalIn(variables)]

  # return: a PathArrowList of all ways to import claims about variables.
  def universalIn(self, variables):
    assert(self.covariant())
    return self.newUnit().toPathArrowList().forwardFollowWithImports(lambda B, P:
      PathArrowList() if B.__class__ != basic.Always or B.value.__class__ != basic.Not else
          (P.advanceLeft().forwardFollow(lambda P:
            P.advanceTwice()).toPathArrowList().forwardFollow(lambda P:
            P.maybeInstantiate(variables)).forwardOnTgts(lambda P:
              P.retreat().forwardFollow(lambda P:
                P.forwardOnPathFollow(lambda x:
                  x.forwardUndoubleDual())))))

  def maybeInstantiate(self, variables):
    if basic.isExistentialOfLength(len(variables), self.object):
      return self.instantiate(variables)
    else:
      return PathArrowList()

  # self must be contravariant.
  # self.object must be a bounded existential of the same length as variables
  # return a list of pairs (B, A) such that B is like self.object.value with substituted variables
  #   and A is a path arrow to self.onObject(B)
  def instantiate(self, variables):
    assert(not self.functor.covariant())
    if len(variables) > 4:
      raise Exception("WARNING: Running instantiate on more than 4 variables may be inefficient.")
    return self.toPathArrowList().forwardFollowWithValues(_perms(variables), lambda perm, path:
        path.instantiate_ordered(perm))

  # like instantiate, but only return instantiations that substitute the variables in order.
  def instantiate_ordered(self, variables):
    path = self
    assert(not path.covariant())
    path_arrow = path.identity()
    for v in variables:
      assert(path_arrow.src == self)
      if path.object.__class__ == basic.Exists:
        path_arrow = path_arrow.forwardFollow(lambda p, v=v:
            p.forwardOnPathFollow(lambda x, v=v:
              x.backwardIntroExists(v)))
        path = path_arrow.tgt
      else:
        return PathArrowList()
    exportArrow = path.exportConjunctively()
    if exportArrow.tgt.bottom().__class__ == basic.Not:
      return path_arrow.forwardCompose(exportArrow).toPathArrowList()
    else:
      return PathArrowList()

def _perms(xs):
  if len(xs) == 0:
    return [[]]
  else:
    return [_functional_insert(ys, i, xs[0])
        for ys in _perms(xs[1:])
        for i in range(len(xs))]

def _functional_insert(l, index, x):
  result = list(l)
  result.insert(index, x)
  return result

def _functional_pop(i, l):
  r = list(l)
  x = r.pop(i)
  return (x, r)

def _functional_pops(l):
  return [_functional_pop(i, l) for i in range(len(l))]

class Arrow:
  # src, tgt: paths
  # arrow: an arrow : src.top() --> tgt.top()
  def __init__(self, src, tgt, arrow):
    assert(src.top() == arrow.src)
    if not(tgt.top() == arrow.tgt):
      raise Exception("Incorrect path arrow\ntgt.top() = %s\narrow.tgt = %s"%(tgt.top(), arrow.tgt))
    assert(tgt.top() == arrow.tgt)
    self.src = src
    self.tgt = tgt
    self.arrow = arrow

  def translate(self):
    return Arrow(src = self.src.translate(),
        tgt = self.tgt.tranlate(),
        arrow = self.arrow.translate())

  def forwardCompose(self, other):
    if self.tgt.top() != other.src.top():
      raise Exception("Incomposable path arrows tgt = \n%s\nsrc = \n%s"%(self.tgt, other.src))
    assert(self.tgt.top() == other.src.top())
    return Arrow(src = self.src, tgt = other.tgt, arrow = self.arrow.forwardCompose(other.arrow))
  def backwardCompose(self, other):
    return other.forwardCompose(self)
  def forwardFollow(self, f):
    return self.forwardCompose(f(self.tgt))
  def backwardFollow(self, f):
    return self.backwardCompose(f(self.src))

  def toPathArrowList(self):
    return PathArrowList([self])

class PathArrowList:
  # arrows: a list of path arrows
  def __init__(self, arrows = []):
    self.arrows = arrows

  def __len__(self):
    return len(self.arrows)
  def __getitem__(self, i):
    return self.arrows[i]
  def __iter__(self):
    return iter(self.arrows)

  # f: takes a tag and a path p and returns a PathArrowList of arrows that start at p.
  # return: <See the below python code.>
  def forwardFollow(self, f):
    return PathArrowList([a.forwardCompose(A)
      for a in self
      for A in f(a.tgt)])

  # f: takes paths to paths.
  def forwardOnTgts(self, f):
    return PathArrowList([A.forwardFollow(f) for A in self])

  # f: takes a pair (value, oldArrow.tgt) to a PathArrowList of arrows composable with oldArrow.tgt
  # return: a list of all arrows formable from applying f to an arrow of self and a value in values.
  def forwardFollowWithValues(self, values, f):
    return PathArrowList([X
      for value in values
      for X in self.forwardFollow(lambda path, value=value: f(value, path))])

  # like forwardFollowWithValues, but as if values were equal to a list of all importable claims.
  # TODO: Consider passing extra arguments that allow for caching or better filtering so as
  #       to improve performance.
  def forwardFollowWithImports(self, f):
    return PathArrowList([A.forwardCompose(B).forwardCompose(C)
      for A in self
      for (b, nt, C) in A.tgt.functor.importFiltered(lambda x, A=A:
        f(x, Path(functor = A.tgt.functor, object = basic.And(x, A.tgt.object))).arrows)
      for B in [Arrow(src = A.tgt, tgt = C.src, arrow = nt(A.tgt.object))] ])

left = 'left'
right = 'right'

def _swapSide(side):
  if side == left:
    return right
  else:
    assert(side == right)
    return left

def _getSide(side, object):
  if side == left:
    return object.left
  else:
    assert(side == right)
    return object.right

class Exists(Endofunctor):
  def __init__(self, variable):
    self.variable = variable
  def __repr__(self):
    return "Exists(%s)"%(self.variable,)
  def _import(self, B):
    assert(self.variable not in B.freeVariables())
    return (lambda x:
        basic.And(left = B, right = self.onObject(x)).forwardAndPastExists())
  def variables(self):
    return [self.variable]
  def onObject(self, object):
    return basic.Exists(variable = self.variable, value = object)
  def onArrow(self, arrow):
    return basic.OnBody(variable = self.variable, arrow = arrow)
  def negations(self):
    return 0

class Always(Endofunctor):
  def __repr__(self):
    return "!"
  def _import(self, B):
    # B|!X --> !(B|X) (not always possible!)
    # but when   B == !C
    # !C | !X --> !!C | !X --> ! (!C | X)
    if B.__class__ != basic.Always:
      raise Exception("Unable to import B past Always when B is not also an Always.  B == %s"%(B,))
    else:
      C = B.value
      return (lambda x:
          basic.And(left = B, right = self.onObject(x)).forwardOnLeftFollow(lambda x:
            x.forwardCojoin()).forwardFollow(lambda x:
              x.forwardZip()))

  # return either:
  #   ('full', nt) for a full lift
  #   ('partial', (tgt, nt)) for a partial lift
  def _liftExists(self, variable):
    return ('full', lambda x: self.onObject(basic.Exists(variable, x)).forwardAlwaysPastExists())

  def variables(self):
    return []
  def onObject(self, object):
    return basic.Always(object)
  def onArrow(self, arrow):
    return basic.OnAlways(arrow)
  def negations(self):
    return 0

always_functor = Always()

class Not(Endofunctor):
  def __repr__(self):
    return "~"
  # self must not be covariant()
  # return a function representing some natural transform: (B|.) o F o (B|.) --> F
  def _export(self, b):
    bAnd = lambda x: basic.And(left = b, right = x)
    return (lambda x:
        # B|(~(B|x)) --> ~x
        bAnd(self.onObject(bAnd(x))).forwardApply())
  def variables(self):
    return []
  def onObject(self, object):
    return basic.Not(object)
  def onArrow(self, arrow):
    return basic.OnNot(arrow)
  def negations(self):
    return 1

not_functor = Not()

class Id(Endofunctor):
  def __repr__(self):
    return "ID"
  def _import(self, B):
    # Id o (B|.) --> (B|.) o Id
    # (B|x) --> (B|x)
    return (lambda x:
        basic.And(left = B, right = x).identity())
  def variables(self):
    return []
  def pop(self):
    raise Exception("Can't pop the identity functor.")
  def onObject(self, object):
    return object
  def onArrow(self, arrow):
    return arrow
  def negations(self):
    return 0

identity_functor = Id()

class Composite(Endofunctor):
  # if right is covariant, self will represent (left o right)
  # otherwise secod is contravariant, and self will represent (oppositeFunctor(left) o right)
  def __init__(self, left, right):
    self.left = left
    self.right = right

  def __repr__(self):
    return "%s\no\n%s"%(self.left, self.right)

  # return either:
  #   ('full', nt) for a full lift
  #   ('partial', (tgt, nt)) for a partial lift
  def _liftExists(self, variable):
    (extent0, x0) = self.left._liftExists(variable)
    if extent0 == 'partial':
      (tgt, nt) = x0
      return ('partial', ( tgt.compose(self.right)
                       , lambda x: self.right.onArrow(nt(x))))
    else:
      assert(extent0 == 'full')
      nt0 = x0
      (extent1, x1) = self.right._liftExists(variable)
      if extent1 == 'partial':
        (tgt, nt1) = x1
        # (Exists x.) o F o G -> F o (Exists x.) o G -> F o (H o (Exists x.) o K)
        return ('partial', ( self.left.compose(tgt)
                         , lambda x: self.right.onArrow(nt0(x)).forwardCompose(
                             nt1(self.left.onObject(x)))))
      else:
        assert(extent1 == 'full')
        # (Exists x.) o F o G -> F o (Exists x.) o G -> F o G o (Exists x.)
        return ('full', lambda x: self.right.onArrow(nt0(x)).forwardCompose(
                          nt1(self.left.onObject(x))))

  def _import(self, B):
    if self.right.covariant():
      assert(self.left.covariant())
      # F o G o (B|.) --> F o (B|.) o G --> (B|.) o F o G
      return (lambda x:
          self.right._import(B)(self.left.onObject(x)).forwardCompose(
            self.right.onArrow(self.left._import(B)(x))))
    else:
      assert(not self.right.covariant())
      assert(not self.left.covariant())
      # F o G o (B|.) --> (B|.) o F o (B|.) o G o (B|.) --> (B|.) o F o G
      bAnd = And(side = right, other = B)
      G_o_BAnd = self.right.compose(bAnd)
      return (lambda x:
          G_o_BAnd.onArrow(self.left._export(B)(x)).forwardCompose(
            self.right._export(B)(self.left.onObject(bAnd.onObject(x)))))

  def _export(self, B):
    bAnd = And(side = right, other = B)
    if self.right.covariant():
      assert(not self.left.covariant())
      # (B|.) o F o G o (B|.) --> (B|.) o F o (B|.) o G --> F o G
      return (lambda x:
          self.right._import(B)(self.left.onObject(bAnd.onObject(x))).forwardCompose(
            self.right.onArrow(self.left._export(B)(x))))
    else:
      assert(not self.right.covariant())
      assert(self.left.covariant())
      # (B|.) o F o G o (B|.) --> F o (B|.) o G o (B|.) --> F o G
      return (lambda x:
          bAnd.onArrow(self.right.onArrow(self.left._import(B)(x))).forwardCompose(
            self.right._export(B)(self.left.onObject(x))))

  def importFilteredCovariantCovariant(self, f):
    assert(self.left.covariant())
    assert(self.right.covariant())
    result = []
    # F o G --> ((B|.) o F) o G
    result.extend([(B, lambda x, nt=nt: self.right.onArrow(nt(x)), X)
                   for B, nt, X in self.left.importFiltered(f)])
    # F o G --> F o ((B|.) o G) --> (B|.) o F o G
    result.extend([(B, lambda x, B=B, nt=nt: nt(self.left.onObject(x)).forwardCompose(
                                 self.right.onArrow(self.left._import(B)(x))), X)
                    for B, nt, X in self.right.importFiltered(f)])
    return result

  def importFilteredContravariantContravariant(self, f):
    assert(not self.right.covariant())
    assert(not self.left.covariant())
    result = []
    # F o G --> ((B|.) o F) o G
    result.extend([(B, lambda x, nt=nt: self.right.onArrow(nt(x)), X)
                   for B, nt, X in self.left.exportFiltered(f)])
    # F o G --> ((B|.) o F o (B|.)) o G = ((B|.) o F) o ((B|.) o G) --> ((B|.) o F) o G
    result.extend([(B, lambda x, B=B, nt=nt: self.right.onArrow(self.left._export(B)(x)).forwardCompose(
                                nt(self.left.onObject(basic.And(B, x)))), X)
                   for B, nt, X in self.right.exportFiltered(f)])
    return result

  # self must be covariant()
  # f takes each object x to a list f(x)
  # return a list of all triples [(B, nt, y)] such that
  #   nt is a natural transform self -> (B|.) o self
  #   y is in f(B)
  def importFiltered(self, f):
    assert(self.covariant())
    if self.right.covariant():
      return self.importFilteredCovariantCovariant(f)
    else:
      return self.importFilteredContravariantContravariant(f)

  def exportFilteredContravariantCovariant(self, f):
    assert(self.right.covariant())
    assert(not self.left.covariant())
    result = []
    # (B|.) o F o G --> F o G
    result.extend([(B, lambda x, nt=nt: self.right.onArrow(nt(x)), X)
                   for B, nt, X in self.left.exportFiltered(f)])
    # (B|.) o F o G --> (B|.) o F o (B|.) o G --> F o G
    result.extend([(B, lambda x, B=B, nt=nt: nt(self.left.onObject(basic.And(B, x))).forwardCompose(
                                 self.right.onArrow(self.left._export(B)(x))), X)
                   for B, nt, X in self.right.importFiltered(f)])
    return result

  def exportFilteredCovariantContravariant(self, f):
    assert(self.left.covariant())
    assert(not self.right.covariant())
    result = []
    # (B|.) o F o G --> F o G
    result.extend([(B, lambda x, nt=nt: self.right.onArrow(nt(x)), X)
                   for B, nt, X in self.left.importFiltered(f)])
    # (B|.) o F o G --> F o (B|.) o G --> F o G
    result.extend([(B, lambda x, B=B, nt=nt: self.right.onArrow(self.left._import(B)(x)).forwardCompose(
                                 nt(self.left.onObject(x))), X)
                   for B, nt, X in self.right.exportFiltered(f)])
    return result

  # self must not be covariant()
  # f takes each object x to a list f(x)
  # return a list of all triples [(B, nt, y)] such that
  #   nt is a natural transform (B|.) o self -> self
  #   y is in f(B)
  def exportFiltered(self, f):
    if self.right.covariant():
      return self.exportFilteredContravariantCovariant(f)
    else:
      return self.exportFilteredCovariantContravariant(f)


  def variables(self):
    result = list(self.left.variables())
    result.extend(self.right.variables())
    return result
  def pop(self):
    (a, b) = self.left.pop()
    return (a, b.compose(self.right))
  def onObject(self, object):
    return self.right.onObject(self.left.onObject(object))
  def onArrow(self, arrow):
    return self.right.onArrow(self.left.onArrow(arrow))
  def negations(self):
    return self.left.negations() + self.right.negations()

class Conjunction(Endofunctor):
  def __init__(self, side, other):
    self.side = side
    self.other = other

  def __repr__(self):
    if self.side == left:
      return "(.%s%s)"%(self.stringDivider(), self.other,)
    else:
      assert(self.side == right)
      return '(%s%s.)'%(self.other, self.stringDivider())

  def variables(self):
    return []
  def createObject(self, left, right):
    raise Exception("Abstract superclass.")
  def createArrow(self, leftArrow, rightArrow):
    return basic.OnConjunction(leftArrow = leftArrow, rightArrow = rightArrow,
        src = self.createObject(left = leftArrow.src, right = rightArrow.src),
        tgt = self.createObject(left = leftArrow.tgt, right = rightArrow.tgt))

  def onObject(self, object):
    if self.side == left:
      return self.createObject(left = object, right = self.other)
    else:
      assert(self.side == right)
      return self.createObject(left = self.other, right = object)

  def onArrow(self, arrow):
    if self.side == left:
      return self.createArrow(leftArrow = arrow, rightArrow = self.other.identity())
    else:
      assert(self.side == right)
      return self.createArrow(leftArrow = self.other.identity(), rightArrow = arrow)

  def negations(self):
    return 0

class And(Conjunction):
  def createObject(self, left, right):
    return basic.And(left = left, right = right)

  def stringDivider(self):
    return "|"

  # return a function represention some natural transform:
  #   (Exists variable .) o F -> G o (Exists variable .) o H such that
  #   G o H = F and H is as small as reasonably possible.
  def _liftExists(self, variable):
    if self.side == left:
      # (Exists variable .) o (.|B) -> (.|B) o (Exists variable .)
      return ('full', lambda x: self.onObject(basic.Exists(variable, x)).forwardAndPastExistsOther())
    else:
      assert(self.side == right)
      # (Exists variable .) o (B|.) -> (B|.) o (Exists variable .)
      return ('full', lambda x: self.onObject(basic.Exists(variable, x)).forwardAndPastExists())

  def _import(self, B):
    bAnd = And(side = right, other = B)
    if self.side == left:
      # B|(X|OTHER) --> (B|X) | OTHER
      return (lambda x: bAnd.onObject(self.onObject(x)).forwardAssociateOther())
    else:
      assert(self.side == right)
      # B|(OTHER|X) --> (OTHER|X)|B --> (OTHER|(X|B)) --> (OTHER|(B|X))
      return (lambda x:
          bAnd.onObject(self.onObject(x)).forwardCommute().forwardFollow(lambda x:
            x.forwardAssociate().forwardFollow(lambda x:
              x.forwardOnRightFollow(lambda x:
                x.forwardCommute()))))

  # self must be covariant()
  # f takes each object x to a list f(x)
  # return a list of triples all [(B, nt, y) such that
  #   nt is a natural transform self -> (B|.) o self
  #   y is in f(B)
  def importFiltered(self, f):
    if self.side == left:
      # (X|A) --> (X|(B|A)) --> ((X|B)|A) --> ((B|X)|A)
      return [(a.tgt.left, lambda x, a=a:
        self.onObject(x).forwardOnRight(a).forwardFollow(lambda x:
          x.forwardAssociateOther().forwardFollow(lambda x:
            x.forwardOnLeftFollow(lambda x:
              x.forwardCommute()))), X) for a, X in self.other.produceFiltered(f)]
    else:
      # (A|X) --> ((B|A)|X) --> ((A|B)|X) --> (A|(B|X))
      assert(self.side == right)
      return [(a.tgt.left, lambda x, a=a:
        self.onObject(x).forwardOnLeft(a.forwardFollow(lambda x:
          x.forwardCommute())).forwardFollow(lambda x:
            x.forwardAssociate()), X) for a, X in self.other.produceFiltered(f)]

class Or(Conjunction):
  def stringDivider(self):
    return "-"
  def _import(self, B):
    bAnd = And(side = right, other = B)
    if self.side == left:
      # B|(X-OTHER) --> (B|X)-OTHER
      return (lambda x:
          bAnd.onObject(self.onObject(x)).forwardDistributeLeft())
    else:
      assert(self.side == right)
      # B|(OTHER-X) --> (OTHER-(B|X))
      return (lambda x:
          bAnd.onObject(self.onObject(x)).forwardDistributeRight())

  def createObject(self, left, right):
    return basic.Or(left = left, right = right)
