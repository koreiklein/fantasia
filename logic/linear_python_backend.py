# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from logic import linear

# A backend for the linear calculus.
# This backend runs on a single machine.
# This backend performs no optimizations.
# This backend translates each primitive transition individually.
# This is an interpreter backend.


# This backend represents data as python objects in the following ways:
# There is a functor rep.  rep is a realization of the Curry-Howard isomorphism.
# Specifically, rep consist of two functions: objectRep and arrowRep
# objectRep assigns to every linear logic object a set of python objects.
# objectRep is not implemented in any way, but it is defined in the following comments.
# objectRep(A | B) ---> {python tuples (a, b) where a in objectRep(A), b in objectRep(B)}

# objectRep(|) ---> The singleton set consisting of the number 1

#          ( A )
# objectRep( - )  ---> The union of sets X and Y
#          ( B )         where X = {(0,a) | a in objectRep(A)}, Y = {(1,b) | b in objectRep(B)}

# objectRep( |A )   --->   The set of python functions taking any a in objectRep(A) as an argument
#          ( *- )            and returning an element of the empty set.
#                          Note: While seemingly ridiculous, this definition is actually useful.

# objectRep(!A)  ---> objectRep(A)   (With GC, ! is purely for keeping track of things while coding.)

# objectRep(x . A) ---> objectRep(A) (Variables and quantifiers have to computational content.)

# A kind of implementation of the functor rep on arrows.
# Take each arrow A --> B to some python object in the set
# Note that the only way to conclude that we've returned an element of the empty set
# is to call a function assumed to return an element of the empty set.
#    ( | A | |B )
# rep( |   | *- )
#    ( *------- )
# As defined above.
def arrowToProgram(arrow):
  if arrow.__class__ == linear.IntroduceDoubleDual:
    return repIntroduceDoubleDual(arrow)
  elif arrow.__class__ == linear.RemoveDoubleDual:
    return repRemoveDoubleDual(arrow)
  elif arrow.__class__ == linear.Diagonal:
    return repDiagonal(arrow)
  elif arrow.__class__ == linear.IntroduceTrue:
    return repIntroduceTrue(arrow)
  elif arrow.__class__ == linear.RemoveFalse:
    return repRemoveFalse(arrow)
  elif arrow.__class__ == linear.Commute:
    return repCommute(arrow)
  elif arrow.__class__ == linear.AssociateA:
    return repAssociateA(arrow)
  elif arrow.__class__ == linear.AssociateB:
    return repAssociateB(arrow)
  elif arrow.__class__ == linear.Forget:
    return repForget(arrow)
  elif arrow.__class__ == linear.Admit:
    return repAdmit(arrow)
  elif arrow.__class__ == linear.Distribute:
    return repDistribute(arrow)
  elif arrow.__class__ == linear.Apply:
    return repApply(arrow)
  elif arrow.__class__ == linear.OnBody:
    return repOnBody(arrow)
  elif arrow.__class__ == linear.OnLeft:
    return repOnLeft(arrow)
  elif arrow.__class__ == linear.OnRight:
    return repOnRight(arrow)
  elif arrow.__class__ == linear.OnAlways:
    return repOnAlways(arrow)
  elif arrow.__class__ == linear.OnNot:
    return repOnNot(arrow)
  elif arrow.__class__ == linear.Identity:
    return repIdentity(arrow)
  elif arrow.__class__ == linear.Composite:
    return repComposite(arrow)
  elif arrow.__class__ in [linear.ConjQuantifier, linear.Eliminate, linear.UnusedExistential]:
    return repIdentity(arrow)
  else:
    raise Exception("Unrecognized Linear Arrow %s."%(arrow.__class__))


def repIntroduceDoubleDual(arrow):
  return (lambda (A, notnotnotA): notnotnotA(lambda notA: notA(A)))

def repRemoveDoubleDual(arrow):
  return (lambda (notnotA, notA): notnotA(notA))

def repDiagonal(arrow):
  return (lambda (alwaysA, notAlwaysAandA): notAlwaysAandA((alwaysA, alwaysA)))

def repIntroduceTrue(arrow):
  return (lambda (A, notAAndTrue): notAAndTrue((A,1)))

def repRemoveFalse(arrow):
  def f((AOrImpossible, notA)):
    assert(AOrImpossible[0] == 0) # Impossible cases should never be represented.
    return notA(AOrImpossible[1])
  return f

def repCommute(arrow):
  return (lambda (AAndB, notBAndA): notBAndA( (AAndB[1], AAndB[0]) ))

def repAssociateA(arrow):
  # (A % B) % C ---> A % (B % C)
  if arrow.type() == linear.andType:
    return (lambda (AB_C, notA_BC): notA_BC( (AB_C[0][0], (AB_C[0][1], AB_C[1])) ))
  else:
    assert(arrow.type() == linear.orType)
    def f((AB_C, notA_BC)):
      if AB_C[0] == 0:
        AB = AB_C[1]
        if AB[0] == 0:
          A = AB[1]
          return notA_BC( (0, A) )
        else:
          assert(AB[0] == 1)
          B = AB[1]
          return notA_BC( (1, (0, B)) )
      else:
        assert(AB_C[0] == 1)
        C = AB_C[1]
        return notA_BC( (1, (1, C)) )
    return f

def repAssociateB(arrow):
  # A % (B % C) ---> (A % B) % C
  if arrow.type() == linear.andType:
    return (lambda (A_BC, notAB_C): notAB_C( ((A_BC[0], A_BC[1][0]), A_BC[1][1]) ))
  else:
    assert(arrow.type() == linear.orType)
    def f((A_BC, notAB_C)):
      if A_BC[0] == 0:
        A = A_BC[1]
        return notAB_C( (0, (0, A)) )
      else:
        assert(A_BC[0] == 1)
        BC = A_BC[1]
        if BC[0] == 0:
          B = BC[1]
          return notAB_C( (0, (1, B)) )
        else:
          assert(BC[0] == 1)
          C = BC[1]
          return notAB_C( (1, C) )
    return f

def repForget(arrow):
  return (lambda (AAndB, notA): notA(AAndB[0]))

def repAdmit(arrow):
  return (lambda (A, notAOrB): notAOrB( (0, A) ))

def repDistribute(arrow):
  # B  |    --->   (B | C)
  # -- | C         -------
  # A  |           (A | C)
  return (lambda (AOrB_And_C, notAAndC_Or_BAndC):
    notAAndC_Or_BAndC( (AOrB_And_C[0][0], (AOrB_And_C[0][1], AOrB_And_C[1])) ))

def repApply(arrow):
  # | A | B  | B  --->  | A
  # *------  |          *--

  # How adroit, we use python closure convesion to implement closure conversion in the target language.
  # (The apply arrow is the essence of closure conversion.)
  return (lambda ((notAAndB, B), notnotA): notnotA(lambda A: notAAndB( (A, B) )))
def repOnBody(arrow):
  return arrowToProgram(arrow.arrow())

# Functorial Arrows
def repOnLeft(arrow):
  # A % B ---> A' % B
  notAAndNotAprime = arrowToProgram(arrow.arrow())
  if arrow.type() == linear.andType:
    return (lambda ((A, B), notAprimeAndB): notAAndNotAprime( (A, lambda Aprime:
      notAprimeAndB( (Aprime, B)))))
  else:
    assert(arrow.type() == linear.orType)
    def f((AOrB, notAprimeOrB)):
      if AOrB[0] == 0:
        A = AOrB[1]
        return notAAndNotAprime( (A, lambda Aprime: notAprimeOrB( (0, Aprime))))
      else:
        assert(AOrB[0] == 1)
        B = AOrB[1]
        return notAprimeOrB( (1, B) )
    return f

def repOnRight(arrow):
  # A % B ---> A % B'
  notBAndNotBprime = arrowToProgram(arrow.arrow())
  if arrow.type() == linear.andType:
    return (lambda ((A,B), notAAndBprime): notBAndNotBprime( (B, lambda Bprime:
      notAAndBprime( (A, Bprime) ))))
  else:
    assert(arrow.type() == linear.orType)
    def f((AOrB, notAOrBprime)):
      if AOrB[0] == 0:
        A = AOrB[1]
        return notAOrBprime( (0, A) )
      else:
        assert(AOrB[0] == 1)
        B = AOrB[1]
        return notBAndNotBprime( (B, lambda Bprime: notAOrBprime( (1, Bprime) )))
    return f

def repOnAlways(arrow):
  # Since the objectReps are the same, the arrowReps can be as well.
  return arrowToProgram(arrow.arrow())

def repOnNot(arrow):
  # Given:  A --> A'
  # Return: |A'  -->  |A
  #         *--       *-
  notAAndNotAprime = arrowToProgram(arrow.arrow())
  return (lambda (notAprime, notnotA): notnotA(lambda A: notAAndNotAprime( (A, lambda Aprime:
    notAprime(Aprime)))))

def repIdentity(arrow):
  return (lambda (A, notA): notA(A))

def repComposite(arrow):
  # Given:  A --> B
  # Given:  B --> C
  # Return: A --> C
  notAAndNotB = arrowToProgram(arrow.left())
  notBAndNotC = arrowToProgram(arrow.right())
  return (lambda (A, notC): notAAndNotB( (A, lambda B: notBAndNotC( (B, notC) )) ))

# A: A Linear Logic Arrow
# x: an element of objectRep(A.src())
# return: an element y of objectRep(A.tgt())
# You can also think of curry_howard as a conversion from
# {ARROWS in the category of linear logic}
# to
# {PROGRAM TRANSFORMATIONS in the category of elements of objectRep(X) for X a linear logic object}
# Where each program transformation is represented as a python function.
def curry_howard(A):
  def f(x):
    notXAndNotY = arrowToProgram(A)
    return applyProgram(notXAndNotY, x)
  return f

# a: an element of objectRep(  | X | |Y
#                              |   | *-
#                              *-------
# x: an element of objectRep(X)
# return: an element of Y obtained by "applying" a to x.
#         We're being clever.  Since clearly the only way a can return an element of the empty set
#         is by calling its second argument with an element of objectRep(Y) we can safely
#         pass in the constant function INSTEAD OF an element of objectRep( |Y )
#                                                                         ( *- )
#         and know that a will ultimately return an element of objectRep(Y)
def applyProgram(a, x):
  y = a( (x, lambda y: y) )
  return y
