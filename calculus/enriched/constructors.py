# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import formula, endofunctor

def Holds(held, holding):
  return formula.Holds(held = held, holding = holding)

def And(values):
  return formula.And(values)
def Or(values):
  return formula.Or(values)

def Not(value):
  return formula.Application(endofunctor = endofunctor.not_functor, formula = value)

def OrdinaryVariableBinding(variable):
  return endofunctor.OrdinaryVariableBinding(variable)
def BoundedVariableBinding(variable, relation):
  return endofunctor.BoundedVariableBinding(variable, relation)
def WelldefinedVariableBinding(variable, relation):
  return endofunctor.WelldefinedVariableBinding(variable, relation)
def ImageVariableBinding(variable, preimage, function):
  return endofunctor.ImageVariableBinding(variable, preimage, function)

def Exists(bindings, value):
  return formula.Application(endofunctor = endofunctor.Exists(bindings), formula = value)

def Forall(bindings, value):
  return Not(Exists(bindings, Not(value)))

def Always(value):
  return formula.Application(endofunctor = endofunctor.always_functor, formula = value)

def Maybe(value):
  return Not(Always(Not(value)))

def Implies(predicates, consequent):
  values = list(predicates)
  values.append(Not(consequent))
  return Not(And(values))

def Iff(left, right):
  return formula.Iff(left, right)

def Hidden(value, name):
  return formula.Hidden(value, name)

