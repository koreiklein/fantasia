# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

import calculus.enriched.formula
import calculus.enriched.endofunctor

# parent: An instance of calculus.enriched.endofunctor.Endofunctor
# child: An instance of calculus.enriched.formula.Formula
# side effect: Print to stdout a description of parent and child.
# return: An identity arrow on child.
def f(parent, child):
  print "The parent's variance is", "covariant." if parent.covariant() else "contravariant."
  print "Rendering parent.onObject(child) as text:"
  # See
  print parent.onObject(child).top_level_render()._backend

  print
  print '==========================================================='
  print

  print "The child is", child
  print "Rendering child as text:"
  print child.top_level_render(covariant = parent.covariant())._backend

  return child.identity()

def run(proof):
  proof.forwardFollow(lambda path:
      path.onPathFollow(lambda child: f(parent = path.endofunctor,
                                        child = child)))


