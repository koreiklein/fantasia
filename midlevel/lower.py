# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import factor

# f, g: endofunctors
# x: a formula
# return: ('full', an enriched arrow g.onObject(f.onObject(x)) -> g.onObject(x))
#         OR
#         ('partial', (a, e, i)) if some of f can be absorbed
#             where a is an arrow: g.onObject(f.onObject(x)) -> g.onObject(e.onObject(x))
#                   and i is an integer measuring the "amount" of f that was absorbed.
#         OR
#         ('none', None) if nothing can be absorbed.
def absorb(x, f, g):
  raise Exception("Not yet implemented.")

# f: an endofunctor
# x: a formula
# return: an arrow : f.onObject(x) -> f.onObject(Or([]) if f.covariant() else And([]))
def export(x, f)
  raise Exception("Not yet implemented.")
