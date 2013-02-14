# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from logic import linear, linear_python_backend, linear_example

cookieRep = "cookieRep"
milkRep = "milkRep"
napkinRep = "napkinRep"


def cookie_implies_milk_rep( (cookie, notMilk) ):
  assert(cookie == cookieRep)
  return notMilk(milkRep)

def milk_implies_napkin_rep( (milk, notNapkin) ):
  assert(milk == milkRep)
  return notNapkin(napkinRep)

def test():
  # starting_claim --------- modus_ponens --------> final_claim
  #         |                     |                      |
  #         |                     |                      |
  #         |                     |                      |
  #         |                     |                      |
  # starting_claim_rep ----- modus_ponens_rep ----> final_claim_rep
  starting_claim_rep = (cookie_implies_milk_rep, milk_implies_napkin_rep)

  # Use the curry-howard isomorphism to convert
  #  linear_example.modus_ponens (a proof)
  # into
  #  modus_ponens_rep (a program transformation)
  modus_ponens_rep = linear_python_backend.curry_howard(linear_example.modus_ponens)

  # Appling a program transformation to the representation of the starting claim
  # yields some representation of the final claim.
  final_claim_rep = modus_ponens_rep(starting_claim_rep)

  # We check that the representation of the final claim indeed performs the function
  # we expect it to.
  assert(napkinRep == linear_python_backend.applyProgram(final_claim_rep, cookieRep))
