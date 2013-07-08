# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import constructors
from lib import natural, library, common_vars, equivalence, function

# A proof that forall n : N . S (S n) > n
n = common_vars.n()

a = common_vars.a()
b = common_vars.b()

claim = natural.Less(natural.zero,
    constructors.Apply( constructors.Apply(natural.zero, natural.natural_successor)
                      , natural.natural_successor))

proof = natural.lib.beginProof().forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      constructors.assume(x, claim)))

proof = proof.forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      x.forwardSimplify()))
