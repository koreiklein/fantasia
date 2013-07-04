# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus.enriched import constructors
from lib import natural, library, common_vars, equivalence, function

# A proof that forall n : N . S (S n) > n
n = common_vars.n()

a = common_vars.a()
b = common_vars.b()

proof = natural.lib.beginProof().forwardFollow(lambda p:
    p.onPathFollow(lambda x:
      constructors.assume(x, constructors.Always(constructors.Holds(a, b)))))
