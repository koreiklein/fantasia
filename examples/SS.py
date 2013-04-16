# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import constructors
from lib import natural, library, common_vars

# A proof that forall n : N . S (S n) > n

proof = natural.lib.beginProof()
proof = proof.forwardFollow(lambda x:
    x.forwardAndTrue().forwardFollow(lambda x:
      x.forwardAssume(constructors.true)))
