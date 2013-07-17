# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

def run(proof):
  for s in proof.tgt.top().top_level_render()._backend.strings:
    print s[:160]

