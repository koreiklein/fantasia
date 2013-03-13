import types
import inspect

class Path():
  # first is some object
  # rest may be none, or a pair consisting of: (a symbol, another path object)
  #   a symbol may be either:
  #     a string: the name of a method taking no arguments and return a child object
  #     a tuple (name, i): where name is the string name of a method taking no
  #                        arguments and returning a list of children,
  #                        and where i is an index into that list.
  def __init__(self, first, rest = None):
    self._first = first
    self._rest = rest
    def g(name, method):
      if not isinstance(method, types.MethodType):
        return
      else:
        def f(self):
          res = method()
          if res.__class__ == list:
            return [self.follows((name, i), res[i]) for i in range(len(res))]
          else:
            return self.follows(name, res)
        assert(not self.__dict__.has_key(name))
        self.__dict__[name] = types.MethodType(f, self)
    for (name, method) in inspect.getmembers(first):
      g(name, method)

  def path_first(self):
    return self._first
  def path_singleton(self):
    return self._rest is None
  def path_last(self):
    if self.path_singleton():
      return self.path_first()
    else:
      return self.path_rest().path_last()
  def path_corest(self):
    if self.path_singleton():
      return None
    else:
      rec = self.path_rest().path_corest()
      if rec is None:
        return Path(first = self.first(), rest = None)
      else:
        return Path(first = self.first(), rest = (self.path_symbol(), rec))
  def path_rest(self):
    if self._rest == None:
      raise Exception("Singleton path has no rest.")
    else:
      return self._rest[1]
  def path_symbol(self):
    if self._rest == None:
      raise Exception("Singleton path has no symbol.")
    else:
      return self._rest[0]
  def follow(self, symbol, value):
    return Path(first = value, rest = (symbol, self))
  def follows(self, symbol, value):
    return Path(first = value, rest = (symbol, self))

