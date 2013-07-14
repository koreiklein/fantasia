# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

from calculus import variable
from calculus.variable import StringVariable
from lib.common_symbols import functionPairsSymbol

p = lambda: StringVariable('p')
n = lambda: StringVariable('n')
m = lambda: StringVariable('m')
h = lambda: StringVariable('h')
k = lambda: StringVariable('k')
t = lambda: StringVariable('t')
q = lambda: StringVariable('q')
r = lambda: StringVariable('r')
s = lambda: StringVariable('s')
l = lambda: StringVariable('l')

a = lambda: StringVariable('a')
b = lambda: StringVariable('b')
c = lambda: StringVariable('c')
d = lambda: StringVariable('d')
e = lambda: StringVariable('e')

aprime = lambda: StringVariable('a\'')
bprime = lambda: StringVariable('b\'')
cprime = lambda: StringVariable('c\'')
dprime = lambda: StringVariable('d\'')
eprime = lambda: StringVariable('e\'')

A = lambda: StringVariable('A')
B = lambda: StringVariable('B')
C = lambda: StringVariable('C')

x = lambda: StringVariable('x')
y = lambda: StringVariable('y')
z = lambda: StringVariable('z')

R = lambda: StringVariable('R')

less = lambda: StringVariable('<')

equivalence = StringVariable('equivalence')

function = StringVariable('function')

tmp = lambda: StringVariable('tmp')

natural = variable.StringVariable('N')

S = variable.StringVariable('S')
S_pairs = variable.ApplySymbolVariable(S, functionPairsSymbol)

zero = variable.StringVariable('0')
