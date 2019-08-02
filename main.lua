local guacyra = require('guacyra')
local algebra = require('algebra')
local list = require('list')
local latex = require('latex')
guacyra.importSymbols(guacyra)
guacyra.importSymbols(algebra)
guacyra.importSymbols(latex)
guacyra.importSymbols(list)
require('ioev')
guacyra.debug.match = false
guacyra.debug.eval = false

i[1] = Set(a,Range(10))
i[2] = Map(function(x) return x^2 end, a)
i[3] = NestList(function(x) return Together(1+1/x) end ,x,7)
i[4] = Map(LaTeX,o[3])
i[5] = SetDelayed(f(x_,y_),x^2+y)
i[6] = f(2,3)
