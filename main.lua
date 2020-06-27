local guacyra = require('guacyra')
--[[local algebra = require('algebra')
local list = require('list')
local latex = require('latex')
guacyra.importSymbols(guacyra)
guacyra.importSymbols(algebra)
guacyra.importSymbols(latex)
guacyra.importSymbols(list)
local SymbEnv = require('symbenv').SymbEnv
--guacyra.debug.eval = false
function test()
  SymbEnv(true)
--[[  In[1] = Set(a,Range(10))
  In[2] = Map(function(x) return x^2 end, a)
  In[3] = NestList(function(x) return Together(1+1/x) end ,x,7)
  In[4] = Map(LaTeX,Out[3])
  In[5] = Set(x,4)
  In[6] = Set(y,Power(Rational(9,2),Rational(-1,3)))
  In[7] = LaTeX(y)
  In[8] = SetDelayed(f(x_,y_),x^2+y)
  In[9] = f(y,3)
  In[1] = Set(y,(u+v)^2)
  In[2] = LaTeX(y)
end
test()
]]
guacyra.debug.io = true
guacyra.debug.eval = true
guacyra.wrap(function() 
  In[1] = LaTeX(Rational(28,15)^Rational(2,3))
end)