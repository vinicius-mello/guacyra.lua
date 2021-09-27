local guacyra = require('guacyra')
guacyra.import()

print(LaTeX(Rational(28,15)^Rational(2,3)):eval())
local Test, x, y = Symbols 'Test x y'
Rule(Test(_{a=NumericQ}),
function(a) return a + 1 end)
print(Test(1):eval())
print(Test(Rational(1,2)):eval())
print(Test(x):eval())