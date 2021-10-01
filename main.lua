local guacyra = require('guacyra')
guacyra.import()

print(LaTeX(Rational(28,15)^Rational(2,3)):eval())
print(LaTeX(Rational(28,15)^Rational(2,3)):eval())
local Test, x, y = Symbols 'Test x y'
Rule(Test(_{a=NumericQ}),
function(a) return a + 1 end)
print(Test(1):eval())
print(Test(Rational(1,2)):eval())
print(Test(x))
math.randomseed(1)
local A = Matrix({{1,2,x,1},{13,-2,1,0},{x,-1,2,2},{0,1,2,3}})
local time = os.clock()
local d = Expand(Det(A))
print(d:eval())
print(string.format("elapsed time: %.2f\n", os.clock() - time))
