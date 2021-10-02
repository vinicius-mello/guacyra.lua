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
local A = Matrix(5,5, function(i,j) return RandomInteger({-4,4}) end)
local time = os.clock()
local d = Det(A:eval())
--local d = RandomInteger({1,4})
print(d,'=',d:eval())
print(string.format("elapsed time: %.2f\n", os.clock() - time))