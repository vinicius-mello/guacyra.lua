local guacyra = require('guacyra')
guacyra.import()

print(LaTeX(Sqrt(3)*Sqrt(2)*Sqrt(8)):eval())
local Test, x, y = Symbols 'Test x y'
Rule(Test(_{a=NumericQ}),
function(a) return a + 1 end)
print(Test(1):eval())
print(Test(Rational(1,2)):eval())
print(Test(x))
math.randomseed(1)
local A = Matrix(4, 4,
  function(i, j) return RandomInteger({-4,4}) end):eval()
print(A)
print(Det(A):eval())
A[1][1] = Integer(1)
print(A)
print(Det(A):eval())
