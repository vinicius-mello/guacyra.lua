local guacyra = require('guacyra')
guacyra.import()

--local profiler = require("profiler")
--profiler.start()


math.randomseed(1)
local test = {}
test[1] = function()
  print('Sum 1000')
  local s = Plus()
  for i=1, 1000 do 
    s[#s+1] = Int(i)
  end
  local sum = s:val()
  print('sum=', sum)
  assert(sum:eq(500500))
end

test[2] = function()
  print('Sum 1/n*(n+1)')
  local s = Plus()
  for i=1, 999 do
    s[#s+1] = Rat(1,i*(i+1))
  end
  local sum = s:val()
  print('sum=', sum)
  assert(sum:eq(Rat(999,1000)))
end

test[3] = function()
  print('Expand (x-1)(1+...+x^n)')
  local x = Symbols('x')
  local s = Plus()
  for i=0, 9 do
    s[#s+1] = Power(x, i) 
  end
  local sum = Expand((x-1)*s):val()
  print('sum=', sum)
  local r = (x^10-1):val()
  assert(sum:eq(r))
end

test[4] = function()
  local exp = (Sqrt(2)+Sqrt(3)+Sqrt(4))^2
  local r = Expand(exp):val()
  print(exp, '=', r)
  assert(r:eq((9+4*Sqrt(2)+4*Sqrt(3)+2*Sqrt(6)):val()))
end

test[5] = function()
  local A = Matrix(4, 4, 
    function(i, j) return 1/(i+j-1) end):val()
  local r = Det(A):val()
  print(Det(A), '=', r)
  assert(r:eq(Rat(1,6048000)))
end

test[6] = function()
  local a, b, c = Symbols('a b c')
  local A = Matrix({1,2,12,a},{-2,3,11,b},{-1,4,18,c})
  local r = RREF(A):val()
  r = Numerator(r[3][4]):val()
  print('Numerator(RREF(A)[3][4])=', r)
  assert(r:eq(Plus(Times(-5,a),Times(-6,b),Times(7,c))))
end

test[7] = function()
  local A = Matrix({1,2,12},{-2,3,11},{-1,4,18})
  local r = RREF(A):val()
  print('RREF(A)=', r)
  print('Rank(A)=', Rank(A):val())
end

test[8] = function()
  local x,y = Symbols('x y')
  local exp = -1+2*x+x^2-3*x*y+y^2+y
  local r = LaTeX(exp):val()
  print(LaTeX(exp:val()), '=', r)
  assert(r:eq(Str('x^2-3xy+y^2+2x+y-1')))
end

test[9] = function()
  local a, b, c = Symbols('a b c')
  local exp = Union(Set(a,b,c),Set(a,b,1,2))
  local r = exp:val()
  print(exp, '=', r)
  exp = Intersection(Set(a,b,c),Set(a,b,1,2))
  r = exp:val()
  print(exp, '=', r)
  exp = In(a, Set(a,b,c))
  print(exp, exp:val())
  exp = In(c, Set(a,b))
  print(exp, exp:val())
  assert(r:eq(Set(a, b)))
end

test[10] = function()
  local a, b, c = Symbols('a b c')
  local A = Matrix({1,2,3,4},{2,3,4,5},{3,4,5,6})
  exp = SubMatrix(A, {1,2}, {3,4})
  local r = exp:val()
  print(exp, '=', r)
  exp = Tuple(r)
  r = exp:tex()
  print(exp, '=', r)
  assert(r=='(3,4,4,5)')
end

for i=1,#test do
  print('Test ',i)
  local time = os.clock()
  test[i]()
  print('\t time elapsed: ',os.clock()-time)
end


--profiler.stop()
--profiler.report("profiler.log")
