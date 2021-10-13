local guacyra = require('guacyra')
guacyra.import()

--local profiler = require("profiler")
--profiler.start()


math.randomseed(1)
local test = {}
test[#test+1] = function()
  print('Sum 1000')
  local s = Plus()
  for i=1, 1000 do 
    s[#s+1] = Int(i)
  end
  local sum = s:eval()
  print('sum=', sum)
  assert(sum==Int(500500))
end

test[#test+1] = function()
  print('Sum 1/n*(n+1)')
  local s = Plus()
  for i=1, 999 do
    s[#s+1] = Rat(1,i*(i+1))
  end
  local sum = s:eval()
  print('sum=', sum)
  assert(sum==Rat(999,1000))
end

test[#test+1] = function()
  print('Expand (x-1)(1+...+x^n)')
  local x = Symbols('x')
  local s = Plus()
  for i=0, 9 do
    s[#s+1] = Power(x, i) 
  end
  local sum = Expand((x-1)*s):eval()
  print('sum=', sum)
  local r = (x^10-1):eval()
  assert(sum==r)
end

test[#test+1] = function()
  local exp = (Sqrt(2)+Sqrt(3)+Sqrt(4))^2
  local r = Expand(exp):eval()
  print(exp, '=', r)
  assert(r==(9+4*Sqrt(2)+4*Sqrt(3)+2*Sqrt(6)):eval())
end

test[#test+1] = function()
  local A = Matrix(4, 4, 
    function(i, j) return 1/(i+j-1) end):eval()
  local r = Det(A):eval()
  print(Det(A), '=', r)
  assert(r==Rat(1,6048000))
end

test[#test+1] = function()
  local a, b, c = Symbols('a b c')
  local A = Matrix({1,2,12,a},{-2,3,11,b},{-1,4,18,c})
  local r = RREF(A):eval()
  r = Numerator(r[3][4]):eval()
  print('Numerator(RREF(A)[3][4])=', r)
  assert(r==Plus(Times(-5,a),Times(-6,b),Times(7,c)))
end

test[#test+1] = function()
  local A = Matrix({1,2,12},{-2,3,11},{-1,4,18})
  local r = RREF(A):eval()
  print('RREF(A)=', r)
  print('Rank(A)=', Rank(A):eval())
end

test[#test+1] = function()
  local x,y = Symbols('x y')
  local exp = -1+2*x+x^2-3*x*y+y^2+y
  local r = LaTeX(exp):eval()
  print(LaTeX(exp:eval()), '=', r)
  assert(r== Str('x^2-3xy+y^2+2x+y-1'))
end

test[#test+1] = function()
  local a, b, c = Symbols('a b c')
  local exp = Union(Set(a,b,c),Set(a,b,1,2))
  local r = exp:eval()
  print(exp, '=', r)
  exp = Intersection(Set(a,b,c),Set(a,b,1,2))
  r = exp:eval()
  print(exp, '=', r)
  exp = In(a, Set(a,b,c))
  print(exp, exp:eval())
  exp = In(c, Set(a,b))
  print(exp, exp:eval())
  assert(r== Set(a, b))
end

test[#test+1] = function()
  local exp = Union(Set('a','b','c'),Set('a','b',1,2))
  local r = exp:eval()
  print(exp, '=', r)
end

for i=1,#test do
  print('Test ',i)
  local time = os.clock()
  test[i]()
  print('\t time elapsed: ',os.clock()-time)
end


--profiler.stop()
--profiler.report("profiler.log")
