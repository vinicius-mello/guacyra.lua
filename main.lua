local guacyra = require('guacyra').import()

--local profiler = require("profiler")
--profiler.start()

math.randomseed(1)
local test = {}


test[1] = function()
  local f, g, h = Symbols('f g h')
  local l = Range(1, 3)
  print('Map(f, Range(1, 3)) =', Map(f, l))
  assert(Map(f, l):eq({f(1), f(2), f(3)}))
  print('Map(t->g(t), Range(1, 3)) =', Map(function(t) return g(t) end, l))
  assert(Map(function(t) return g(t) end, l):eq({g(1), g(2), g(3)}))
  print('Apply(f, Range(1, 3)) =', Apply(f, l))
  assert(Apply(f, l):eq(f(1, 2, 3)))
  print('First(Apply(f, Range(1, 3))) =', First(Apply(f, l)))
  assert(First(Apply(f, l)):eq(1))
  print('Rest(Map(f, Range(1, 3))) =', Rest(Map(f, l)))
  assert(Rest(Map(f, l)):eq({f(2), f(3)}))
  print('Reduce(f, Range(1, 3)) =', Reduce(f, l))
  assert(Reduce(f, l):eq(f(f(1,2),3)))
  print('Reduce(f, Range(1, 3), 0) =', Reduce(f, l, 0))
  assert(Reduce(f, l, 0):eq(f(f(f(0,1),2),3)))
  print('GroupWith(Equal, {f,f,g,h,h,h,g,g}) =', GroupWith(Equal, {f,f,g,h,h,h,g,g}))
  assert(GroupWith(Equal, {f,f,g,h,h,h,g,g}):eq({{f,f},{g},{h,h,h},{g,g}}))
end

test[2] = function()
  local x, y = Symbols('x y')
  local one = Int(1)
  print('(1+2)+3 =',one+2+3)
  print('1+2+3 =',Plus(one+2+3))
  print('1+1/2+1/3 =',Plus(one+Rat(1,2)+Rat(1,3)))
  print('1+x+2*x*y+x*x+x*y-x^2-(x+y) =', 1+x+2*x*y+x*x+x*y-x^2-(x+y))
  assert((1+x+2*x*y+x*x+x*y-x^2-(x+y)):eq(Plus(1,Times(-1,y),Times(3,x,y))))
end

test[3] = function()
  local x, y, f = Symbols('x y f')
  local one = Int(1)
  print(Sqrt(128)*Sqrt(6))
  print(Expand((x-y)*(x+y)))
  print((f(x)*(x+y)*f(y)))
end

test[4] = function()
  local exp = (Sqrt(2)+Sqrt(3)+Sqrt(4))^2
  local r = Expand(exp)
  print('(Sqrt(2)+Sqrt(3)+Sqrt(4))^2 =', r)
  assert(r:eq((9+4*Sqrt(2)+4*Sqrt(3)+2*Sqrt(6))))
end



test[5] = function()
  print('Sum 1000')
  local s = List()
  for i=1, 1000 do 
    s[#s+1] = Int(i)
  end
  local sum = Apply(Plus, s)
  print('sum=', sum)
  assert(sum:eq(500500))
end

test[6] = function()
  print('Sum 1/n*(n+1)')
  local s = List()
  for i=1, 999 do
    s[#s+1] = Rat(1,i*(i+1))
  end
  local sum = Apply(Plus, s)
  print('sum=', sum)
  assert(sum:eq(Rat(999,1000)))
end

test[7] = function()
  local a, b, c = Symbols('a b c')
  local exp = Union(Set(a,b,c),Set(a,b,1,2))
  print('Union(Set(a,b,c),Set(a,b,1,2)) =', exp)
  exp = Intersection(Set(a,b,c),Set(a,b,1,2))
  print('Intersection(Set(a,b,c),Set(a,b,1,2)) =', exp)
  exp = In(a, Set(a,b,c))
  print('In(a, Set(a,b,c))', exp)
  exp = In(c, Set(a,b))
  print('In(c, Set(a,b))', exp)
end

test[8] = function()
  local A = Matrix(4, 4, 
    function(i, j) return 1/(i+j-1) end)
  local r = Det(A)
  print('Det(A) =', r)
  assert(r:eq(Rat(1,6048000)))
end

test[9] = function()
  local a, b, c = Symbols('a b c')
  local A = Matrix({1,2,12,a},{-2,3,11,b},{-1,4,18,c})
  local r = RREF(A)
  r = Num(r[3][4])
  print('Num(RREF(A)[3][4])=', r)
  assert(r:eq(Plus(Times(-5,a),Times(-6,b),Times(7,c))))
end


test[10] = function()
  local A = Matrix({1,2,12},{-2,3,11},{-1,4,18})
  local r = RREF(A)
  print('RREF(A)=', r)
  print('Rank(A)=', Rank(A))
end

test[11] = function()
  local x,y = Symbols('x y')
  local exp = -1+2*x+x^2-3*x*y+y^2+y
  print(exp)
  local r = TeX(exp)
  print('TeX(exp) =', r)
  assert(r:eq('x^2-3xy+y^2+2x+y-1'))
end

test[12] = function()
  local a, b, c = Symbols('a b c')
  local A = Matrix({1,2,3,4},{2,3,4,5},{3,4,5,6})
  local exp = Sub(A, {1,2}, {3,4})
  print('Sub(A, {1,2}, {3,4}) =', exp)
  exp = Tuple(exp)
  local r = exp:tex()
  print(exp, '=', r)
  print(Trans(A))
  A = Matrix({1,2},{3,4})
  print(Block({A,A},{A,A}))
  assert(r=='\\left(3,4,4,5\\right)')
end

test[13] = function()
  print('Expand (x-1)(1+...+x^n)')
  local x = Symbols('x')
  local s = List()
  for i=0, 9 do
    s[#s+1] = Power(x, i) 
  end
  print(s)
  s = Apply(Plus, s)
  print(s)
  local sum = Expand((x-1)*s)
  print('sum=', sum)
  local r = x^10-1
  print('r', r)
  assert(sum:eq(r))
end

test[14] = function()
  local x, f = Symbols('x f')
  print('Diff(Cos(f(x)^2), x) =',TeX(Diff(Cos(f(x)^2), x)))
end

test[14] = function()
  print(TeX(3+4*I))
  local A = Matrix({1,2,1+2*I},{-2,3,-2+3*I},{-1,4,-1+4*I})
  local r = RREF(A)
  print('RREF(A)=', r)
end

test[15] = function()
  local A = Matrix(
    {Zm(1,13), Zm(6,13), Zm(8,13)},
    {Zm(5,13), Zm(10,13), Zm(12,13)},
    {Zm(8,13), Zm(1,13), Zm(3,13)})
  local Id = Matrix(3,3, function(i,j)
    if i:eq(j) then
      return Zm(1,13)
    else
      return Int(0)
    end
  end)
  print('A =', A)
  print('Det(A)=', Det(A))
  print(Sub(RREF(Block({A, Id})),{1,3},{4,6}))
end

test[16] = function()
  local A = Matrix({1,-1},{2,1})  
  local B = Matrix({-3,2},{0,2})
  print(A..B)
  print(Choose(Range(1,60),6))
  print(Choose(Range(1,60),6))
  print(Choose(Range(1,60),6))
  print(Choose(Range(1,60),6))
end

test[17] = function()
  local a = List(Rat(5,7),Rat(4,7),Rat(2,7),Rat(2,7))
  local s = Apply(Plus, Map(function(t) return t*t end), a)
  local A = Matrix(4,4,
    function(i, j)
      if i:eq(1) then
        return a[j[1]]
      elseif j:eq(1) then
        return a[i[1]]
      elseif i:eq(j) then
        return (a[i[1]]^2-a[1]-1)/(1+a[1])
      else
        return a[i[1]]*a[j[1]]/(1+a[1])
      end
    end)
  print(A)
  print(A..Trans(A))
end

test[18] = function()
  local A = Rand({-4,5},5,5)
  print(A)
  print(Det(A))
  A = Rand({-4,4},6,6)
  print(A)
  print(Det(A))
  A = Rand({-2,2},8,8)
  print(A)
  print(Det(A))
  local lambda = Symbol('\\lambda')
  A = Rand({-3,3},3,3)
  print(A)
  A = A-lambda*Matrix(3,3,1)
  print(A)
  print(Expand(Det(A)):tex())
end

for i=1,#test do
  print('Test ',i)
  local time = os.clock()
  test[i]()
  print('\t time elapsed: ',os.clock()-time)
end

--profiler.stop()
--profiler.report("profiler.log")
