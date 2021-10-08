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

for i=1,#test do
  print('Test ',i)
  local time = os.clock()
  test[i]()
  print('\t time elapsed: ',os.clock()-time)
end

--profiler.stop()
--profiler.report("profiler.log")
