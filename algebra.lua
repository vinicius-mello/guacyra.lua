local guacyra = require('guacyra')
local number = require('number')
local binomial = number.binomial
local isInteger = number.isInteger
local factorization = number.factorization
local SymbEnv = require('symbenv').SymbEnv
local floor = math.floor

local Symbol = guacyra.Symbol
local Plus = guacyra.Plus
local Times = guacyra.Times
local Power = guacyra.Power
local Number = guacyra.Number
local Rational = guacyra.Rational
local Error = guacyra.Error
local Map = guacyra.Map
local Apply = guacyra.Apply
local SetDelayed = guacyra.SetDelayed

Plus.flat = true
Plus.orderless = true
Plus:addDown(function(exp)
  if Match(exp, Plus()) then
    return Number(0)
  elseif Match(exp, Plus(a_)) then
    return a
  elseif Match(exp, 0+b__) then
    return Plus(b)
  elseif Match(exp,Plus(a_(Number),b_(Number),c___)) then
    return Plus(Number(a[1]+b[1]),c)
  elseif Match(exp, Plus(a_(Number),p_(Rational),c___)) then
    if isInteger(a[1]) then
      return Plus(Rational(a[1]*p[2]+p[1],p[2]),c)
    else
      return Plus(Number((a[1]*p[2]+p[1])/p[2]),c)
    end
  elseif Match(exp, Plus(p_(Rational),q_(Rational),c___)) then
    return Plus(Rational(p[1]*q[2]+q[1]*p[2],p[2]*q[2]),c)
  end
  return nil
end)

local function ins(t,a,b)
  if t[a:tostring()] == nil then
    t[a:tostring()] = {a, Sequence(b)}
    return false
  else 
    local s = t[a:tostring()][2]
    s[#s+1] = b
    return true
  end 
end

Plus:addDown(function(exp)
  -- collect coeffs
  local r = Plus()
  local flag = false
  local coefs = {}
  for i=1,#exp do
    if Match(exp[i],Times(a_(Number),b_)) then
      flag = ins(coefs,b,Number(a[1])) or flag
    elseif Match(exp[i],Times(a_(Number),b__)) then
      flag = ins(coefs,b,Number(a[1])) or flag
    elseif Match(exp[i],Times(p_(Rational),b_)) then
      flag = ins(coefs,b,Rational(p[1],p[2])) or flag
    elseif Match(exp[i],Times(p_(Rational),b__)) then
      flag = ins(coefs,b,Rational(p[1],p[2])) or flag
    elseif Match(exp[i],Times(b__)) then
      flag = ins(coefs,b,Number(1)) or flag
    else
      local t = exp[i] 
      flag = ins(coefs,t,Number(1)) or flag
    end
  end
  if flag then 
    for k,v in pairs(coefs) do
      v[2][0] = Plus
      r[#r+1] = Times(v[2],v[1])
    end
    return r
  end
  return nil
end)

Times.flat = true
Times.orderless = true
Times:addDown(function(exp)
  if Match(exp, Times()) then
    return Number(1) 
  elseif Match(exp,Times(a_)) then
    return a
  elseif Match(exp, 1*a__) then
    return Times(a)
  elseif Match(exp,0*__) then
    return Number(0)
  elseif Match(exp,Times(a_(Number),b_(Number),c___)) then
    return Times(Number(a[1]*b[1]),c)
  elseif Match(exp,Times(a_(Number),p_(Rational),c___)) then
    if isInteger(a[1]) then
      return Times(Rational(a[1]*p[1],p[2]),c)
    else
      return Times(Number(a[1]*p[1]/p[2]),c)
    end
  elseif Match(exp,Times(p_(Rational),q_(Rational),c___)) then
    return Times(Rational(p[1]*q[1],p[2]*q[2]),c)
  end
  return nil
end)

Times:addDown(function(exp)
  if Match(exp,Times(-1,Plus(a__))) then
    return Map(function(t) return Times(-1,t) end, Plus(a))
  end
  return nil
end)

Times:addDown(function(exp)
  -- collect bases
  local r = Times()
  local flag = false
  local coefs = {}
  for i=1,#exp do
    if Match(exp[i],Power(a_,b_)) then
      flag = ins(coefs,a,b) or flag
    else
      local t = exp[i]
      flag = ins(coefs,t,Number(1)) or flag
    end
  end
  if flag then 
    for k,v in pairs(coefs) do
      v[2][0] = Plus
      r[#r+1] = Power(v[1],v[2])
    end
    return r
  end
  return nil
end)

Times:addDown(function(exp)
  -- collect expoents
  local r = Times()
  local flag = false
  local coefs = {}
  for i=1,#exp do
    if Match(exp[i],Power(a_(Number),b_)) then
      flag = ins(coefs,b,a) or flag
    else
      local t = exp[i]
      ins(coefs,Number(1),t)
    end
  end
  if flag then 
    for k,v in pairs(coefs) do
      v[2][0] = Times
      r[#r+1] = Power(v[2],v[1])
    end
    return r
  end
  return nil
end)

Power:addDown(function(exp)
  if Match(exp, _^0) then 
    return Number(1)
  elseif Match(exp, 1^_) then
    return Number(1)
  elseif Match(exp, a_^1) then
    return a
  elseif Match(exp, a_(Number)^b_(Number)) then
    if isInteger(a[1]) and isInteger(b[1]) then
      if b[1]<0 then
        return Rational(1,floor(a[1]^(-b[1])))
      elseif b[1]>0 then
        return Number(floor(a[1]^b[1]))
      end
    else
      return Number(a[1]^b[1])
    end
  elseif Match(exp, p_(Rational)^b_(Number)) then
    if isInteger(b[1]) then
      if b[1]<0 then
        return Rational(floor(p[2]^(-b[1])),floor(p[1]^(-b[1])))
      elseif b[1]>0 then
        return Rational(floor(p[1]^b[1]),floor(p[2]^b[1]))
      end
    else
      return Number((p[1]/p[2])^b[1])
    end
  elseif Match(exp, a_(Number)^p_(Rational)) then
    local function root(fac,p,q)
      local u, v = 1, 1
      for i=1,#fac do
        local fip = fac[i][2]*p
        local prime = fac[i][1]
        local a = floor(fip/q)
        local b = fip - a*q
        u = u * floor(prime^a)
        v = v * floor(prime^b)
      end
      return u, v
    end
    if isInteger(a[1]) then
      if a[1]>0 then
        if p[1]>0 then
          local fact = factorization(a[1])
          local u,v = root(fact,p[1],p[2])
          if u==1 and p[1]==1 then 
            return nil
          else 
            return Times(u,Power(v,Rational(1,p[2])))
          end
        else
          local fact = factorization(a[1])
          p[1] = -p[1]
          local k = math.floor(p[1]/p[2])
          local r = p[1]-k*p[2]
          local u,v = root(fact,p[2]-r,p[2])
          return Times(Rational(u,a[1]^(k+1)),Power(v,Rational(1,p[2])))
        end
      end
    else
      return Number(a[1]^(p[1]/p[2]))  
    end
  elseif Match(exp, a_(Rational)^p_(Rational)) then
    return Times(Power(Number(a[1]),p),Power(Number(a[2]),Rational(-p[1],p[2])))
  elseif Match(exp, Power(Power(a_,b_),c_)) then
    return Power(a,b*c)
  end
  return nil
end)

Power:addDown(function(exp)
  if Match(exp, Power(Times(a__),e_)) then
    return Map(function(t) return Power(t,e) end,Times(a))
  end
  return nil
end)

local Expand = Symbol('Expand')
Expand:addDown(function(exp)
  if Match(exp, Expand(Times(a__))) then
    local aa = a
    for j=1,#aa do
      if Match(aa[j], Plus(b__)) then
        local r = Plus()
        for k=1,#b do
          local t = aa:copy()
          t[j] = b[k]
          r[#r+1] = Expand(Times(t))
        end 
        return r
      elseif Match(aa[j], Power(Plus(b__),n_(Number))) and isInteger(n[1]) and n[1]>0 then 
        local t = aa:copy()
        t[0] = Times
        t[j] = Expand(Power(Plus(b),n[1]))
        return Expand(t)
      end
    end
    return exp[1]
  end
  return nil
end)

Expand:addDown(function(exp)
  if Match(exp, Expand(Power(Plus(a_,b__),n_(Number)))) and isInteger(n[1]) and n[1]>0 then
    local r = Plus()
    for i=0,n[1] do
      r[#r+1]=Expand(Times(binomial(n[1],i),Power(a,n[1]-i),Expand(Power(Plus(b),i))))
    end
    return r
  end  
  return nil
end)

Expand:addDown(function(exp)
  if Match(exp, Expand(Plus(a_,b__))) then
    return Plus(Expand(a),Expand(Plus(b)))
  end  
  return nil
end)

Expand:addDown(function(exp)
  if Match(exp, Expand(a_)) then
    return a
  end  
  return nil
end)

local NumeratorDenominator = Symbol('NumeratorDenominator')
NumeratorDenominator:addDown(function(exp)
  if Match(exp, NumeratorDenominator(p_(Rational))) then
    return List(p[1],p[2])
  elseif Match(exp, NumeratorDenominator(a_(Number))) then
    return List(a,1)
  elseif Match(exp, NumeratorDenominator(Power(a_,b_(Number)))) then
    if b[1]<0 then return List(1,Power(a,-b[1]))
    else return List(Power(a,b),1) end
  elseif Match(exp, NumeratorDenominator(Times(a__))) then
    local e = Map(NumeratorDenominator,List(a)):eval()
    local num = Times()
    local den = Times()
    for i=1,#e do
      num[#num+1] = e[i][1]
      den[#den+1] = e[i][2]
    end
    return List(num,den)
  elseif Match(exp, NumeratorDenominator(Plus(a__))) then
    local e = Map(NumeratorDenominator,List(a)):eval()
    local num = Plus()
    local den = Times()
    local t = {}
    for i=1,#e do
      local ei = e[i][2]
      local eis = ei:tostring()
      if not t[eis] then
        t[eis] = true
        den[#den+1] = ei
      end 
    end
    for i=1,#e do
      local r = ((den:copy())*e[i][1]/e[i][2]):eval()
      num[#num+1] = r
    end
    return List(num,den)
  elseif Match(exp, NumeratorDenominator(a_)) then
    return List(a,1)
  end
  return nil
end)

local Denominator = Symbol('Denominator')
Denominator:addDown(function(exp)
  if Match(exp, Denominator(a_)) then
    local l = NumeratorDenominator(a):eval()
    return l[2]
  end
  return nil
end)

local Numerator = Symbol('Numerator')
Numerator:addDown(function(exp)
  if Match(exp, Numerator(a_)) then
    local l = NumeratorDenominator(a):eval()
    return l[1]
  end
  return nil
end)

local Together = Symbol('Together')
Together:addDown(function(exp)
  if Match(exp, Together(a_)) then
    local l = NumeratorDenominator(a):eval()
    if l[2][0]==Number then
      return l[1]/l[2]
    else
      return Together(l[1])/Together(l[2])
    end
  end
  return nil
end)

local Sqrt = Symbol('Sqrt')
local function init()
  SymbEnv()
  In[1] = SetDelayed(Sqrt(x_),Power(x,Rational(1,2)))
end

init()

return {
  Expand = Expand,
  NumeratorDenominator = NumeratorDenominator,
  Numerator = Numerator,
  Denominator = Denominator,
  Together = Together,
  Sqrt = Sqrt,
}
