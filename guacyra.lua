local comb = require('combenum')
local number = require('number')
local gcd = number.gcd
local isInteger = number.isInteger

local guacyra = {}

local Symbol = {'Symbol'}
Symbol[0] = Symbol
setmetatable(Symbol, guacyra)

local function makeAtom(s)
  local t = {s}
  t[0] = Symbol
  setmetatable(t, guacyra)
  return t
end

local Number = makeAtom('Number')
local Rational = makeAtom('Rational')
local String = makeAtom('String')
local Boolean = makeAtom('Boolean')
local Function = makeAtom('Function')

local function isObject(e)
  return getmetatable(e)==guacyra 
end

local function isAtomHead(e) 
  return e==Symbol   or e==Number
    or   e==Rational or e==String
    or   e==Boolean  or e==Function
end

local function isAtom(e)
  return isObject(e) and isAtomHead(e[0])
end
guacyra.isAtom = isAtom

local function isSymbol(e)
  return isObject(e) and e[0]==Symbol
end
guacyra.isSymbol = isSymbol

local function isBlankSymbol(e)
  return isSymbol(e) and e[1]:sub(-1)=='_'
end

guacyra.Symbol = Symbol
guacyra.Number = Number
guacyra.Rational = Rational
guacyra.String = String
guacyra.Boolean = Boolean
guacyra.Function = Function

guacyra.debug = {}
-- lua 5.3 workaround
local unpack = unpack or table.unpack

local List
local Blank
local BlankSequence
local BlankNullSequence

local tostr

local function makeExp(h,...) 
  local t = {...}
  t[0] = h
  setmetatable(t, guacyra)
  if h == Symbol then
    if type(t[1])~='string' then
      error('Invalid symbol: Symbol('..tostr(t[1])..')')
    end
    t.up = {}
    t.down = {}
    return t
  end
  local function blankType(b,h) 
    local bl = b
    local bls = bl[1]
    if bls:sub(-3)=='___' then
      return BlankNullSequence(String(bls:sub(1,-4)),h)
    elseif bls:sub(-2)=='__' then
      return BlankSequence(String(bls:sub(1,-3)),h)
    else
      return Blank(String(bls:sub(1,-2)),h)
    end
  end
  if #t==1 and isBlankSymbol(h) 
           and (isSymbol(t[1]) and not isBlankSymbol(t[1])) then
    return blankType(h,t[1])
  end
  if isBlankSymbol(h) then
    h = blankType(h)
    t[0] = h
  end
  if h == Rational and isInteger(t[1]) and isInteger(t[2]) then
		local d = gcd(t[1],t[2])
		t[1] = t[1]/d
		t[2] = t[2]/d
		if t[2]<0 then 
	  	t[2]=-t[2]
			t[1]=-t[1]
		end
		if t[2]==1 then
			t[0] = Number
			t[2] = nil
		end
  end
  if not isAtomHead(h) then
    for i=1,#t do
      local a = t[i]
      if isBlankSymbol(a) then
        t[i] = blankType(a)
	    elseif getmetatable(a)~=guacyra then
        if type(a) == 'number' then
          t[i] = Number(a)
        elseif type(a) == 'string' then
          t[i] = String(a)
        elseif type(a) == 'table' then
          t[i] = makeExp(List,unpack(a))
        elseif type(a) == 'function' then
          t[i] = Function(a)
        elseif type(a) == 'boolean' then
          t[i] = Boolean(a)
        end
      end
    end
  else
    -- TODO typecheck
    for i=1,#t do
      if isObject(t[i]) then
        print(t[i])
        error('Ill-formed atom: '..tostr(h)..'(...,'..tostr(t[i])..',...)')
      end
    end
  end
  return t
end

guacyra.__call = makeExp
List = Symbol('List')
guacyra.List = List
local Sequence = Symbol('Sequence')
guacyra.Sequence = Sequence
local Error = Symbol('Error')
guacyra.Error = Error
local Null = Symbol('Null')
guacyra.Null = Null
Blank = Symbol('Blank')
guacyra.Blank = Blank
BlankSequence = Symbol('BlankSequence')
guacyra.BlankSequence = BlankSequence
BlankNullSequence = Symbol('BlankNullSequence')
guacyra.BlankNullSequence = BlankNullSequence

tostr = function(e)
  if not isObject(e) then
	  return tostring(e)
  end
  if isAtom(e) then
    if e[0]==Symbol then
      return e[1]
    end
    if e[0]==String then
      return '"'..e[1]..'"'
    end
    if e[0]==Number then
      return ''..e[1]
    end
    if e[0]==Rational then
      return ''..e[1]..'/'..e[2]
    end
    if e[0]==Boolean then
      if e[1] then return 'True'
      else return 'False' end
    end
    if e[0]==Function then
      return tostring(e[1])
    end
  end
  if e[0]==Blank then
    if e[2] then
      return e[1][1]..'_'..tostr(e[2])
    else
      return e[1][1]..'_'
    end
  end
  if e[0]==BlankSequence then
    if e[2] then
      return e[1][1]..'__'..tostr(e[2])
    else
      return e[1][1]..'__'
    end
  end
  if e[0]==BlankNullSequence then
    if e[2] then
      return e[1][1]..'___'..tostr(e[2])
    else
      return e[1][1]..'___'
    end
  end
  local s,cs
  if e[0]==List then
    s, cs = '{', '}'
  else 
    s = tostr(e[0])..'('
    cs = ')'
  end
  for i=1,#e do
    if i>1 then s = s..',' end 
    s = s..tostr(e[i])
  end
  s = s..cs
  return s
end

guacyra.__tostring = tostr
guacyra.tostring = tostr

local function copy(ex)
  if isAtom(ex) then
    return ex
  else
    local r = {}
    for i=0,#ex do
      r[i] = copy(ex[i])
    end
    setmetatable(r, guacyra)
    return r 
  end
end
guacyra.copy = copy

local function equal(ea,eb)
  local sa = #ea
  local sb = #eb
  if sa~=sb then
    return false
  end
  if isAtom(ea) and isAtom(eb) then
    for i=0,#ea do
      if ea[i]~=eb[i] then
        return false
      end
    end
    return true
  end
  if not isAtom(ea) and not isAtom(eb) then
    for i=0,#ea do
      if not equal(ea[i],eb[i]) then
        return false
      end
    end
    return true
  end
  return false
end
guacyra.equal = equal

local function length(ex) 
  if isAtom(ex) then
    return 1
  end
  local s = 0
  for i=1,#ex do
    s = s + length(ex[i])
  end
  return s
end
guacyra.length = length

local atomOrder = {
  [Number] = 1,
  [Rational] = 2,
  [String] = 3,
  [Symbol] = 4,
  [Boolean] = 5,
  [Function] = 6,
}

local Plus = Symbol('Plus')
guacyra.Plus = Plus
local Times = Symbol('Times')
guacyra.Times = Times
local Power = Symbol('Power')
guacyra.Power = Power

local function lessTree(ea,eb)
  local function ty(e)
    if isAtom(e) then return 1
    else              return 2
    end
  end 
  local ta = ty(ea)
  local tb = ty(eb)
  if ta<tb then return true end
  if tb<ta then return false end
  if ta==1 then
    if ea[0]==eb[0] then
      if ea[0]==String or ea[0]==Number then
        return ea[1]<eb[1]
      elseif ea[0]==Rational then
        return ea[1]/ea[2]<eb[1]/eb[2]
      else
        return tostring(ea[1])<tostring(eb[1])
      end
    else 
      return atomOrder[ea[0] ]<atomOrder[eb[0] ]
    end
  end
  if #ea<#eb then return true end
  if #eb<#ea then return false end
  for i=0,#ea do
    if lessTree(ea[i],eb[i]) then
      return true
    elseif lessTree(eb[i],ea[i]) then
      return false
    end
  end
  return false
end
guacyra.less = lessTree

guacyra.__index = guacyra


-- lua 5.2 workaround
local setfenv = setfenv or function(f, t)
--    f = (type(f) == 'function' and f or debug.getinfo(f + 1, 'f').func)
    local name
    local up = 0
    repeat
        up = up + 1
        name = debug.getupvalue(f, up)
    until name == '_ENV' or name == nil
    if name then
      debug.upvaluejoin(f, up, function() return name end, 1) -- use unique upvalue
      debug.setupvalue(f, up, t)
    end
end

getfenv = getfenv or function(f)
--    f = (type(f) == 'function' and f or debug.getinfo(f + 1, 'f').func)
    local name, val
    local up = 0
    repeat
        up = up + 1
        name, val = debug.getupvalue(f, up)
    until name == '_ENV' or name == nil
    return val
end

local function subst(ex,sub) 
  if isAtom(ex) then 
    if ex[0]==Symbol and sub[ex[1]]~= nil then
      return copy(sub[ex[1]])
    else 
      return ex
    end
  else
    local r = {}
    for i=0,#ex do
      r[i] = subst(ex[i],sub)
    end
    setmetatable(r, guacyra)  
    return r
  end
end
guacyra.subst = subst

local function delta(sub1,sub2) 
  for k,v1 in pairs(sub1) do
    local v2 = sub2[k]
    if v2~=nil then
      if not equal(v1,v2) then
        return false
      end
    end 
  end
  return true
end

local function unionDelta(sub,th)
  local thr = {}
  for i=1,#th do
    if delta(sub,th[i]) then
      local subi = {}
      for k,v in pairs(sub) do
        subi[k] = v
      end
      for k,v in pairs(th[i]) do
        subi[k] = v
      end
      thr[#thr+1] = subi
    end
  end
  return thr
end

local function printSub(d)
  for k,v in pairs(d) do
    print('\t',k,v)
  end
end

-- Adapted from "Non-linear Associative-Commutative Many-to-One
-- Pattern Matching with Sequence Variables"
-- by Manuel Krebber
local matchOneToOne
local function matchSequence(s,p,fa,comu,th)
  local n = #s
  local m = #p
  local nstar = 0
  for i=1,m do 
    if p[i][0]==BlankNullSequence then 
      nstar = nstar + 1
    end
  end
  if m-nstar>n then return {} end
  local nplus = 0
  for i=1,m do 
    if p[i][0]==BlankSequence then 
      nplus = nplus + 1
    end
  end
  if fa~=nil then
    for i=1,m do 
      if p[i][0]==Blank then 
        nplus = nplus + 1
      end
    end
  end
  local nfree = n-m+nstar
  local nseq = nstar+nplus
  local thr = {}
  if nseq==0 and nfree>0 then
    return thr
  end
  for perm in comb.permutations(n) do
    for k in comb.weak_compositions(nfree,nseq) do
      local i = 1
      local j = 1
      local thprime = {}
      for ti=1,#th do
        local subprime = {}
        for key,v in pairs(th[ti]) do
          subprime[key] = v
        end
        thprime[#thprime+1] = subprime
      end
      for l=1,m do
        local lsub = 1
        local hl = p[l][0]
        if hl==BlankNullSequence or hl==BlankSequence
          or (hl==Blank and fa~=nil) then
          lsub = lsub + k[j]
          if hl==BlankNullSequence then lsub = lsub-1 end
          j = j+1 
        end
        local sprime = Sequence()
        for si=i,i+lsub-1 do 
          sprime[#sprime+1] = s[perm[si]]
        end
        thprime = matchOneToOne(sprime,p[l],fa,thprime)
        if #thprime==0 then
          break
        end
        i = i+lsub 
      end
      for ti=1,#thprime do
        thr[#thr+1] = thprime[ti]
      end
    end
    if not comu then
      break
    end
  end
  return thr
end

matchOneToOne = function(s,p,fa,th) 
  local n = #s
  local hp = p[0]
  if hp==Blank and fa==nil then
    local subprime = {}
    local name = p[1][1]
    if name~='' then 
      subprime[name] = s[1]
    end
    if n==1 then
      if p[2]==nil or (p[2]==s[1][0]) then 
        return unionDelta(subprime,th)
      end
    end
  elseif hp==Blank or hp==BlankSequence or hp==BlankNullSequence then
    local subprime = {}
    local name = p[1][1]
    local head = p[2]
    if hp==Blank and fa~=nil then
      if name~='' then
        if #s>1 then
          subprime[name] = fa(s)
        else
          subprime[name] = s[1]
        end
      end
    else
      if name~='' then
        subprime[name] = s
      end
    end
    local flag = true
    if head then
      for i=1,#s do
        if not equal(s[i][0],head) then
          flag = false
          break
        end
      end
    end
    if flag and (hp==BlankNullSequence or n>=1) then
      return unionDelta(subprime,th)
    end
  elseif isAtom(p) then
    if n==1 and equal(s[1],p) then 
      return th
    end
  elseif n==1 then
    local hs = s[1][0]
    if equal(hp,hs) or hp==Blank then
      local sp = p:copy()
      sp[0] = Sequence
      local sq = s[1]:copy()
      sq[0] = Sequence
      local faprime 
      if hp.flat then
        faprime = hp
      else
        faprime = nil
      end
      th = matchSequence(sq,sp,faprime,hp.orderless,th)
      if hp==Blank then
        local subh = {}
        local name = p[1][1]
        if name~='' then
          subh[name] = hs
        end
        return unionDelta(subh,th)
      else
        return th
      end
    end
  end
  return {}
end

guacyra.matches = function(ex,pat)
  return matchOneToOne(Sequence(ex),pat,nil,{{}}) 
end

local function match(ex,pat,cap)
  if isAtom(pat) then
    return equal(pat,ex)
  end
  if pat[0]==Blank then
    local name = pat[1][1]
    local head = pat[2]
    if head~=nil and not equal(ex[0],head) then
      return false
    end
    if name == '' then
      return true
    end
    local en = rawget(cap,name)
    if en~=nil then
      return equal(ex,en)
    else
      cap[name] = ex
      return true
    end
  end
  for i=0,#pat do
    if (pat[i][0]==BlankNullSequence or pat[i][0]==BlankSequence)
       and i~=#pat then
       error('Blank sequence must be the last part: '..tostr(pat))
    end 
    if pat[i][0]==BlankNullSequence 
       or (pat[i][0]==BlankSequence and i<=#ex) then
      local name = pat[i][1][1]
      local head = pat[i][2]
      local exr = Sequence()
      for j=i,#ex do
        exr[#exr+1] = ex[j]
        if head and not equal(ex[j][0],head) then
          return false
        end
      end
      if name == '' then
        return true
      end
      local en = rawget(cap,name)
      if en~=nil then
        return equal(en, exr)
      else 
        cap[name] = exr
        return true
      end
    end
    if i>#ex then return false end
    if not match(ex[i],pat[i],cap) then
      return false
    end
  end
  if #pat<#ex then
    return false
  end
  return true
end
guacyra.match = match

local function transform(exp,trans)
  local env = {}
  local mt = {}
  setmetatable(env,mt)
  env.ClearCapture = function()
    local del = {}
    for k,v in pairs(env) do
      if k:sub(-1)~='_' and type(v)~='function' then
        del[#del+1] = k
      end 
    end
    for i=1,#del do
      env[del[i]] = nil 
    end
  end
  env.Match = function(exp,pat)
    env.ClearCapture()
    local r = match(exp,pat,env)
    if r and guacyra.debug.match then
      print('match:\t',pat,exp)
    end
    return r
  end
  mt.__index = function(t,k)
    local l = rawget(t,k)
    if l~=nil then
      return l
    else
      if k:sub(-1)=='_' then
        local s = Symbol(k)
        env[k] = s
        return s
      else
        return _G[k]
      end
    end
  end
  local oldenv = getfenv(trans)
  setfenv(trans,env)
  local ret = trans(exp) 
  setfenv(trans,oldenv)
  return ret
end
guacyra.transform = transform

local function evalR(e)
  if guacyra.debug.eval then
    print('eval:\t',e)
  end
  if e[0]==Symbol then
    if e.value then
      return evalR(e.value)
    else 
      return e
    end
  end
  if isAtom(e) then
    return e
  end
  local head = evalR(e[0])
  local ex = head()
  if head[0]==Function then
    for i=1,#e do
      ex[i] = evalR(e[i])
    end
    return evalR(head[1](unpack(ex)))
  end 
  if head.holdAll then
    for i=1,#e do
      ex[i] = e[i]
    end
  else
    for i=1,#e do
      if head.holdFirst and i==1  then
        ex[i] = e[i]
      else 
        ex[i] = evalR(e[i])
      end
    end
  end
  if not head.sequenceHold then
    local i = 1
    while i<=#ex do
      if ex[i][0]==Sequence then
        local exi = table.remove(ex,i)
        for j=1,#exi do
          table.insert(ex,i+j-1,exi[j])
        end
        i = i + #exi
      else
        i = i + 1
      end
    end
  end
  if head.flat then
    local i = 1
    while i<=#ex do
      if equal(ex[i][0],head) then
        local exi = table.remove(ex,i)
        for j=1,#exi do
          table.insert(ex,i+j-1,exi[j])
        end
        i = i + #exi
      else
        i = i + 1
      end
    end
  end
  if guacyra.debug.sort then
    print('sort:\t',e)
  end
  if head.orderless then
    table.sort(ex,lessTree)
  end
  local tex
  for i=1,#ex do
    local uphead = ex[i][0]
    if uphead[0]==Symbol and uphead.up then
      for j=1,#uphead.up do
        tex = transform(ex, uphead.up[j])
        if tex then
          return evalR(tex) 
        end
      end  
    end
  end
  if head[0]==Symbol and head.down then
    for j=1,#head.down do
      tex = transform(ex, head.down[j])
      if tex then
        return evalR(tex) 
      end
    end  
  end
  return ex
end

local function eval(e)
  return evalR(copy(e))
end
guacyra.eval = eval

guacyra.addDown = function(ex,tr)
  if ex[0]==Symbol then
    ex.down[#ex.down+1] = tr
  end
end

guacyra.addUp = function(ex,tr)
  if ex[0]==Symbol then
    ex.up[#ex.up+1] = tr
  end
end

local Set = Symbol('Set')
guacyra.Set = Set
Set.holdFirst = true
Set:addDown(function(exp)
  if Match(exp, Set(a_(Symbol),b_)) then
    a.value = b
    return b
  elseif Match(exp, Set(f_(p__),v_)) then
    local fe = p:copy()
    fe[0] = f
    local ve = v
    f:addDown(function(exp2)
      local r = exp2:matches(fe)
      if #r>0 then
        return ve:subst(r[1])
      end
      return nil
    end)
    return Null
  end
  return nil 
end)

local SetDelayed = Symbol('SetDelayed')
guacyra.SetDelayed = SetDelayed
SetDelayed.holdAll = true
SetDelayed:addDown(function(exp)
  if Match(exp, SetDelayed(a_(Symbol),b_)) then
    a.value = b
    return b
  elseif Match(exp, SetDelayed(f_(p__),v_)) then
    local fe = p:copy()
    fe[0] = f
    local ve = v
    f:addDown(function(exp2)
      local r = exp2:matches(fe)
      if #r>0 then
        return ve:subst(r[1])
      end
      return nil
    end)
    return Null
  end
  return nil 
end)

local Apply = Symbol('Apply')
guacyra.Apply = Apply
Apply:addDown(function(exp)
  if Match(exp, Apply(a_,b_(c___))) then
    return a(c)
  end
  return nil 
end)
 
local Map = Symbol('Map')
guacyra.Map = Map
Map:addDown(function(exp)
  if Match(exp, Map(f_,h_(a___))) then
    for i=1,#a do
      a[i] = f(a[i])
    end
    return h(a)
  end
  return nil 
end)

local Cat = Symbol('Cat')
Cat.flat = true
guacyra.Cat = Cat
Cat:addDown(function(exp)
  if Match(exp, Cat(a_(String))) then
    return a
  elseif Match(exp, Cat(a_(String),b_(String),c___)) then
    return Cat(a[1]..b[1],c)
  end
  return nil 
end)

local Timing = Symbol('Timing')
Timing.holdFirst = true
guacyra.Timing = Timing
Timing:addDown(function(exp)
  if Match(exp, Timing(a_)) then
    local st = os.clock()
    local r = a:eval()
    local et = os.clock()
    return List(et-st, r)
  end
  return nil 
end)


guacyra.__add = function(a,b) return Plus(a,b) end 
guacyra.__sub = function(a,b) return Plus(a,Times(-1,b)) end
guacyra.__unm = function(a)   return Times(-1,a) end
guacyra.__mul = function(a,b) return Times(a,b) end
guacyra.__div = function(a,b) return Times(a,Power(b,-1)) end
guacyra.__pow = function(a,b) return Power(a,b) end

guacyra.importSymbols = function(t)
  for k,v in pairs(t) do
    if isSymbol(v) then
      _G[k] = v
    end
  end
end

return guacyra
