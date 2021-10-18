
-- Number Theory
local floor, infinite, random = math.floor, math.huge, math.random
local abs = math.abs

local function gcd(a, b)
  while b ~= 0 do a, b = b, a % b end
  return abs(a)
end

local function isInt(a) return type(a) == 'number' and a == floor(a) end

local function binomial(n, k)
  if k > n then return nil end
  if k > n / 2 then k = n - k end
  local numer, denom = 1, 1
  for i = 1, k do
    numer = numer * (n - i + 1)
    denom = denom * i
  end
  return floor(numer / denom) -- lua 5.3
end

--- Calculate the modular power for any exponent.
local function fmodpow(bse, exp, mod)
  bse = bse % mod
  local prod = 1
  while exp > 0 do
    if exp % 2 == 1 then prod = prod * bse % mod end
    exp = floor(exp / 2)
    bse = (bse * bse) % mod
  end
  return prod
end

local function witnesses(n)
  if n < 1373653 then
    return 2, 3
  elseif n < 4759123141 then
    return 2, 7, 61
  elseif n < 2152302898747 then
    return 2, 3, 5, 7, 11
  elseif n < 3474749660383 then
    return 2, 3, 5, 7, 11, 13
  else
    return 2, 325, 9375, 28178, 450775, 9780504, 1795265022
  end
end

--- Given a number n, returns numbers r and d such that 2^r*d+1 == n
--- Miller-Rabin primality test
local function miller_rabin(n, ...)
  local s, d = 0, n - 1
  while d % 2 == 0 do d, s = d / 2, s + 1 end
  for i = 1, select('#', ...) do
    local witness = select(i, ...)
    if witness >= n then break end
    local x = fmodpow(witness, d, n)
    if (x ~= 1) then
      local t = s
      while x ~= n - 1 do
        t = t - 1
        if t <= 0 then return false end
        x = (x * x) % n
        if x == 1 then return false end
      end
    end
  end
  return true
end

local mrthreshold = 1e3

local primes = setmetatable({
  2, 3 --[[just hard-code the even special case and following number]]
}, {
  __index = function(self, index)
    if type(index) == 'number' then
      for i = #self, index - 1 do local dummy = self[i] end -- Precalculate previous primes to avoid building up a stack
      for candidate = self[index - 1] + 2 --[[All primes >2 are odd]] , infinite do
        if index > mrthreshold then
          if miller_rabin(candidate, witnesses(candidate)) then
            rawset(self, index, candidate)
            return candidate
          end
        else
          local half = floor(candidate / 2)
          for i = 1, index - 1 do
            local div = self[i]
            if div > half then
              rawset(self, index, candidate);
              return candidate
            end -- A number can't possibly be divisible by something greater than its half
            if candidate % div == 0 then break end -- Candidate is divisible by a prime, this not prime itself
          end
        end
      end
    end
  end
})

local function factorize(subject)
  if subject == 1 then
    return -- Can be ommitted for implicit return ;)
  elseif subject > 0 then
    for i = 1, infinite do
      local candidate = primes[i]
      if subject % candidate == 0 then
        return candidate, factorize(subject / candidate)
      end
    end
  else
    return nil,
           "Can't be bothered to look up if negative numbers have a prime factorization"
  end
end

local function factorization(n)
  local a = {factorize(n)}
  local count = 0
  local cur = a[1]
  local r = {}
  for i = 1, #a + 1 do
    local ai = a[i]
    if ai == cur then
      count = count + 1
    else
      r[#r + 1] = {cur, count}
      cur = ai
      count = 1
    end
  end
  return r
end

-- Kernel
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

local Int = makeAtom('Int')
local Rat = makeAtom('Rat')
local Str = makeAtom('Str')
local Bool = makeAtom('Bool')
local Fun = makeAtom('Fun')
local Nil = makeAtom('Nil')

local List, _, __, ___
guacyra.Symbol = Symbol
guacyra.Int = Int
guacyra.Rat = Rat
guacyra.Str = Str
guacyra.Bool = Bool
guacyra.Fun = Fun
guacyra.Nil = Nil

-- lua 5.3 workaround
local unpack = unpack or table.unpack

local function isObject(e)
  return getmetatable(e) == guacyra
end

local function isAtomHead(e)
  return e == Symbol or e == Int or
    e == Rat or e == Str or
    e == Bool or e == Fun or e == Nil
end

local function isAtom(e)
  local h = e[0]
  return h == Symbol or h == Int or
    h == Rat or h == Str or
    h == Bool or h == Fun or e == Nil
end
guacyra.isAtom = isAtom

local function isSymbol(e)
  return e[0] == Symbol
end
guacyra.isSymbol = isSymbol

local function isFun(e)
  return e[0] == Fun
end
guacyra.isFun = isFun

local function lhead(e) 
  if isSymbol(e) then
    return e
  else 
    return lhead(e[0])
  end
end

local makeExp

local function conv(a)
  if not isObject(a) then
    if type(a) == 'number' then
      a = Int(floor(a))
    elseif type(a) == 'string' then
      a = Str(a)
    elseif type(a) == 'boolean' then
      a = Bool(a) 
    elseif type(a) == 'table' then
      a = makeExp(List, unpack(a))
    elseif type(a) == 'function' then
      a = Fun(a)
    end
  end
  return a
end

local eval

makeExp = function(h, ...)
  local t = {...}
  t[0] = h
  setmetatable(t, guacyra)
  if h == Symbol then
    if type(t[1]) ~= 'string' then
      error('Invalid symbol: Symbol(' .. tostr(t[1]) .. ')')
    end
    t.up = {}
    t.down = {}
    return t
  end
  if h == Rat then
    if not isInt(t[1]) or not isInt(t[2]) then
      error('Ill-formed Rat')
    end
    local d = gcd(t[1], t[2])
    t[1] = floor(t[1] / d) -- lua 5.3
    t[2] = floor(t[2] / d)
    if t[2] < 0 then
      t[2] = -t[2]
      t[1] = -t[1]
    end
    if t[2] == 1 then
      t[0] = Int
      t[2] = nil
    end
    return t
  end
  if (h==_ or h==__ or h==___)
    and type(t[1])=='table' and not isObject(t[1]) then
    local key = ''
    local type = _
    for k,v in pairs(t[1]) do
      if isSymbol(v) or isFun(v) then
        key = k
        type = v
      end
    end
    t[1]=Str(key)
    if type ~= _ then
      t[2] = type
    end
    t.isPattern = true
    return t
  end
  if not isAtomHead(h) then
    local f = false or t[0].isPattern
    for i = 1, #t do
      t[i] = conv(t[i])
      f = f or t[i].isPattern  
    end
    if not f then
      local r = eval(t)
      return r
    else
      t.isPattern = true
      return t
    end
  end
  return t
end
guacyra.__call = makeExp

local function cat(h, ...)
  local t
  t = {...}
  t[0] = h
  if not isAtomHead(h) then
    for i = 1, #t do
      t[i] = conv(t[i])
    end
  end
  setmetatable(t, guacyra)
  return t
end

List = Symbol('List')
guacyra.List = List
_ = Symbol('_')
guacyra._ = _
__ = Symbol('__')
guacyra.__ = __
___ = Symbol('___')
guacyra.___ = ___

local True = Bool(true)
guacyra.True = True
local False = Bool(false)
guacyra.False = False
local function test(v) 
  if isObject(v) and v[0]==Bool then
    return v[1]
  end
  return v
end
guacyra.test = test

local function Symbols(vl, global) 
  local vars = {}
  for var in vl:gmatch("%S+") do
    local sym = Symbol(var)
    table.insert(vars, sym)
    if global then
      global[var] = sym
    end
  end
  return unpack(vars)
end

tostr = function(e)
  if not isObject(e) then return tostring(e) end
  if isAtom(e) then
    if e[0] == Symbol then return e[1] end
    if e[0] == Str then return e[1] end
    if e[0] == Int then return '' .. e[1] end
    if e[0] == Rat then return '' .. e[1] .. '/' .. e[2] end
    if e[0] == Bool then
      if e[1] then
        return 'True'
      else
        return 'False'
      end
    end
    if e[0] == Fun then
      return e.name or tostring(e[1])
    end
  end
  if e[0] == _ then
    if e[2] then
      return e[1][1] .. '_' .. tostr(e[2])
    else
      return e[1][1] .. '_'
    end
  end
  if e[0] == __ then
    if e[2] then
      return e[1][1] .. '__' .. tostr(e[2])
    else
      return e[1][1] .. '__'
    end
  end
  if e[0] == ___ then
    if e[2] then
      return e[1][1] .. '___' .. tostr(e[2])
    else
      return e[1][1] .. '___'
    end
  end
  local s, cs
  if e[0] == List then
    s, cs = '[', ']'
  else
    s = tostr(e[0]) .. '('
    cs = ')'
  end
  for i = 1, #e do
    if i > 1 then s = s .. ',' end
    s = s .. tostr(e[i])
  end
  s = s .. cs
  return s
end

guacyra.__tostring = tostr
guacyra.tostring = tostr

local function copy(ex)
  if isAtom(ex) then
    return ex
  else
    local r = {}
    for i = 0, #ex do r[i] = copy(ex[i]) end
    setmetatable(r, guacyra)
    return r
  end
end
guacyra.copy = copy

local function equalR(ea, eb)
  local sa = #ea
  local sb = #eb
  if sa ~= sb then return false end
  if isAtom(ea) and isAtom(eb) then
    for i = 0, #ea do if ea[i] ~= eb[i] then return false end end
    return true
  end
  if not isAtom(ea) and not isAtom(eb) then
    for i = 0, #ea do if not equalR(ea[i], eb[i]) then return false end end
    return true
  end
  return false
end
local function equal(ea, eb)
  return equalR(ea, eb)
end
guacyra.equal = equal
--guacyra.__eq = equal
guacyra.eq = function(a, b)
  return equal(a, conv(b))
end
local function has(ex, subex)
  if isAtom(ex) then
    return equal(ex, subex)
  end
  if equal(ex, subex) then
    return true
  else
    for i=1, #ex do
      if has(ex[i], subex) then
        return true
      end
    end
    return false
  end
end

local Numeric, Sequence, Plus, Times, Power =
  Symbols('Numeric Sequence Plus Times Power', guacyra)

local function isNumeric(e)
  return e[0] == Int or e[0] == Rat
end

local function numericValue(e)
  if e[0] == Int then
    return e[1]
  elseif e[0] == Rat then
    return e[1] / e[2]
  end
end

local Mono, Poly = Symbols('Mono Poly', guacyra)

-- Joel S. Cohen, Computer Algebra and Symbolic Computation: Mathematical Methods
local function less(u, v)
  -- O1
  if isNumeric(u) and isNumeric(v) then
    return numericValue(u) < numericValue(v)
  end
  if u[0] == Str and v[0] == Str then
    return u[1] < v[1]
  end
  -- O2
  if isSymbol(u) and isSymbol(v) then
    return u[1] < v[1]
  end
  -- O3
  if (u[0] == Plus and v[0] == Plus)
  or (u[0] == Times and v[0] == Times) then
    local m = #u
    local n = #v
    while m > 0 and n > 0 do
      if equal(u[m], v[n]) then
        m = m - 1
        n = n - 1
      else
        return less(u[m], v[n])
      end
    end
    return m < n
  end
  -- O4
  if u[0] == Power and v[0] == Power then
    if equal(u[1], v[1]) then
      return less(u[2], v[2])
    else
      return less(u[1], v[1])
    end
  end
  -- O5.5
  if u[0]==Mono and v[0]==Mono then
    return Mono.order(u, v)
  end
  -- O6
  if u[0] == v[0] then
    local m = #u
    local n = #v
    local i = 1
    while i <= m and i <= n do
      if equal(u[i], v[i]) then
        i = i + 1
      else
        return less(u[i], v[i])
      end
    end
    return m < n
  end
  -- O7
  if isNumeric(u) and not isNumeric(v) then
    return true
  elseif not isNumeric(u) and isNumeric(v) then
    return false
  end
  -- O8
  if u[0] == Times then
    return less(u, cat(Times, v))
  elseif v[0] == Times then
    return less(cat(Times, u), v)
  end
  -- O9
  if u[0] == Power then
    return less(u, cat(Power, v, 1))
  elseif v[0] == Power then
    return less(cat(Power, u, 1), v)
  end
  -- O10
  if u[0] == Plus then
    return less(u, cat(Plus, v))
  elseif v[0] == Plus then
    return less(cat(Plus, u), v)
  end
  -- O12
  if isSymbol(v) and equal(u[0], v) then
    return false
  elseif isSymbol(u) and equal(u, v[0]) then
    return true
  end
  -- Catch all
  return tostring(u) < tostring(v)
end

guacyra.less = less
guacyra.lt = function(a, b)
  return less(a, conv(b))
end
guacyra.gt = function(a, b)
  return less(conv(b), a)
end
guacyra.le = function(a, b)
  return guacyra.lt(a, b) or guacyra.eq(a, b)
end
guacyra.ge = function(a, b)
  return guacyra.gt(a, b) or guacyra.eq(a, b)
end

guacyra.__index = guacyra

local function subst(ex, sub)
  if isAtom(ex) then
    if ex[0] == Symbol and sub[ex[1]] ~= nil then
      local a = conv(sub[ex[1]])
      return copy(a)
    else
      return ex
    end
  else
    local r = {}
    for i = 0, #ex do r[i] = subst(ex[i], sub) end
    setmetatable(r, guacyra)
    return r
  end
end
guacyra.subst = subst

local function matchR(ex, pat, cap)
  if isAtom(pat) then return equal(pat, ex) end
  if pat[0] == _ then
    local name = pat[1][1]
    local head = pat[2]
    if head ~= nil then
      if isFun(head) and not test(head[1](ex)) then
        return false
      elseif isSymbol(head) and not equal(ex[0], head) then
        return false
      end
    end
    if name == '' then return true end
    local en = rawget(cap, name)
    if en ~= nil then
      return equal(ex, en)
    else
      cap[name] = ex
      return true
    end
  end
  for i = 0, #pat do
    if (pat[i][0] == ___ or pat[i][0] == __) and i ~=
      #pat then error('Blank sequence must be the last part: ' .. tostr(pat)) end
    if pat[i][0] == ___ or
      (pat[i][0] == __ and i <= #ex) then
      local name = pat[i][1][1]
      local head = pat[i][2]
      local exr = cat(Sequence)
      for j = i, #ex do
        exr[#exr + 1] = ex[j]
        if head ~= nil then
          if isFun(head) and not test(head[1](ex[j])) then
            return false
          elseif isSymbol(head) and not equal(ex[j][0], head) then
            return false
          end
        end
      end
      if name == '' then return true end
      local en = rawget(cap, name)
      if en ~= nil then
        return equal(en, exr)
      else
        cap[name] = exr
        return true
      end
    end
    if i > #ex then return false end
    if not matchR(ex[i], pat[i], cap) then return false end
  end
  if #pat < #ex then return false end
  return true
end
guacyra.match = function(exp, pat, cap)
  local cap2 = {}
  local ret = matchR(exp, pat, cap2)
  if ret then for k, v in pairs(cap2) do cap[k] = v end end
  return ret
end

local function evalR(e, rec)
  --print('eval: ', e)
  local head = e[0]
  local ex = cat(head)
  if rec then 
    for i = 1, #e do ex[i] = eval(e[i], rec) end
  else
    for i = 1, #e do ex[i] = e[i] end
  end
  if head[0] == Fun then
    return eval(head[1](unpack(ex)))
  end
  local lh = lhead(head)
  if not lh.sequenceHold then
    local i = 1
    while i <= #ex do
      if ex[i][0] == Sequence then
        local exi = table.remove(ex, i)
        for j = 1, #exi do table.insert(ex, i + j - 1, exi[j]) end
        i = i + #exi
      else
        i = i + 1
      end
    end
  end
  if lh.flat then
    local i = 1
    while i <= #ex do
      if equal(ex[i][0], head) then
        local exi = table.remove(ex, i)
        for j = 1, #exi do table.insert(ex, i + j - 1, exi[j]) end
        i = i + #exi
      else
        i = i + 1
      end
    end
  end
  if lh.orderless then table.sort(ex, less) end
  local tex
  for i = 1, #ex do
    local uphead = lhead(ex[i])
    if uphead.up then
      for j = 1, #uphead.up do
        tex = uphead.up[j](ex)
        if tex then return --[[eval]](tex) end
      end
    end
  end
  if lh.down then
    for j = 1, #lh.down do
      tex = lh.down[j](ex)
      if tex then return --[[eval]](tex) end
    end
  end
  return ex
end

eval = function(e, rec)
  if isAtom(e) then
    return e
  else
    return evalR(e, rec)
  end
end

guacyra.eval = eval

local max_args = 10
local function getArgs(fun)
  local args = {}
  local hook = debug.gethook()
  local argHook = function( ... )
    local info = debug.getinfo(3)
    if 'pcall' ~= info.name then return end
    for i = 1, max_args do
      local name, value = debug.getlocal(2, i)
      if '(*temporary)' == name 
        or '(temporary)' == name then
        debug.sethook(hook)
        error('')
        return
      end
      table.insert(args,name)
    end
  end
  debug.sethook(argHook, "c")
  pcall(fun)
  return args
end

local function Rule(pat, fu, sym)
  local tab
  if not sym then
    sym = lhead(pat)
    tab = sym.down
  else
    tab = sym.up
  end
  local args = getArgs(fu)
  tab[#tab+1] = function(ex)
    local cap = {}
    if ex:match(pat, cap) then
      local cargs = {}
      for i=1,#args do cargs[#cargs+1] = cap[args[i]] end
      return fu(unpack(cargs))
    else
      return nil
    end
  end
end
guacyra.Rule = Rule

local Equal, Less = 
  Symbols('Equal Less', guacyra)
Rule(Equal(_{a=_}, _{b=_}),
function(a, b) return Bool(equal(a, b)) end)
Rule(Less(_{a=_}, _{b=_}),
function(a, b) return Bool(less(a, b)) end)
Rule(Numeric(_{a=_}),
function(a)
  return Bool(isNumeric(a))
end)

local Map, Apply, First, Rest, Fold, Reduce, GroupWith = 
  Symbols('Map Apply First Rest Fold Reduce GroupWith', guacyra)

Rule(Map(_{a=_}, _{b=_}),
function(a, b)
  local l = cat(List)
  for i=1,#b do
    l[#l+1] = a(b[i])
  end
  l[0] = b[0]
  return  l
end)
Rule(Apply(_{a=_}, _{b=_}(___{c=_})),
function(a, b, c)
  return a(c)
end)
Rule(First(_{a=_}(_{b=_}, ___{c=_})),
function(a, b, c)
  return b
end)
Rule(Rest(_{a=_}(_{b=_}, ___{c=_})),
function(a, b, c)
  return a(c)
end)
Rule(Fold(_{a=_}, _{b=_}, _{c=_}),
function(a, b, c)
  local t = b
  for i = 1, #c do
    t = a(t, c[i]) end
  return t
end)
Rule(Reduce(_{a=_}, _{b=List}),
function(a, b)
  local r = b[1]
  for i = 2, #b do
    r = a(r, b[i])
  end
  return r
end)
Rule(Reduce(_{a=_}, _{b=List}, _{c=_}),
function(a, b, c)
  local r = c
  for i = 1, #b do
    r = a(r, b[i])
  end
  return r
end)
Rule(GroupWith(_{a=_}, _{b=_}),
function(a, b)
  local r = cat(List)
  local last = b[1]
  local l = cat(List, last)
  for i=2,#b do
    if test(a(last, b[i])) then
      l[#l+1] = b[i]
    else
      r[#r+1] = l
      last = b[i]
      l = cat(List, last)
    end
  end
  r[#r+1] = l
  return r
end)

local Cat, Range, RandInt = 
  Symbols('Cat Range RandInt', guacyra)

Rule(Cat(___{c=_}),
function(c)
  local t = ""
  for i = 1, #c do
    if isAtom(c[i]) and c[i][0] == Str then
      t = t .. (c[i][1])
    else
      t = t .. (c[i]:tostring())
    end
  end
  return Str(t)
end)

Rule(Range(_{a=Int}, _{b=Int}),
function(a, b)
  local t = cat(List)
  for i = a[1], b[1] do
    t[#t+1] = Int(i) end
  return t
end)
Rule(RandInt({_{a=Int}, _{b=Int}}),
function(a, b)
  return Int(random(a[1], b[1]))
end)
Rule(RandInt({_{a=Int}, _{b=Int}},
  _{n=Int}),
function(a, b, n)
  local t = cat(List)
  for i = 1, n[1] do
    t[#t+1] = Int(random(a[1], b[1]))
  end
  return t
end)

guacyra.__add = Plus
guacyra.__sub = function(a, b) return Plus(a, Times(-1, b)) end
guacyra.__unm = function(a) return Times(-1, a) end
guacyra.__mul = Times
guacyra.__div = function(a, b) return Times(a, Power(b, -1)) end
guacyra.__pow = Power
local NumericQ = Fun(
function(ex)
  return Bool(isNumeric(ex))
end)
guacyra.NumericQ = NumericQ

Plus.flat = true
Plus.orderless = true
Rule(Plus(),
function() return Int(0) end)
Rule(Plus(_{a=_}),
function(a) return a end)
Rule(Plus(_{a=Int}, _{b=Int}),
function(a, b) return Int(a[1]+b[1]) end)
Rule(Plus(_{a=Int}, _{b=Rat}),
function(a, b) return Rat(a[1]*b[2]+b[1], b[2]) end)
Rule(Plus(_{a=Rat}, _{b=Int}),
function(a, b) return Rat(b[1]*a[2]+a[1], a[2]) end)
Rule(Plus(_{a=Rat}, _{b=Rat}),
function(a, b) return Rat(a[1]*b[2]+b[1]*a[2], a[2]*b[2]) end)
Rule(Plus(0, __{a=_}),
function(a) return Plus(a) end)
Rule(Plus(_{a=_},_{a=_}),
function(a)
  return Times(2, a)
end)

Times.flat = true
Times.orderless = true
Rule(Times(),
function() return Int(1) end)
Rule(Times(_{a=_}),
function(a) return a end)
Rule(Times(_{a=Int}, _{b=Int}),
function(a, b) return Int(a[1]*b[1]) end)
Rule(Times(_{a=Int}, _{b=Rat}),
function(a, b) return Rat(a[1]*b[1], b[2]) end)
Rule(Times(_{a=Rat}, _{b=Int}),
function(a, b) return Rat(b[1]*a[1], a[2]) end)
Rule(Times(_{a=Rat}, _{b=Rat}),
function(a, b) return Rat(a[1]*b[1], a[2]*b[2]) end)
Rule(Times(1, __{b=_}),
function(b) return Times(b) end)
Rule(Times(0, __{b=_}),
function(b) return Int(0) end)
Rule(Times(-1, Plus(__{a=_})),
function(a)
  local r = Map(function(t) return Times(-1, t) end, List(a))
  return Apply(Plus, r)
end)
Rule(Times(_{a=_},_{a=_}),
function(a)
  return Power(a, 2)
end)

Rule(Plus(__{a=_}),
function(a)
  if #a==2 then
    return nil
  end
  local last = a[1]
  local flag = false
  local l = cat(List)
  for i=2,#a do
    local ca = cat(Plus, last, a[i])
    local p = Plus(last, a[i])
    if equal(ca, p) then
      l[#l+1] = last
      last = a[i]
    else
      flag = true
      last = p
    end
  end
  l[#l+1] = last
  if flag then 
    return Apply(Plus, l)
  else 
    return nil
  end
end)

Rule(Times(__{a=_}),
function(a)
  if #a==2 then
    return nil
  end
  local last = a[1]
  local flag = false
  local l = cat(List)
  for i=2,#a do
    local ca = cat(Times, last, a[i])
    local p = Times(last, a[i])
    if equal(ca, p) then
      l[#l+1] = last
      last = a[i]
    else
      flag = true
      last = p
    end
  end
  l[#l+1] = last
  if flag then 
    return Apply(Times, l)
  else 
    return nil
  end
end)

Rule(Plus(Times(__{a=_}),Times(__{a=_})),
function(a)
  return Times(2, a)
end, Times)
Rule(Plus(Times(__{a=_}), Times(_{c=NumericQ},__{a=_})),
function(c, a)
  return Times(Plus(c, 1), a)
end, Times)
Rule(Plus(Times(_{c=NumericQ},__{a=_}),Times(_{d=NumericQ},__{a=_})),
function(c, a, d)
  return Times(Plus(c, d), a)
end, Times)
Rule(Plus(_{a=_},Times(_{c=NumericQ}, _{a=_})),
function(a, c)
  return Times(Plus(c, 1), a)
end, Times)

Rule(_{}^0,
function() return Int(1) end)
Rule(1^_{},
function() return Int(1) end)
Rule(_{a=_}^1,
function(a) return a end)
Rule(_{a=Int}^_{b=Int},
function(a, b)
  if b[1] < 0 then
    return Rat(1, floor(a[1] ^ (-b[1])))
  elseif b[1] > 0 then
    return Int(floor(a[1] ^ b[1]))
  end
end)
Rule(_{p=Rat}^_{b=Int},
function(p, b)
  if b[1] < 0 then
    return Rat(floor(p[2]^(-b[1])), floor(p[1]^(-b[1])))
  elseif b[1] > 0 then
    return Rat(floor(p[1]^b[1]), floor(p[2]^b[1]))
  end
end)
Rule(_{a=Int}^_{p=Rat},
function(a, p)
  local function root(fac, p, q)
    local u, v = 1, 1
    for i = 1, #fac do
      local fip = fac[i][2] * p
      local prime = fac[i][1]
      local a = floor(fip / q)
      local b = fip - a * q
      u = u * floor(prime ^ a)
      v = v * floor(prime ^ b)
    end
    return u, v
  end
  if a[1] > 0 then
    if p[1] > 0 then
      local fact = factorization(a[1])
      local u, v = root(fact, p[1], p[2])
      if u == 1 and p[1] == 1 then
        return nil
      else
        return Times(u, Power(v, Rat(1, p[2])))
      end
    else
      local fact = factorization(a[1])
      p[1] = -p[1]
      local k = math.floor(p[1] / p[2])
      local r = p[1] - k * p[2]
      local u, v = root(fact, p[2] - r, p[2])
      return Times(Rat(u, a[1] ^ (k + 1)), Power(v, Rat(1, p[2])))
    end
  end
end)
Rule(_{a=Rat}^_{p=Rat},
function(a, p)
  return Times(Power(Int(a[1]), p),
    Power(Int(a[2]), Rat(-p[1], p[2])))
end)

Rule(Power(Power(_{a=_}, _{b=_}), _{c=_}),
function(a, b, c)
  return Power(a, b * c)
end)

Rule(Power(Times(__{a=_}), _{b=_}),
function(a, b)
  return Apply(Times, 
    Map(function(t) return Power(t, b) end, List(a)))
end)

Rule(Times(_{a=_}, Power(_{a=_}, _{e=_})),
function(a, e)
  if a[0]==Int then
    return nil
  else
    return Power(a, Plus(e, 1))
  end
end, Power)

Rule(Times(Power(_{a=_}, _{e=_}),
           Power(_{a=_}, _{f=_})),
function(a, e, f)
  return Power(a, Plus(e, f))
end, Power)

Rule(Times(Power(_{a=Int}, _{e=NumericQ}),
           Power(_{b=Int}, _{e=NumericQ})),
function(a, e, b)
  return Power(Times(a, b), e)
end, Power)

local Sqrt, Expand = 
  Symbols('Sqrt Expand', guacyra)
Rule(Sqrt(_{a=_}),
function(a) return a^Rat(1,2) end)

Rule(Expand(Times(_{a=_}, Plus(_{b=_}, _{c=_}))),
function(a, b, c)
  return Plus(Expand(Times(a, b)), Expand(Times(a, c)))
end)
Rule(Expand(Times(_{a=_}, Plus(_{b=_}, __{c=_}))),
function(a, b, c)
  return Plus(Expand(Times(a, b)), Expand(Times(a, Plus(c))))
end)
Rule(Expand(Power(Plus(_{a=_}, _{b=_}), _{n=Int})),
function(a, b, n)
  local l = cat(List)
  for i=0,n[1] do
    l[#l+1] = Expand(
      Times(binomial(n[1], i),
        Expand(Power(a,i)),
        Expand(Power(b,n[1]-i))))
  end
  return Apply(Plus, l)
end)
Rule(Expand(Power(Plus(_{a=_}, __{b=_}), _{n=Int})),
function(a, b, n)
  local l = cat(List)
  for i=0,n[1] do
    l[#l+1] = Expand(
      Times(binomial(n[1], i),
        Expand(Power(a,i)),
        Expand(Power(Plus(b),n[1]-i))))
  end
  return Apply(Plus, l)
end)
Rule(Expand(Plus(__{a=_})), 
function(a)
  return Apply(Plus, Map(Expand, List(a)))
end)
Rule(Expand(Times(_{a=_},__{b=_})),
function(a, b)
  local tb =Times(b)
  local t = Expand(tb)
  if equal(t, tb) then
    return nil
  else
    return Expand(Times(a, t))
  end
end)
Rule(Expand(_{a=_}), 
function(a)
  return a
end)

local Numerator, Denominator, NumeratorDenominator, Together = 
  Symbols('Numerator Denominator NumeratorDenominator Together', guacyra)

Rule(NumeratorDenominator(_{p=Rat}),
function(p)
  return List(p[1], p[2])
end)
Rule(NumeratorDenominator(_{a=Int}),
function(a)
  return List(a[1], 1)
end)
Rule(NumeratorDenominator(Power(_{a=_}, _{b=Int})),
function(a, b)
  if b[1]<0 then
    return List(1, Power(a, -b[1]))
  else
    return List(Power(a, b), 1)
  end
end)
Rule(NumeratorDenominator(Power(_{a=_}, _{q=Rat})),
function(a, q)
  if q[1]<0 then
    return List(1, Power(a, Rat(-q[1],q[2])))
  else
    return List(Power(a, q), 1)
  end
end)
Rule(NumeratorDenominator(Times(__{a=_})),
function(a)
  local e = Map(NumeratorDenominator, List(a))
  local num = cat(Times)
  local den = cat(Times)
  for i=1,#e do
    num[#num+1] = e[i][1]
    den[#den+1] = e[i][2]
  end
  return List(eval(num), eval(den))
end)
Rule(NumeratorDenominator(Plus(__{a=_})),
function(a)
  local e = Map(NumeratorDenominator, List(a))
  local num = cat(Plus)
  local den = cat(Times)
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
    local r = (den:copy())*e[i][1]/e[i][2]
    num[#num+1] = r
  end
  return List(eval(num), eval(den))
end)
Rule(NumeratorDenominator(_{a=_}),
function(a)
  return List(a, 1)
end)
Rule(Numerator(_{a=_}),
function(a)
  local nd = NumeratorDenominator(a)
  return nd[1]
end)
Rule(Denominator(_{a=_}),
function(a)
  local nd = NumeratorDenominator(a)
  return nd[2]
end)
Rule(Together(_{a=_}),
function(a)
  local l = NumeratorDenominator(a)
  if l[2][0]==Int then
    return l[1]/l[2]
  else
    return Together(l[1])/Together(l[2])
  end
end)

local Set, In, Union, Intersection = 
  Symbols('Set In Union Intersection', guacyra)
Set.orderless = true
Rule(Set(__{c=_}),
function(c)
  local r = cat(Set, c[1])
  local flag = false
  for i = 2,#c do
    if not equal(c[i], c[i-1]) then
      r[#r+1] = c[i]
    else
      flag = true
    end
  end
  if flag then 
    return r
  end
  return nil
end)

Rule(Union(_{a=Set}, _{b=Set}),
function(a, b)
  local r = Apply(List, a)
  for i=1,#b do r[#r+1] = b[i] end
  return Apply(Set, r)
end)

Rule(Intersection(_{a=Set}, _{b=Set}),
function(a, b)
  local r = cat(Set)
  local i = 1
  local j = 1
  while i<=#a and j<=#b do
    if less(a[i],b[j]) then 
      i = i+1
    elseif less(b[j], a[i]) then
      j = j+1
    else
      r[#r+1] = a[i]
      i = i+1
      j = j+1
    end
  end
  return r
end)

Rule(In(_{a=_}, _{b=Set}),
function(a, b)
  for i=1,#b do
    if equal(a, b[i]) then
      return True
    end
  end
  return False
end)

local function deg(m) 
  local r = 0
  local l = m[2]
  for i=1,#l do
    r = r+l[i][1]
  end
  return r
end

local function deglex(m1, m2)
  local d1, d2 = deg(m1), deg(m2)
  if d1<d2 then 
    return false
  elseif d1>d2 then
    return true
  end
  return less(m2[2], m1[2])
end

Mono.order = deglex

Rule(Power(Mono(_{c=NumericQ}, _{e=List}), _{p=Int}),
function(c, e, p) 
  e = copy(e)
  for i=1,#e do e[i] = e[i]*p end
  return Mono(c^p, e)
end, Mono)

Rule(Times(__{m=Mono}),
function(m)
  local l = cat(List)
  local c = Int(1)
  for i=1,#m do
    c = c*m[i][1]
    local n = m[i][2]
    for j=1,#n do
      if not l[j] then l[j] = Int(0) end 
      l[j] = l[j]+n[j] 
    end
  end
  return Mono(c, l)
end, Mono)

Rule(Times(_{c=NumericQ}, __{m=Mono}),
function(c, m)
  local l = cat(List)
  for i=1,#m do
    c = c*m[i][1]
    local n = m[i][2]
    for j=1,#n do
      if not l[j] then l[j] = Int(0) end 
      l[j] = l[j]+n[j] 
    end
  end
  return Mono(c, l)
end, Mono)

Poly.orderless = true
Poly.flat = true
Rule(Poly(_{c=NumericQ}, ___{m=Mono}),
function(c, m)
  local n
  if #m>0 then
    n = #m[1][2]
  end
  local l = cat(List)
  for i=1,n do l[#l+1] = Int(0) end
  return Poly(Mono(c, l), m)
end)

local function isPolynomial(p, var)
  if isSymbol(p) then
    var[p[1]] = p
    return true
  elseif isNumeric(p) then
    return true 
  elseif p[0]==Plus or p[0]==Times then
    for i=1,#p do
      if not isPolynomial(p[i], var) then
        return false
      end
    end
    return true 
  elseif p[0]==Power then
    if isPolynomial(p[1], var) 
      and p[2][0]==Int and p[2][1]>0 then
      return true
    end
  end
  return false
end

local function isMonomial(p, var)
  if isSymbol(p) then
    var[p[1]] = p
    return true
  elseif isNumeric(p) then
    return true 
  elseif p[0]==Power then
    if isSymbol(p[1]) 
      and p[2][0]==Int and p[2][1]>0 then
      var[p[1][1]] = p[1]
      return true
    end
  elseif p[0]==Times then
    for i=1,#p do
      if not isMonomial(p[i], var) then
        return false
      end
    end
    return true 
  end
  return false
end

local function isExpandedPolynomial(p, var)
  if isMonomial(p, var) then
    return true
  elseif p[0]==Plus then
    for i=1,#p do
      if not isMonomial(p[i], var) then
        return false
      end
    end
    return true 
  end
  return false
end

local function expToPoly(p, var)
  local s = {}
  for k,v in pairs(var) do
    s[#s+1] = k
  end
  table.sort(s)
  local subs = {}
  local n = #s
  local l = cat(List)
  for i=1,n do l[#l+1] = Int(0) end
  for i=1,n do 
    local ll = copy(l)
    ll[i] = Int(1)
    subs[s[i]] = cat(Mono, 1, ll)
  end
  subs['Plus'] = Poly
  local r = p:subst(subs)
  return r:eval(true), s
end

local TeXP = Symbol("TeXP")
local TeX = Symbol("TeX")
guacyra.TeX = TeX
guacyra.tex = function(e)
  return TeX(e)[1]
end
Rule(TeXP(Plus(__{c=_})),
function(c)
  return Cat('(', TeX(Plus(c)), ')')
end)
Rule(TeXP(_{a=_}),
function(a) return TeX(a) end)
Rule(TeX(Times(_{p=Rat}, _{a=Symbol})),
function(p, a)
  if p[1] < 0 then
    local s = (TeX(Times(-p[1], a)))[1]
    return Str('-\\frac{'..s..'}{'..p[2]..'}')
  else
    local s = (TeX(Times(p[1], a)))[1]
    return Str('\\frac{'..s..'}{'..p[2]..'}')
  end
end)
Rule(TeX(_{p=Rat}),
function(p)
  local a, b = p[1], p[2]
  if a<0 then
    return Str('-\\frac{'..(-a)..'}{'..b..'}')
  else
    return Str('\\frac{'..(a)..'}{'..b..'}')
  end
end)
Rule(TeX(Times(-1,__{a=_})),
function(a) 
  return Cat('-', TeXP(Times(a)))
end)
Rule(TeX(Times(__{a=_})),
function(a)
  local l = NumeratorDenominator(Times(a))
  if l[2][0]==Int then
    return Apply(Cat,Map(TeXP,List(a)))
  else
    local num = TeX(l[1])
    local den = TeX(l[2])
    return Cat('\\frac{',num,'}{',den,'}')
  end
end)
Rule(TeX(Power(_{a=_},_{b=Rat})),
function(a, b)
  if b[1] == 1 then
    if b[2] == 2 then
      return Cat('\\sqrt{', TeX(a), '}')
    else
      return Cat('\\sqrt['..b[2]..']{',TeX(a),'}')
    end
  else
    return Cat(TeXP(a),'^{', TeX(b), '}')
  end
end)
Rule(TeX(Power(_{a=_}, _{b=Int})),
function(a, b)
  if b[1]<0 then
    return Cat('\\frac{1}{',TeX(Power(a,-b[1])),'}')
  else
    b = ''..b[1]
    if #b>1 then
      return Cat(TeXP(a), '^{'..b..'}')
    else
      return Cat(TeXP(a), '^'..b)
    end
  end
end)
Rule(TeX(Power(_{a=Symbol}, _{b=_})),
function(a, b)
  return Cat(a[1] .. '^{', TeX(b),'}')
end)
Rule(TeX(Power(_{a=_}, _{b=_})),
function(a, b)
    return Cat(TeXP(a), '^{', TeX(b),'}')
end)

local function formatPoly(p, vars)
  if p[0]==Mono then
    local s
    if equal(p[1], Int(1)) then
      if deg(p)==0 then return '1' end
      s = ''
    elseif equal(p[1], Int(-1)) then
      if deg(p)==0 then return '-1' end
      s = '-'
    else 
      s = TeX(p[1])[1]
    end
    local l = p[2]
    for i=1,#l do
      local ll = l[i]
      if ll[1]==1 then
        s = s..vars[i] 
      elseif ll[1]>1 then
        local ls = tostring(ll)
        if #ls==1 then
          s = s..vars[i]..'^'..ls        
        else
          s = s..vars[i]..'^{'..ls..'}'
        end
      end
    end
    return s
  elseif p[0]==Poly then
    local s
    for i=1,#p do
      if i==1 then
        s = formatPoly(p[i], vars)
      else
        local ss = formatPoly(p[i], vars)
        if ss:sub(1,1)~='-' then
          s = s..'+'
        end
        s = s..ss
      end
    end
    return s
  end
end

Rule(TeX(Plus(__{c=_})),
function(c)
  local vars = {}
  local pp = Plus(c)
  if isExpandedPolynomial(pp, vars) then
    local p, s = expToPoly(pp, vars)
    return Str(formatPoly(p, s))
  end
  local s = ''
  for i=1,#c do
    local t = TeX(c[i])
    if t[1]:sub(1,1)~='-' and i~=1 then
      s = s..'+'
    end
    s = s..t[1]
  end
  return Str(s)
end)

Rule(TeX(Set(__{a=_})),
function(a)
  local s='\\{'
  for i=1,#a do
    if i~=1 then
      s = s..','
    end
    s = s..(TeX(a[i])[1])
  end
  s = s..'\\}'
  return Str(s)
end)

Rule(TeX(List(__{a=_})),
function(a)
  local s='['
  for i=1,#a do
    if i~=1 then
      s = s..','
    end
    s = s..TeX(a[i])[1]
  end
  s = s..']'
  return Str(s)
end)

Rule(TeX(_{a=_}),
function(a)
  return Str(a:tostring())
end)

local Diff, Derivative, Sin, Cos, Exp, Log, Pi = 
  Symbols('Diff Derivative Sin Cos Exp Log Pi', guacyra)

Rule(Exp(0),
function() return Int(1) end)
Rule(Log(1),
function() return Int(0) end)
Rule(Sin(0),
function() return Int(0) end)
Rule(Sin(Pi),
function() return Int(0) end)
Rule(Sin(Times(_{n=Int}, Pi)),
function() return Int(0) end)
Rule(Sin(Times(_{p=Rat}, Pi)),
function(p)
  local a, b = p[1], p[2]
  if a < 0 then 
    return -Sin(a*Pi/b)
  elseif a/b > 2 then
    return Sin((a%(2*b))*Pi/b)
  elseif a/b > 1 then
    return -Sin((a-b)*Pi/b)
  elseif a/b > 0.5 then
    return Sin((b - a)*Pi/b)
  elseif a == 1 and b == 2 then
    return Int(1)
  elseif a == 1 and b == 3 then
    return Sqrt(3)/2
  elseif a == 1 and b == 4 then
    return Sqrt(2)/2
  elseif a == 1 and b == 6 then
    return Rat(1, 2)
  else
    return nil
  end
end)
Rule(Cos(0),
function() return Int(1) end)
Rule(Cos(Pi),
function() return Int(-1) end)
Rule(Cos(Times(_{n=Int}, Pi)),
function() return Int((-1)^n[1]) end)
Rule(Cos(Times(_{p=Rat}, Pi)),
function(p)
  local a, b = p[1], p[2]
  if a < 0 then 
    return Cos((-a)*Pi/b)
  elseif a/b > 2 then
    return Cos((a%(2*b))*Pi/b)
  elseif a/b > 1 then
    return -Cos((a-b)*Pi/b)
  elseif a/b > 0.5 then
    return -Cos((b - a)*Pi/b)
  elseif a == 1 and b == 2 then
    return Int(0)
  elseif a == 1 and b == 3 then
    return Rat(1, 2)
  elseif a == 1 and b == 4 then
    return Sqrt(2)/2
  elseif a == 1 and b == 6 then
    return Sqrt(3)/2
  else
    return nil
  end
end)
Rule(Diff(_{k=_}, _{x=Symbol}),
function(k, x)
  if not has(k, x) then return Int(0) end
  return nil
end)
Rule(Diff(_{x=Symbol},_{x=Symbol}),
function(x) return Int(1) end)
Rule(Diff(Power(_{x=Symbol}, _{n=Int}), _{x=Symbol}),
function(x, n) return n*x^(n-1) end)
Rule(Derivative(Log)(1)(_{x=_}),
function(x) return 1/x end)
Rule(Derivative(Exp)(1)(_{x=_}),
function(x) return Exp(x) end)
Rule(Derivative(Sin)(1)(_{x=_}),
function(x) return Cos(x) end)
Rule(Derivative(Cos)(1)(_{x=_}),
function(x) return -Sin(x) end)
Rule(Diff(Times(_{k=_}, __{a=_}), _{x=Symbol}),
function(k, x, a)
  if not has(k, x) then 
    return k*Diff(Times(a), x)
  else
    return Times(Diff(k, x), a)+k*Diff(Times(a), x)
  end
end)
Rule(Diff(Plus(__{a=_}), _{x=Symbol}), 
function(a, x) 
  return Map(function(t) return Diff(t,x) end, Plus(a))
end)
Rule(Diff(Power(_{f=_}, _{n=NumericQ}), _{x=Symbol}),
function(f, n, x)
  return Times(n, Power(f, n-1), Diff(f, x))
end)
Rule(Diff(_{f=_}(_{y=_}), _{x=Symbol}),
function(f, y, x)
  return Times(Derivative(f)(1)(y), Diff(y, x))
end)
Rule(TeX(Pi),
function() return Str('\\pi') end, Pi)
Rule(TeX(Exp(_{a=_})),
function(a)
  return Cat('e^{', TeX(a), '}')
end, Exp)
Rule(TeX(Log(_{a=_})),
function(a)
  return Cat('\\log{', TeX(a), '}')
end, Log)
Rule(TeX(Sin(_{a=_})),
function(a)
  return Cat('\\sin{', TeX(a), '}')
end, Sin)
Rule(TeX(Cos(_{a=_})),
function(a)
  return Cat('\\cos{', TeX(a), '}')
end, Cos)
Rule(TeX(Derivative(_{f=_})(1)(_{x=_})),
function(f, x)
  return Cat(TeX(f), "{'}(", TeX(x),')')
end, Derivative)

local Zp = Symbols('Zp', guacyra)
Rule(Numeric(Zp(_{a=Int}, _{p=Int})),
function(a, p)
  return True
end, Zp)
Rule(Zp(0,_{p=Int}),
function(p) return Int(0) end)
Rule(Zp(_{a=Int}, _{p=Int}),
function(a, p)
  if a[1]>=0 and a[1]<p[1] then
    return nil
  else
    return cat(Zp, a[1] % p[1], p)
  end
end)
Rule(Plus(_{a=Int}, Zp(_{b=Int}, _{p=Int})),
function(a, b, p)
  return Zp((a[1]+b[1])%p[1], p)
end, Zp)
Rule(Plus(Zp(_{a=Int},_{p=Int}), Zp(_{b=Int},_{p=Int})),
function(a, b, p)
  return Zp((a[1]+b[1])%p[1], p)
end, Zp)
Rule(Times(_{a=Int}, Zp(_{b=Int},_{p=Int})),
function(a, b, p)
  return Zp((a[1]*b[1])%p[1], p)
end, Zp)
Rule(Times(Zp(_{a=Int},_{p=Int}), Zp(_{b=Int},_{p=Int})),
function(a, b, p)
  return Zp((a[1]*b[1])%p[1], p)
end, Zp)
Rule(Power(_{z=Zp}, _{n=Int}),
function(z, n)
  local p = z[2][1]
  local r = Int(1)
  for i=1,math.abs(n[1]) do
    r = r*z
  end
  if n[1]<0 then
    for i=1,p-1 do
      if (i*r):eq(Zp(1, p)) then
        return Zp(i, p)
      end
    end
  end
  return r
end, Zp)
Rule(TeX(Zp(_{a=Int}, _{p=Int})),
function(a)
  return TeX(a)
end, Zp)

local Complex, Conjugate, Abs =
  Symbols('Complex Conjugate Abs', guacyra)

local I = Complex(0, 1)
guacyra.I = I
Rule(Numeric(Complex(_{a=_},_{b=_})),
function(a, b)
  return Bool(isNumeric(a) and isNumeric(b))
end, Complex)
Rule(Complex(_{a=_}, 0), 
function(a)
  return a
end)
Rule(Conjugate(Complex(_{a=_}, _{b=_})), 
function(a, b)
  return Complex(a, -b)
end)
Rule(Abs(Complex(_{a=_}, _{b=_})), 
function(a, b)
  return Sqrt(a^2+b^2)
end)
Rule(Plus(Complex(_{a=_}, _{b=_}),
          Complex(_{c=_}, _{d=_})),
function(a, b, c, d)
  return Complex(a+c, b+d) 
end, Complex)
Rule(Plus(_{a=NumericQ},
          Complex(_{c=_}, _{d=_})),
function(a, c, d)
  return Complex(a+c, d) 
end, Complex)
Rule(Times(Complex(_{a=_}, _{b=_}),
           Complex(_{c=_}, _{d=_})),
function(a, b, c, d)
  return Complex(a*c-b*d, a*d+b*c) 
end, Complex)
Rule(Times(_{a=NumericQ},
          Complex(_{c=_}, _{d=_})),
function(a, c, d)
  return Complex(a*c, a*d) 
end, Complex)
Rule(Power(_{z=Complex}, _{n=Int}),
function(z, n)
  local r = Int(1)
  for i=1,math.abs(n[1]) do
    r = r*z
  end
  if n[1]<0 then
    return Conjugate(r)/Power(Abs(r), 2)
  end
  return r
end, Complex)
Rule(TeX(Complex(_{a=_},_{b=_})),
function(a, b)
  local i = Symbols('\\mathrm{i}')
  local b = TeX(b*i)
  if a:eq(0) then
    return b
  end
  if b[1]:sub(1,1)=='-' then
    return Cat(TeX(a),b)
  else
    return Cat(TeX(a),'+',b)
  end 
end, Complex)

local Matrix, Dot, Det, RREF, Rank = 
  Symbols('Matrix Dot Det RREF Rank', guacyra)
guacyra.__concat = Dot

Rule(Matrix(_{m=Int}, _{n=Int}, _{f=Fun}),
function(m, n, f)
  local rs = cat(Matrix)
  for i=1,m[1] do
    local r = cat(List)
    for j=1,n[1] do
      r[j] = f(i, j)
    end
    rs[i] = r
  end
  return rs
end)
local function dims(m) 
  return #m, #m[1]
end
Rule(Times(_{a=_}, _{A=Matrix}),
function(a, A)
  local B = Matrix()
  local m, n = dims(A)
  for i=1,m do
    local l = List()
    for j=1,n do
      l[#l+1] = a*A[i][j]
    end
    B[#B+1] = l
  end
  return B
end, Matrix)
Rule(Plus(_{A=Matrix}, _{B=Matrix}),
function(A, B)
  local C = Matrix()
  local m, n = dims(A)
  for i=1,m do
    local l = List()
    for j=1,n do
      l[#l+1] = A[i][j]+B[i][j]
    end
    C[#C+1] = l
  end
  return C
end, Matrix)
Rule(TeX(Matrix(__{rs=_})),
function(rs)
  local t = ''
  local n = #rs[1]
  for i=1,#rs do
    local r = rs[i]
    for j=1,#r do
      if j>1 then t = t..' & ' end 
      t = t..(TeX(r[j])[1])
    end
    t = t..' \\\\'
  end
  local fmt = '{'..string.rep('r', n)..'}'
  return Cat('\\left[\\begin{array}', fmt,
    Str(t),
    '\\end{array}\\right]')
end, Matrix)

Rule(RandInt({_{a=Int}, _{b=Int}},
  _{m=Int}, _{n=Int}),
function(a, b, m, n)
  local r = cat(Matrix)
  for i=1,m[1] do
    local l = cat(List)
    for j=1,n[1] do
      l[#l+1] = Int(random(a[1], b[1]))
    end
    r[#r+1] = l
  end
  return r
end)

function dot(A, B)
  local m, n = dims(A)
  local n2, p = dims(B)
  if n~=n2 then
    error('Wrong dimensions.')
  end
  local rs = cat(Matrix)
  for i=1,m do 
    local r = cat(List)
    for j=1,p do
      local c = cat(List)
      for k=1,n do
        c[#c+1] = A[i][k]*B[k][j]
      end
      r[#r+1] = Apply(Plus, c)
    end
    rs[#rs+1] = r
  end
  return rs 
end

Dot.flat = true
Rule(Dot(_{A=Matrix}, _{B=Matrix}), dot)
Rule(Dot(__{As=Matrix}),
function(As)
  return Reduce(Dot, List(As))
end)

local function diagonal(A) 
  local r = cat(List)
  local m, n = dims(A)
  if m~=n then
    error('Not a square matrix')
  end
  for i=1,n do
    r[#r+1] = A[i][i]
  end
  return r 
end

local function bird(A, X) 
  local m, n = dims(A)
  local d = diagonal(X)
  for i=1,m do for j=1,n do
    if j<i then
      X[i][j] = Int(0)
    end
  end end
  local nd = List(0)
  for i=n-1,1,-1 do
    nd[#nd+1] = Plus(d[i+1], nd[#nd])
  end
  for i=1,n do
    X[i][i] = Times(-1,nd[n-i+1])
  end
  return dot(X,A)
end

local function det(A) 
  local m, n = dims(A)
  if m~=n then 
    error('Not a square matrix.')
  end
  if n==2 then
    return (A[1][1]*A[2][2]-A[1][2]*A[2][1])
  elseif n==3 then
    return (A[1][1]*A[2][2]*A[3][3]+
      A[1][2]*A[2][3]*A[3][1]+
      A[1][3]*A[2][1]*A[3][2]-
      A[1][3]*A[2][2]*A[3][1]-
      A[1][2]*A[2][1]*A[3][3]-
      A[1][1]*A[2][3]*A[3][2])
  elseif n==4 then
    return (
    A[1][1]*A[2][2]*A[3][3]*A[4][4]+
    A[1][1]*A[2][3]*A[3][4]*A[4][2]+
    A[1][1]*A[2][4]*A[3][2]*A[4][3]+
    A[1][2]*A[2][1]*A[3][4]*A[4][3]+
    A[1][2]*A[2][3]*A[3][1]*A[4][4]+
    A[1][2]*A[2][4]*A[3][3]*A[4][1]+
    A[1][3]*A[2][1]*A[3][2]*A[4][4]+
    A[1][3]*A[2][2]*A[3][4]*A[4][1]+
    A[1][3]*A[2][4]*A[3][1]*A[4][2]+
    A[1][4]*A[2][1]*A[3][3]*A[4][2]+
    A[1][4]*A[2][2]*A[3][1]*A[4][3]+
    A[1][4]*A[2][3]*A[3][2]*A[4][1]-
    A[1][1]*A[2][2]*A[3][4]*A[4][3]-
    A[1][1]*A[2][3]*A[3][2]*A[4][4]-
    A[1][1]*A[2][4]*A[3][3]*A[4][2]-
    A[1][2]*A[2][1]*A[3][3]*A[4][4]-
    A[1][2]*A[2][3]*A[3][4]*A[4][1]-
    A[1][2]*A[2][4]*A[3][1]*A[4][3]-
    A[1][3]*A[2][1]*A[3][4]*A[4][2]-
    A[1][3]*A[2][2]*A[3][1]*A[4][4]-
    A[1][3]*A[2][4]*A[3][2]*A[4][1]-
    A[1][4]*A[2][1]*A[3][2]*A[4][3]-
    A[1][4]*A[2][2]*A[3][3]*A[4][1]-
    A[1][4]*A[2][3]*A[3][1]*A[4][2])
  end
  local X = copy(A)
  for i=1,n-1 do X = bird(A, X) end
  if n%2 == 0 then
    return Times(-1, X[1][1])
  end
  return X[1][1]
end

Rule(Det(_{A=Matrix}), det)

local function rref(A)
  local m, n = dims(A)
  local ii = 1
  for j=1,n do
    local i = ii
    while i<=m and equal(A[i][j], Int(0)) do
      i = i+1
    end
    if i <= m then
      if not Numeric(A[i][j]):test() then
        return
      end
      if i ~= ii then
        A[i], A[ii] = A[ii], A[i]
      end
      local k = (1/A[ii][j])
      if not equal(k, Int(1)) then
        A[ii][j] = Int(1)
        for jj = j+1,n do
          A[ii][jj] = k*A[ii][jj]
        end
      end
      for i=ii-1,1,-1 do
        local k = Times(-1, A[i][j]/A[ii][j])
        if not equal(k, Int(0)) then
          A[i][j] = Int(0)
          for jj=j+1,n do 
            A[i][jj] = Expand(A[i][jj]+k*A[ii][jj])
          end
        end
      end
      for i=ii+1,m do
        local k = Times(-1, A[i][j]/A[ii][j])
        if not equal(k, Int(0)) then
          A[i][j] = Int(0)
          for jj=j+1,n do 
            A[i][jj] = Expand(A[i][jj]+k*A[ii][jj])
          end
        end
      end
      if ii == m then
        ii = m+1
        break
      end
      ii = ii + 1
    end
  end
  return ii-1
end

Rule(RREF(_{A=Matrix}),
function(A)
  local B = copy(A)
  rref(B)
  return B
end)

Rule(Rank(_{A=Matrix}),
function(A)
  local B = copy(A)
  return Int(rref(B))
end)

local SubMatrix, Tuple, Transpose, BlockMatrix = 
  Symbols('SubMatrix Tuple Transpose BlockMatrix', guacyra)

Rule(SubMatrix(_{a=Matrix},
  List(_{i1=Int},_{i2=Int}),
  List(_{j1=Int},_{j2=Int})),
function (a, i1, i2, j1, j2)
  local r = Matrix()
  for i=i1[1],i2[1] do
    local l = List()
    for j=j1[1],j2[1] do
      l[#l+1] = a[i][j]
    end
    r[#r+1] = l
  end
  return r
end)

Rule(SubMatrix(_{a=Matrix},
  List(_{i1=Int},_{i2=Int}),
  _{j1=Int}),
function (a, i1, i2, j1)
  return SubMatrix(a,{i1,i2},{j1,j1})
end)

Rule(SubMatrix(_{a=Matrix},
  _{i1=Int},
  List(_{j1=Int},_{j2=Int})),
function (a, i1, j1, j2)
  return SubMatrix(a,{i1,i1},{j1,j2})
end)

Rule(Tuple(_{a=Matrix}),
function (a)
  local m, n = dims(a)
  local l = Tuple()
  for i=1,m do
    for j=1,n do
      l[#l+1] = a[i][j]
    end
  end
  return l
end)

Rule(TeX(Tuple(__{a=_})),
function(a)
  local s='('
  for i=1,#a do
    if i~=1 then
      s = s..','
    end
    s = s..(TeX(a[i])[1])
  end
  s = s..')'
  return Str(s)
end
,Tuple)

Rule(Transpose(_{a=Matrix}),
function (a)
  local m, n = dims(a)
  local r = Matrix()
  for j=1,n do
    local l = List()
    for i=1,m do
      l[#l+1] = a[i][j]
    end
    r[#r+1] = l
  end
  return r
end)

Rule(BlockMatrix(__{a=List}),
function (a)
  local mb, nb = dims(a)
  local r = Matrix()
  local ir = 1
  for ib=1,mb do
    local m = #a[ib][1]
    for i = 1,m do 
      local l = List()
      for jb=1,nb do
        local mm, n = dims(a[ib][jb])
        for j=1,n do
          l[#l+1] = a[ib][jb][i][j]
        end
      end
      r[#r+1] = l
    end
  end
  return r
end)

guacyra.import = function()
  for k,v in pairs(guacyra) do
    if isObject(v) then
      _G[k] = v
    end 
  end
  _G['Symbols'] = Symbols
  _G['Rule'] = Rule
end

return guacyra