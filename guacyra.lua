
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
local String = makeAtom('String')
local Boolean = makeAtom('Boolean')
local Function = makeAtom('Function')

local List, _, __, ___
guacyra.Symbol = Symbol
guacyra.Int = Int
guacyra.Rat = Rat
guacyra.String = String
guacyra.Boolean = Boolean
guacyra.Function = Function

-- lua 5.3 workaround
local unpack = unpack or table.unpack

local function isObject(e)
  return getmetatable(e) == guacyra
end

local function isAtomHead(e)
  return e == Symbol or e == Int or
    e == Rat or e == String or
    e == Boolean or e == Function
end

local function isAtom(e)
  local h = e[0]
  return h == Symbol or h == Int or
    h == Rat or h == String or
    h == Boolean or h == Function
end
guacyra.isAtom = isAtom

local function isSymbol(e)
  return e[0] == Symbol
end
guacyra.isSymbol = isSymbol

local function isFunction(e)
  return e[0] == Function
end
guacyra.isFunction = isFunction

local ruleCount = 0

local function maxDef(e)
  local function maxDefR(e, s)
    if isSymbol(e) then
      return math.max(e.def, s)
    elseif isAtom(e) then
      return -1
    else
      local r = -1
      for i=0,#e do
        r = math.max(maxDefR(e[i], r), r)
      end
      return r
    end
  end
  return maxDefR(e, -1)
end
guacyra.maxDef = maxDef

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
      a = String(a)
    elseif type(a) == 'boolean' then
      a = Boolean(a) 
    elseif type(a) == 'table' then
      a = makeExp(List, unpack(a))
    elseif type(a) == 'function' then
      a = Function(a)
    end
  end
  return a
end

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
    t.def = -1
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
  end
  if (h==_ or h==__ or h==___)
    and type(t[1])=='table' and not isObject(t[1]) then
    local key = ''
    local type = _
    for k,v in pairs(t[1]) do
      if isSymbol(v) or isFunction(v) then
        key = k
        type = v
      end
    end
    t[1]=String(key)
    if type ~= _ then
      t[2] = type
    end
    return t
  end
  if not isAtomHead(h) then
    for i = 1, #t do
      t[i] = conv(t[i])
    end
  end
  return t
end
guacyra.__call = makeExp
List = Symbol('List')
guacyra.List = List
_ = Symbol('_')
guacyra._ = _
__ = Symbol('__')
guacyra.__ = __
___ = Symbol('___')
guacyra.___ = ___
local Sequence = Symbol('Sequence')
guacyra.Sequence = Sequence
local Error = Symbol('Error')
guacyra.Error = Error
local Null = Symbol('Null')
guacyra.Null = Null
Blank = Symbol('Blank')
local True = Boolean(true)
guacyra.True = True
local False = Boolean(false)
guacyra.False = False
local function test(v) 
  if isObject(v) and v[0]==Boolean then
    return v[1]
  end
  return v
end
guacyra.test = test

local Indeterminate = Symbol("Indeterminate")
guacyra.Indeterminate = Indeterminate

tostr = function(e)
  if not isObject(e) then return tostring(e) end
  if isAtom(e) then
    if e[0] == Symbol then return e[1] end
    if e[0] == String then return e[1] end
    if e[0] == Int then return '' .. e[1] end
    if e[0] == Rat then return '' .. e[1] .. '/' .. e[2] end
    if e[0] == Boolean then
      if e[1] then
        return 'True'
      else
        return 'False'
      end
    end
    if e[0] == Function then
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
    s, cs = '{', '}'
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
guacyra.__eq = equal

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

local Plus = Symbol('Plus')
guacyra.Plus = Plus
local Times = Symbol('Times')
guacyra.Times = Times
local Power = Symbol('Power')
guacyra.Power = Power

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

-- Joel S. Cohen, Computer Algebra and Symbolic Computation: Mathematical Methods
local function less(u, v)
  -- O1
  if isNumeric(u) and isNumeric(v) then
    return numericValue(u) < numericValue(v)
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
    return less(u, Times(v))
  elseif v[0] == Times then
    return less(Times(u), v)
  end
  -- O9
  if u[0] == Power then
    return less(u, Power(v, 1))
  elseif v[0] == Power then
    return less(Power(u, 1), v)
  end
  -- O10
  if u[0] == Plus then
    return less(u, Plus(v))
  elseif v[0] == Plus then
    return less(Plus(u), v)
  end
  -- O12
  if isSymbol(v) and equal(u[0], v) then
    return false
  elseif isSymbol(u) and equal(u, v[0]) then
    return true
  end
  if u[0] == String and v[0] == String then
    return u[1] < v[1]
  end
  -- Catch all
  return tostring(u) < tostring(v)
end

guacyra.less = less
guacyra.__lt = less

guacyra.__le = function(a, b)
  return less(a, b) or equal(a, b)
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
      if isFunction(head) and not test(head[1](ex)) then
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
      local exr = Sequence()
      for j = i, #ex do
        exr[#exr + 1] = ex[j]
        if head ~= nil then
          if isFunction(head) and not test(head[1](ex[j])) then
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

local function flatten(e)
  if isAtom(e) then return e end
  for i=1,#e do
    e[i] = flatten(e[i])
  end
  local head = e[0]
  if isSymbol(head) and head.flat then
    local i = 1
    while i <= #e do
      if equal(e[i][0], head) then
        local ei = table.remove(e, i)
        for j = 1, #ei do
          table.insert(e, i + j - 1, ei[j])
        end
        i = i + #ei
      else
        i = i + 1
      end
    end
  end
  return e
end

local function sort(e)
  if isAtom(e) then return e end
  for i=1,#e do
    e[i] = sort(e[i])
  end
  local head = e[0]
  if isSymbol(head) and head.orderless then
    table.sort(e, less)
  end
  return e
end

local eval

local function evalR(e)
  local head = eval(e[0])
  local ex = head()
  if head[0] == Function then
    for i = 1, #e do ex[i] = eval(e[i]) end
    return eval(head[1](unpack(ex)))
  end
  local lh = lhead(head)
  if lh.holdAll then
    for i = 1, #e do ex[i] = e[i] end
  else
    for i = 1, #e do
      if lh.holdFirst and i == 1 then
        ex[i] = e[i]
      else
        ex[i] = eval(e[i])
      end
    end
  end
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
        if tex then return eval(tex) end
      end
    end
  end
  if lh.down then
    for j = 1, #lh.down do
      tex = lh.down[j](ex)
      if tex then return eval(tex) end
    end
  end
  return ex
end

--local cache = {}

eval = function(e)
  if isAtom(e) then
    return e
  else
    return evalR(e)
    --[[local d = maxDef(e)
    local st = tostr(e)
    local ch = cache[st]
    if ch and ch.def == d and d~= math.huge then 
      return ch.value 
    end
    local le = evalR(e)
    ch = {}
    ch.def = d
    ch.value = le
    cache[st] = ch
    if not isAtom(le) then
      local ch = {}
      ch.def = maxDef(le)
      ch.value = le
      cache[tostr(le)] = ch
    end
    return le]]
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
  ruleCount = ruleCount + 1
  sym.def = math.max(ruleCount, sym.def)
  --print('Def: ',sym, sym.def)
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

local Equal, Less = 
  Symbols('Equal Less', guacyra)
Rule(Equal(_{a=_}, _{b=_}),
function(a, b) return Boolean(equal(a, b)) end)
Rule(Less(_{a=_}, _{b=_}),
function(a, b) return Boolean(less(a, b)) end)

local function apply(a, b)
  setmetatable(b, guacyra)
  b[0] = a
  return b
end
local function map(a, b)
  local r = {}
  for i = 1, #b do
    r[#r+1] = a(b[i]) end
  return r
end
local function reduce(a, b)
  local r = b[1]
  for i = 2, #b do
    r = a(r, b[i])
  end
  return r
end
local function reduce1(a, b, c)
  local r = c
  for i = 1, #b do
    r = a(r, b[i])
  end
  return r
end
local function groupWith(a, b, g)
  local r = {}
  r = reduce1(
  function(s, c)
    if #s==0 then
      s[1] = {c}
    else 
      local last = s[#s]
      if b(c, last[1]) then
        last[#last+1] = c
      else
        s[#s+1] = {c}
      end 
    end
    return s
  end, a, r)
  if g then 
    return map(g, r)
  else 
    return r
  end
end

local Map, Apply, First, Rest, Fold, Reduce, GroupWith = 
  Symbols('Map Apply First Rest Fold Reduce GroupWith', guacyra)


Rule(Map(_{a=_}, _{b=_}),
function(a, b)
  return  apply(b[0], map(a, b))
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
    t = a(t, c[i]):eval() end
  return t
end)
Rule(Reduce(_{a=_}, _{b=List}),
function(a, b)
  return reduce(
    function(p, q) return a(p, q):eval() end, b)
end)
Rule(Reduce(_{a=_}, _{b=List}, _{c=_}),
function(a, b, c)
  return reduce1(
    function(p, q) return a(p, q):eval() end, b, c)
end)
Rule(GroupWith(_{a=_}, _{b=_}),
function(a, b)
  local r = groupWith(a,
    function(p, q) return test(b(p, q):eval()) end,
    function(s) return apply(List, s) end)
  return apply(List, s)
end)

local Cat, Range, RandomInt = 
  Symbols('Cat Range RandomInt', guacyra)
RandomInt.def = math.huge

Rule(Cat(___{c=_}),
function(c)
  local t = ""
  for i = 1, #c do
    if isAtom(c[i]) and c[i][0] == String then
      t = t .. (c[i][1])
    else
      t = t .. (c[i]:tostring())
    end
  end
  return String(t)
end)
Rule(Range(_{a=Int}, _{b=Int}),
function(a, b)
  local t = List()
  for i = a[1], b[1] do
    t[#t+1] = Int(i) end
  return t
end)
Rule(RandomInt({_{a=Int}, _{b=Int}}),
function(a, b)
  return Int(random(a[1], b[1]))
end)
Rule(RandomInt({_{a=Int}, _{b=Int}},
  _{n=Int}),
function(a, b, n)
  local t = List()
  for i = 1, n[1] do
    t[#t+1] = Int(random(a[1], b[1]))
  end
  return t
end)

guacyra.__add = function(a, b) return Plus(a, b) end
guacyra.__sub = function(a, b) return Plus(a, Times(-1, b)) end
guacyra.__unm = function(a) return Times(-1, a) end
guacyra.__mul = function(a, b) return Times(a, b) end
guacyra.__div = function(a, b) return Times(a, Power(b, -1)) end
guacyra.__pow = function(a, b) return Power(a, b) end

local NumericQ = Function(
function(ex)
  return Boolean(isNumeric(ex))
end)
guacyra.NumericQ = NumericQ

Plus.flat = true
Plus.orderless = true
Rule(Plus(),
function() return Int(0) end)
Rule(Plus(_{a=_}),
function(a) return a end)
local function nplus(a, b)
  if a[0]==Int then
    if b[0]==Int then
      return Int(a[1]+b[1])
    else
      return Rat(a[1]*b[2]+b[1], b[2])
    end
  else
    if b[0]==Int then
      return Rat(b[1]*a[2]+a[1], a[2])
    else
      return Rat(a[1]*b[2]+b[1]*a[2], a[2]*b[2])
    end
  end
end 
local function ntimes(a, b)
  if a[0]==Int then
    if b[0]==Int then
      return Int(a[1]*b[1])
    else
      return Rat(a[1]*b[1], b[2])
    end
  else
    if b[0]==Int then
      return Rat(b[1]*a[1], a[2])
    else
      return Rat(a[1]*b[1], a[2]*b[2])
    end
  end
end 

Times.flat = true
Times.orderless = true
Rule(Times(),
function() return Int(1) end)
Rule(Times(_{a=_}),
function(a) return a end)
Rule(Times(1, __{b=_}),
function(b) return Times(b) end)
Rule(Times(0, __{b=_}),
function(b) return Int(0) end)
Rule(Times(-1, Plus(__{a=_})),
function(a)
  return apply(Plus, 
    map(function(t) return Times(-1, t) end, a))
end)

Rule(Plus(__{a=_}),
function(a)
  local n = Int(0)
  local snum = 0
  local nnum = List()
  for i=1,#a do
    local t = a[i]
    if isNumeric(t) then
      n = nplus(n, t)
      snum = snum+1
    else
      if t[0]==Times then
        if not isNumeric(t[1]) then
          t = copy(t)
          table.insert(t, 1, Int(1))
        end
      else
        t = Times(1, t)
      end
      nnum[#nnum+1] = t
    end
  end
  local size = #nnum
  if size == 0 then
    return n
  end
  nnum = groupWith(nnum, function(a, b) 
    local cap, cap2 = {}, {}
    a:match(Times(_{co=_}, __{te=_}), cap)
    b:match(Times(_{co=_}, __{te=_}), cap2)
    return equal(cap.te, cap2.te)
    end)
  if #nnum == size and snum <= 1 then return nil end
  local num
  if equal(n, Int(0)) then
    num = Plus()
  else
    num = Plus(n)
  end
  nnum = reduce1(function(s, c)
    local ret = copy(c[1])
    c = map(function(t)
      return t[1]
    end, c)
    local co = reduce(nplus, c)
    ret[1] = co
    if not equal(co, Int(0)) then
      s[#s+1] = ret
    end
    return s
  end, nnum, num)
  return nnum
end)

Rule(Times(__{a=_}),
function(a)
  local n = Int(1)
  local snum = 0
  local nnum = List()
  for i=1,#a do
    local t = a[i]
    if isNumeric(t) then
      n = ntimes(n, t)
      snum = snum+1
    else
      if t[0]~=Power then
        t = Power(t, 1)
      end
      nnum[#nnum+1] = t
    end
  end
  local size = #nnum
  if size == 0 or equal(n, Int(0)) then
    return n
  end
  nnum = groupWith(nnum, function(a, b) 
    local cap, cap2 = {}, {}
    a:match(Power(_{ba=_}, _{ex=_}), cap)
    b:match(Power(_{ba=_}, _{ex=_}), cap2)
    return equal(cap.ba, cap2.ba)
    end)
  if #nnum == size and snum <= 1 then return nil end
  local num
  if equal(n, Int(1)) then
    num = Times()
  else
    num = Times(n)
  end
  nnum = reduce1(function(s, c)
    local ret = copy(c[1])
    c = map(function(t)
      return t[2]
    end, c)
    local co = reduce(nplus, c)
    ret[2] = co
    if not equal(co, Int(0)) then
      if equal(co, Int(1)) then
        s[#s+1] = ret[1]
      else
        s[#s+1] = ret
      end
    end
    return s
  end, nnum, num)
  return nnum
end)

Rule(Times(__{a=_}),
function(a)
  local n = Int(1)
  local snum = 0
  local nnum = List()
  for i=1,#a do
    local t = a[i]
    if isNumeric(t) then
      n = ntimes(n, t)
      snum = snum+1
    else
      if t[0]~=Power then
        t = Power(t, 1)
      end
      nnum[#nnum+1] = t
    end
  end
  local size = #nnum
  if size == 0 or equal(n, Int(0)) then
    return n
  end
  nnum = groupWith(nnum, function(a, b) 
    local cap, cap2 = {}, {}
    local aq = a:match(Power(_{ba=Int}, _{ex=NumericQ}), cap)
    local bq = b:match(Power(_{ba=Int}, _{ex=NumericQ}), cap2)
    return aq and bq and equal(cap.ex, cap2.ex)
    end)
  if #nnum == size and snum <= 1 then return nil end
  local num
  if equal(n, Int(1)) then
    num = Times()
  else
    num = Times(n)
  end
  nnum = reduce1(function(s, c)
    if #c == 1 then
      s[#s+1] = c[1][1]
      return s
    end
    local ret = copy(c[1])
    c = map(function(t)
      return t[1]
    end, c)
    local co = reduce(ntimes, c)
    ret[1] = co
    s[#s+1] = ret
    return s
  end, nnum, num)
  return nnum
end)

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
  return apply(Times, 
    map(function(t) return Power(t, b) end, a))
end)

local Sqrt, Expand = 
  Symbols('Sqrt Expand', guacyra)
Rule(Sqrt(_{a=_}),
function(a) return a^Rat(1,2) end)

Rule(Expand(Times(__{a=_})),
function(a)
  local aa = a
  for j = 1, #aa do
    local cap = {}
    if aa[j]:match(Plus(__{b=_}), cap) then
      local r = Plus()
      for k = 1, #cap.b do
        local t = aa:copy()
        t[j] = cap.b[k]
        r[#r + 1] = Expand(Times(t))
      end
      return r
    elseif aa[j]:match(Power(Plus(__{b=_}), _{n=Int}), cap)
      and cap.n[1] > 0 then
      local t = aa:copy()
      t[0] = Times
      t[j] = Expand(Power(Plus(cap.b), cap.n[1]))
      return Expand(t)
    end
  end
  return Times(a)
end)
Rule(Expand(Power(Plus(_{a=_}, __{b=_}), _{n=Int})),
function(a, b, n)
  local r = Plus()
  for i = 0, n[1] do
    r[#r+1] = Expand(
      Times(binomial(n[1], i), Power(a, n[1] - i),
      Expand(Power(Plus(b), i))))
  end
  return r
end)
Rule(Expand(Plus(_{a=_}, __{b=_})), function(a, b)
  return Plus(Expand(a), Expand(Plus(b)))
end)
Rule(Expand(_{a=List}),
function(a)
  return Map(Expand, a)
end)
Rule(Expand(_{a=_}),
function(a) return a end)

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
  local e = Map(NumeratorDenominator,List(a)):eval()
  local num = Times()
  local den = Times()
  for i=1,#e do
    num[#num+1] = e[i][1]
    den[#den+1] = e[i][2]
  end
  return List(num,den)
end)
Rule(NumeratorDenominator(Plus(__{a=_})),
function(a)
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
end)
Rule(NumeratorDenominator(_{a=_}),
function(a)
  return List(a, 1)
end)
Rule(Numerator(_{a=_}),
function(a)
  local nd = NumeratorDenominator(a):eval()
  return nd[1]
end)
Rule(Denominator(_{a=_}),
function(a)
  local nd = NumeratorDenominator(a):eval()
  return nd[2]
end)
Rule(Together(_{a=_}),
function(a)
  local l = NumeratorDenominator(a):eval()
  if l[2][0]==Int then
    return l[1]/l[2]
  else
    return Together(l[1])/Together(l[2])
  end
end)

local function lessMath(u, v)
  if isNumeric(u) and isNumeric(v) then
    return numericValue(u) < numericValue(v)
  end
  if isSymbol(u) and isSymbol(v) then
    return u[1] < v[1]
  end
  if (u[0] == Plus and v[0] == Plus)
  or (u[0] == Times and v[0] == Times) then
    local m = #u
    local n = #v
    while m > 0 and n > 0 do
      if equal(u[m], v[n]) then
        m = m - 1
        n = n - 1
      else
        return lessMath(u[m], v[n])
      end
    end
    return m < n
  end
  if u[0] == Power and v[0] == Power then
    if equal(u[2], v[2]) then
      return lessMath(u[1], v[1])
    else
      return lessMath(v[2], u[2]) -- order
    end
  end
  if u[0] == v[0] then
    local m = #u
    local n = #v
    local i = 1
    while i <= m and i <= n do
      if equal(u[i], v[i]) then
        i = i + 1
      else
        return lessMath(u[i], v[i])
      end
    end
    return m < n
  end
  if u[0] == Times then
    return lessMath(u, Times(v))
  elseif v[0] == Times then
    return lessMath(Times(u), v)
  end
  if u[0] == Power then
    return lessMath(u, Power(v, 1))
  elseif v[0] == Power then
    return lessMath(Power(u, 1), v)
  end
  if u[0] == Plus then
    return lessMath(u, Plus(v))
  elseif v[0] == Plus then
    return lessMath(Plus(u), v)
  end
  if isNumeric(u) and not isNumeric(v) then
    return false
  elseif not isNumeric(u) and isNumeric(v) then
    return true
  end
end

local LaTeXP = Symbol("LaTeXP")
local LaTeX = Symbol("LaTeX")
guacyra.LaTeX = LaTeX
Rule(LaTeXP(Plus(__{c=_})),
function(c)
  return Cat('(', LaTeX(Plus(c)), ')')
end)
Rule(LaTeXP(_{a=_}),
function(a) return LaTeX(a) end)
Rule(LaTeX(Times(_{p=Rat}, _{a=Symbol})),
function(p, a)
  if p[1] < 0 then
    local s = (LaTeX(Times(-p[1], a)):eval())[1]
    return String('-\\frac{'..s..'}{'..p[2]..'}')
  else
    local s = (LaTeX(Times(p[1], a)):eval())[1]
    return String('\\frac{'..s..'}{'..p[2]..'}')
  end
end)
Rule(LaTeX(_{p=Rat}),
function(p)
  local a, b = p[1], p[2]
  if a<0 then
    return String('-\\frac{'..(-a)..'}{'..b..'}')
  else
    return String('\\frac{'..(a)..'}{'..b..'}')
  end
end)
Rule(LaTeX(Times(-1,__{a=_})),
function(a) 
  return Cat('-', LaTeXP(Times(a)))
end)
Rule(LaTeX(Times(__{a=_})),
function(a)
  local l = NumeratorDenominator(Times(a)):eval()
  if l[2][0]==Int then
    return Apply(Cat,Map(LaTeXP,List(a)))
  else
    local num = LaTeX(l[1]):eval()
    local den = LaTeX(l[2]):eval()
    return Cat('\\frac{',num,'}{',den,'}')
  end
end)
Rule(LaTeX(Power(_{a=_},_{b=Rat})),
function(a, b)
  if b[1] == 1 then
    if b[2] == 2 then
      return Cat('\\sqrt{', LaTeX(a), '}')
    else
      return Cat('\\sqrt['..b[2]..']{',LaTeX(a),'}')
    end
  else
    return Cat(LaTeXP(a),'^{', LaTeX(b), '}')
  end
end)
Rule(LaTeX(Power(_{a=_}, _{b=Int})),
function(a, b)
  if b[1]<0 then
    return Cat('\\frac{1}{',LaTeX(Power(a,-b[1])),'}')
  else
    b = ''..b[1]
    if #b>1 then
      return Cat(LaTeXP(a), '^{'..b..'}')
    else
      return Cat(LaTeXP(a), '^'..b)
    end
  end
end)
Rule(LaTeX(Power(_{a=Symbol}, _{b=_})),
function(a, b)
  return Cat(a[1] .. '^{', LaTeX(b),'}')
end)
Rule(LaTeX(Power(_{a=_}, _{b=_})),
function(a, b)
    return Cat(LaTeXP(a), '^{', LaTeX(b),'}')
end)
Rule(LaTeX(Plus(__{c=_})),
function(c)
  c = copy(c)
  table.sort(c, lessMath)
  print(c)
  local s = ''
  for i=1,#c do
    local t = LaTeX(c[i]):eval()
    if t[1]:sub(1,1)~='-' and i~=1 then
      s = s..'+'
    end
    s = s..t[1]
  end
  return String(s)
end)
Rule(LaTeX(_{a=_}),
function(a)
  return String(a:tostring())
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
  return Map(function(t) return Diff(t,x) end, Plus(a) )
end)
Rule(Diff(Power(_{f=_}, _{n=NumericQ}), _{x=Symbol}),
function(f, n, x)
  return Times(n, Power(f, n-1), Diff(f, x))
end)
Rule(Diff(_{f=_}(_{y=_}), _{x=Symbol}),
function(f, y, x)
  return Times(Derivative(f)(1)(y), Diff(y, x))
end)
Rule(LaTeX(Pi),
function() return String('\\pi') end, Pi)
Rule(LaTeX(Exp(_{a=_})),
function(a)
  return Cat('e^{', LaTeX(a), '}')
end, Exp)
Rule(LaTeX(Log(_{a=_})),
function(a)
  return Cat('\\log{', LaTeX(a), '}')
end, Log)
Rule(LaTeX(Sin(_{a=_})),
function(a)
  return Cat('\\sin{', LaTeX(a), '}')
end, Sin)
Rule(LaTeX(Cos(_{a=_})),
function(a)
  return Cat('\\cos{', LaTeX(a), '}')
end, Cos)
Rule(LaTeX(Derivative(_{f=_})(1)(_{x=_})),
function(f, x)
  return Cat(LaTeX(f), "{'}(", LaTeX(x),')')
end, Derivative)

local Matrix, Dot, Det, RREF = 
  Symbols('Matrix Dot Det RREF', guacyra)

Rule(Matrix(_{m=Int}, _{n=Int}, _{f=Function}),
function(m, n, f)
  local rs = Matrix()
  for i=1,m[1] do
    local r = List()
    for j=1,n[1] do
      r[j] = f(i, j):eval()
    end
    rs[i] = r
  end
  return rs
end)
Rule(Matrix(_{m=List}),
function(m)
  local rs = Matrix()
  if #m==0 or #m[1]==0 then
    error('Empty list.')
  end
  local n = #m[1]
  for i=1,#m do
    local r = List()
    for j=1,n do
      if #m[i]~=n then
        error('Not a matrix.')
      end
      r[j] = m[i][j]
    end
    rs[i] = r
  end
  return rs
end)
local function dims(m) 
  return #m, #m[1]
end
Rule(LaTeX(Matrix(__{rs=_})),
function(rs)
  local t = ''
  for i=1,#rs do
    local r = rs[i]
    for j=1,#r do
      if j>1 then t = t..' & ' end 
      t = t..(LaTeX(r[j]):eval()[1])
    end
    t = t..' \\\\'
  end
  return Cat('\\left\\[\\begin{matrix}',
    String(t),
    '\\end{matrix}\\right\\]')
end, Matrix)

function dot(A, B)
  local m, n = dims(A)
  local n2, p = dims(B)
  if n~=n2 then
    error('Wrong dimensions.')
  end
  local rs = Matrix()
  for i=1,m do 
    local r = List()
    for j=1,p do
      local c = Plus()
      for k=1,n do
        c[#c+1] = A[i][k]*B[k][j]
      end
      r[#r+1] = c:eval()
    end
    rs[#rs+1] = r
  end
  return rs 
end

Rule(Dot(_{A=Matrix}, _{B=Matrix}), dot)

local function diagonal(A) 
  local r = List()
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
  local nd = List(Int(0))
  for i=n-1,1,-1 do
    nd[#nd+1] = Plus(d[i+1], nd[#nd]):eval()
  end
  for i=1,n do
    X[i][i] = Times(-1,nd[n-i+1]):eval()
  end
  return dot(X,A)
end

local function det(A) 
  local m, n = dims(A)
  if m~=n then 
    error('Not a square matrix.')
  end
  if n==2 then
    return (A[1][1]*A[2][2]-A[1][2]*A[2][1]):eval()
  elseif n==3 then
    return (A[1][1]*A[2][2]*A[3][3]+
      A[1][2]*A[2][3]*A[3][1]+
      A[1][3]*A[2][1]*A[3][2]-
      A[1][3]*A[2][2]*A[3][1]-
      A[1][2]*A[2][1]*A[3][3]-
      A[1][1]*A[2][3]*A[3][2]):eval()
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
    A[1][4]*A[2][3]*A[3][1]*A[4][2]):eval()
  end
  local X = copy(A)
  for i=1,n-1 do X = bird(A, X) end
  if n%2 == 0 then
    return Times(-1, X[1][1]):eval()
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
      if i ~= ii then
        A[i], A[ii] = A[ii], A[i]
      end
      local k = (1/A[ii][j]):eval()
      if not equal(k, Int(1)) then
        A[ii][j] = Int(1)
        for jj = j+1,n do
          A[ii][jj] = k*A[ii][jj]:eval()
        end
      end
      for i=ii-1,1,-1 do
        local k = Times(-1, A[i][j]/A[ii][j]):eval()
        if not equal(k, Int(0)) then
          A[i][j] = Int(0)
          for jj=j+1,n do 
            A[i][jj] = (A[i][jj]+k*A[ii][jj]):eval()
          end
        end
      end
      for i=ii+1,m do
        local k = Times(-1, A[i][j]/A[ii][j]):eval()
        if not equal(k, Int(0)) then
          A[i][j] = Int(0)
          for jj=j+1,n do 
            A[i][jj] = (A[i][jj]+k*A[ii][jj]):eval()
          end
        end
      end
      if ii == m then break end
      ii = ii + 1
    end
  end
end

Rule(RREF(_{A=Matrix}),
function(A)
  local B = copy(A)
  rref(B)
  return B
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