-- Enumeration
local function weak_compositions(m, n)
  local first = true
  local it = function(v, i)
    if first then
      first = false
      return v
    end
    if n == 0 or v[n] == m then return nil end
    local r
    for k = n - 1, 1, -1 do
      r = k
      if v[r] ~= 0 then break end
    end
    v[r] = v[r] - 1;
    for j = r + 1, n do v[j] = 0 end
    v[r + 1] = m
    for j = 1, r do v[r + 1] = v[r + 1] - v[j] end
    return v
  end
  local ini = {}
  for i = 1, n do ini[i] = 0 end
  if n > 0 then ini[1] = m end
  return it, ini, ini
end

local function permutations(n)
  local first = true
  local it = function(v, k)
    if first then
      first = false
      return v
    end
    local i = n
    while i > 1 and v[i - 1] >= v[i] do i = i - 1 end
    if (i == 1) then return nil end
    local j = n
    while v[j] <= v[i - 1] do j = j - 1 end
    v[i - 1], v[j] = v[j], v[i - 1]
    j = n
    while i < j do
      v[i], v[j] = v[j], v[i]
      i = i + 1
      j = j - 1
    end
    return v
  end
  local ini = {}
  for i = 1, n do ini[i] = i end
  return it, ini, ini
end

-- Number Theory
local floor, infinite, random = math.floor, math.huge, math.random
local abs = math.abs

local function gcd(a, b)
  while b ~= 0 do a, b = b, a % b end
  return abs(a)
end

local function isInteger(a) return type(a) == 'number' and a == floor(a) end

local function binomial(n, k)
  if k > n then return nil end
  if k > n / 2 then k = n - k end
  numer, denom = 1, 1
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

local Number = makeAtom('Number')
local Rational = makeAtom('Rational')
local String = makeAtom('String')
local Boolean = makeAtom('Boolean')
local Function = makeAtom('Function')

local function isObject(e) return getmetatable(e) == guacyra end

local function isAtomHead(e)
  return e == Symbol or e == Number or e == Rational or e == String or e ==
           Boolean or e == Function
end

local function isAtom(e) return isObject(e) and isAtomHead(e[0]) end
guacyra.isAtom = isAtom

local function isSymbol(e) return isObject(e) and e[0] == Symbol end
guacyra.isSymbol = isSymbol

local function isBlankSymbol(e) return isSymbol(e) and e[1]:sub(-1) == '_' end

local function isFunction(e) return isObject(e) and e[0] == Function end
guacyra.isFunction = isFunction

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

local function makeExp(h, ...)
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
  local function blankType(b, h)
    local bl = b
    local bls = bl[1]
    if bls:sub(-3) == '___' then
      return BlankNullSequence(String(bls:sub(1, -4)), h)
    elseif bls:sub(-2) == '__' then
      return BlankSequence(String(bls:sub(1, -3)), h)
    else
      return Blank(String(bls:sub(1, -2)), h)
    end
  end
  if #t == 1 and isBlankSymbol(h) and
    ((isSymbol(t[1]) and not isBlankSymbol(t[1])) or isFunction(t[1]) or type(t[1])=='function') then
      return blankType(h, t[1])
    end
  if isBlankSymbol(h) then
    h = blankType(h)
    t[0] = h
  end
  if h == Rational then
    if not isInteger(t[1]) or not isInteger(t[2]) then
      error('Ill-formed Rational')
    end
    local d = gcd(t[1], t[2])
    t[1] = floor(t[1] / d) -- lua 5.3
    t[2] = floor(t[2] / d)
    if t[2] < 0 then
      t[2] = -t[2]
      t[1] = -t[1]
    end
    if t[2] == 1 then
      t[0] = Number
      t[2] = nil
    end
  end
  if not isAtomHead(h) then
    for i = 1, #t do
      local a = t[i]
      if isBlankSymbol(a) then
        t[i] = blankType(a)
      elseif getmetatable(a) ~= guacyra then
        if type(a) == 'number' then
          t[i] = Number(a)
        elseif type(a) == 'string' then
          t[i] = String(a)
        elseif type(a) == 'table' then
          t[i] = makeExp(List, unpack(a))
        elseif type(a) == 'function' then
          t[i] = Function(a)
        elseif type(a) == 'boolean' then
          t[i] = Boolean(a)
        end
      end
    end
  else
    -- TODO typecheck
    for i = 1, #t do
      if isObject(t[i]) then
        print(t[i])
        error('Ill-formed atom: ' .. tostr(h) .. '(...,' .. tostr(t[i]) ..
                ',...)')
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
local True = Boolean(true)
guacyra.True = True
local False = Boolean(false)
guacyra.False = False
local Undefined = Symbol("Undefined")
guacyra.Undefined = Undefined

tostr = function(e)
  if not isObject(e) then return tostring(e) end
  if isAtom(e) then
    if e[0] == Symbol then return e[1] end
    if e[0] == String then return '"' .. e[1] .. '"' end
    if e[0] == Number then return '' .. e[1] end
    if e[0] == Rational then return '' .. e[1] .. '/' .. e[2] end
    if e[0] == Boolean then
      if e[1] then
        return 'True'
      else
        return 'False'
      end
    end
    if e[0] == Function then return tostring(e[1]) end
  end
  if e[0] == Blank then
    if e[2] then
      return e[1][1] .. '_' .. tostr(e[2])
    else
      return e[1][1] .. '_'
    end
  end
  if e[0] == BlankSequence then
    if e[2] then
      return e[1][1] .. '__' .. tostr(e[2])
    else
      return e[1][1] .. '__'
    end
  end
  if e[0] == BlankNullSequence then
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

local function equal(ea, eb)
  local sa = #ea
  local sb = #eb
  if sa ~= sb then return false end
  if isAtom(ea) and isAtom(eb) then
    for i = 0, #ea do if ea[i] ~= eb[i] then return false end end
    return true
  end
  if not isAtom(ea) and not isAtom(eb) then
    for i = 0, #ea do if not equal(ea[i], eb[i]) then return false end end
    return true
  end
  return false
end
guacyra.equal = equal

local function length(ex)
  if isAtom(ex) then return 1 end
  local s = 0
  for i = 1, #ex do s = s + length(ex[i]) end
  return s
end
guacyra.length = length

local atomOrder = {
  [Number] = 1,
  [Rational] = 2,
  [String] = 3,
  [Symbol] = 4,
  [Boolean] = 5,
  [Function] = 6
}

local Plus = Symbol('Plus')
guacyra.Plus = Plus
local Times = Symbol('Times')
guacyra.Times = Times
local Power = Symbol('Power')
guacyra.Power = Power

local function isNumeric(e)
  return e[0] == Number or e[0] == Rational
end

local function numericValue(e)
  if e[0] == Number then 
    return e[1]
  elseif e[0] == Rational then
    return e[1] / e[2]
  end
end

-- Joel S. Cohen, Computer Algebra and Symbolic Computation: Mathematical Methods 
local function comp(u, v)
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
        return comp(u[m], v[n])
      end
    end
    return m < n
  end
  -- O4
  if u[0] == Power and v[0] == Power then
    if equal(u[1], v[1]) then
      return comp(u[2], v[2])
    else
      return comp(u[1], v[1])
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
        return comp(u[i], v[i])
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
    return comp(u, Times(v))
  elseif v[0] == Times then
    return comp(Times(u), v)
  end
  -- O9
  if u[0] == Power then 
    return comp(u, Power(v, 1))
  elseif v[0] == Power then
    return comp(Power(u, 1), v)
  end
  -- O10
  if u[0] == Plus then 
    return comp(u, Plus(v))
  elseif v[0] == Plus then
    return comp(Plus(u), v)
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

guacyra.less = comp

guacyra.__index = guacyra

-- lua 5.2 workaround
local setfenv = setfenv or function(f, t)
  f = (type(f) == 'function' and f or debug.getinfo(f + 1, 'f').func)
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
guacyra.setfenv = setfenv

getfenv = getfenv or function(f)
  f = (type(f) == 'function' and f or debug.getinfo(f + 1, 'f').func)
  local name, val
  local up = 0
  repeat
    up = up + 1
    name, val = debug.getupvalue(f, up)
  until name == '_ENV' or name == nil
  return val
end

local function subst(ex, sub)
  if isAtom(ex) then
    if ex[0] == Symbol and sub[ex[1]] ~= nil then
      return copy(sub[ex[1]])
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

local function delta(sub1, sub2)
  for k, v1 in pairs(sub1) do
    local v2 = sub2[k]
    if v2 ~= nil then if not equal(v1, v2) then return false end end
  end
  return true
end

local function unionDelta(sub, th)
  local thr = {}
  for i = 1, #th do
    if delta(sub, th[i]) then
      local subi = {}
      for k, v in pairs(sub) do subi[k] = v end
      for k, v in pairs(th[i]) do subi[k] = v end
      thr[#thr + 1] = subi
    end
  end
  return thr
end

local function printSub(d) for k, v in pairs(d) do print('\t', k, v) end end

-- Adapted from "Non-linear Associative-Commutative Many-to-One
-- Pattern Matching with Sequence Variables"
-- by Manuel Krebber
local matchOneToOne
local function matchSequence(s, p, fa, comu, th)
  local n = #s
  local m = #p
  local nstar = 0
  for i = 1, m do if p[i][0] == BlankNullSequence then nstar = nstar + 1 end end
  if m - nstar > n then return {} end
  local nplus = 0
  for i = 1, m do if p[i][0] == BlankSequence then nplus = nplus + 1 end end
  if fa ~= nil then
    for i = 1, m do if p[i][0] == Blank then nplus = nplus + 1 end end
  end
  local nfree = n - m + nstar
  local nseq = nstar + nplus
  local thr = {}
  if nseq == 0 and nfree > 0 then return thr end
  for perm in permutations(n) do
    for k in weak_compositions(nfree, nseq) do
      local i = 1
      local j = 1
      local thprime = {}
      for ti = 1, #th do
        local subprime = {}
        for key, v in pairs(th[ti]) do subprime[key] = v end
        thprime[#thprime + 1] = subprime
      end
      for l = 1, m do
        local lsub = 1
        local hl = p[l][0]
        if hl == BlankNullSequence or hl == BlankSequence or
          (hl == Blank and fa ~= nil) then
          lsub = lsub + k[j]
          if hl == BlankNullSequence then lsub = lsub - 1 end
          j = j + 1
        end
        local sprime = Sequence()
        for si = i, i + lsub - 1 do sprime[#sprime + 1] = s[perm[si]] end
        thprime = matchOneToOne(sprime, p[l], fa, thprime)
        if #thprime == 0 then break end
        i = i + lsub
      end
      for ti = 1, #thprime do thr[#thr + 1] = thprime[ti] end
    end
    if not comu then break end
  end
  return thr
end

matchOneToOne = function(s, p, fa, th)
  local n = #s
  local hp = p[0]
  if hp == Blank and fa == nil then
    local subprime = {}
    local name = p[1][1]
    if name ~= '' then subprime[name] = s[1] end
    if n == 1 then
      if p[2] == nil or (p[2] == s[1][0]) then
        return unionDelta(subprime, th)
      end
    end
  elseif hp == Blank or hp == BlankSequence or hp == BlankNullSequence then
    local subprime = {}
    local name = p[1][1]
    local head = p[2]
    if hp == Blank and fa ~= nil then
      if name ~= '' then
        if #s > 1 then
          subprime[name] = fa(s)
        else
          subprime[name] = s[1]
        end
      end
    else
      if name ~= '' then subprime[name] = s end
    end
    local flag = true
    if head then
      for i = 1, #s do
        if not equal(s[i][0], head) then
          flag = false
          break
        end
      end
    end
    if flag and (hp == BlankNullSequence or n >= 1) then
      return unionDelta(subprime, th)
    end
  elseif isAtom(p) then
    if n == 1 and equal(s[1], p) then return th end
  elseif n == 1 then
    local hs = s[1][0]
    if equal(hp, hs) or hp == Blank then
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
      th = matchSequence(sq, sp, faprime, hp.orderless, th)
      if hp == Blank then
        local subh = {}
        local name = p[1][1]
        if name ~= '' then subh[name] = hs end
        return unionDelta(subh, th)
      else
        return th
      end
    end
  end
  return {}
end

guacyra.matches = function(ex, pat)
  return matchOneToOne(Sequence(ex), pat, nil, {{}})
end

local function matchR(ex, pat, cap)
  if isAtom(pat) then return equal(pat, ex) end
  if pat[0] == Blank then
    local name = pat[1][1]
    local head = pat[2]
    if head ~= nil then
      if isFunction(head) and not (head[1](ex))[1] then
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
    if (pat[i][0] == BlankNullSequence or pat[i][0] == BlankSequence) and i ~=
      #pat then error('Blank sequence must be the last part: ' .. tostr(pat)) end
    if pat[i][0] == BlankNullSequence or
      (pat[i][0] == BlankSequence and i <= #ex) then
      local name = pat[i][1][1]
      local head = pat[i][2]
      local exr = Sequence()
      for j = i, #ex do
        exr[#exr + 1] = ex[j]
        if head ~= nil then
          if isFunction(head) and not (head[1](ex[j]))[1] then
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

local function evalR(e)
  if guacyra.debug.eval then print('eval:\t', e) end
  if e[0] == Symbol then
    if e.value then
      return evalR(e.value)
    else
      return e
    end
  end
  if isAtom(e) then return e end
  local head = evalR(e[0])
  local ex = head()
  if head[0] == Function then
    for i = 1, #e do ex[i] = evalR(e[i]) end
    return evalR(head[1](unpack(ex)))
  end
  if head.holdAll then
    for i = 1, #e do ex[i] = e[i] end
  else
    for i = 1, #e do
      if head.holdFirst and i == 1 then
        ex[i] = e[i]
      else
        ex[i] = evalR(e[i])
      end
    end
  end
  if not head.sequenceHold then
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
  if head.flat then
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
  if guacyra.debug.sort then print('sort:\t', e) end
  if head.orderless then table.sort(ex, guacyra.less) end
  local tex
  for i = 1, #ex do
    local uphead = ex[i][0]
    if uphead[0] == Symbol and uphead.up then
      for j = 1, #uphead.up do
        tex = uphead.up[j](ex)
        if tex then return evalR(tex) end
      end
    end
  end
  if head[0] == Symbol and head.down then
    for j = 1, #head.down do
      tex = head.down[j](ex)
      if tex then return evalR(tex) end
    end
  end
  return ex
end

local function eval(e) return evalR(copy(e)) end
guacyra.eval = eval

guacyra.addDown = function(ex, tr)
  if ex[0] == Symbol then ex.down[#ex.down + 1] = tr end
end

guacyra.addUp = function(ex, tr)
  if ex[0] == Symbol then ex.up[#ex.up + 1] = tr end
end

local function wrap(fu, symbols)
  local i = {}
  local o = {}
  symbols = symbols or {}
  symbols.In = i
  symbols.Out = o
  local st = {}
  st.__index = function(t, k)
    local s = rawget(symbols, k) or rawget(guacyra, k) or rawget(_G, k)
    if s == nil then
      s = guacyra.Symbol(k)
      symbols[k] = s
    end
    return s
  end
  local it = {}
  it.__newindex = function(t, k, v)
    if guacyra.debug.io then print('In[' .. k .. ']=', v) end
    rawset(t, k, v)
    o[k] = v:eval()
    if guacyra.debug.io then print('Out[' .. k .. ']=', o[k]) end
  end
  setmetatable(i, it)
  setmetatable(symbols, st)
  local oldenv = getfenv(fu)
  setfenv(fu, symbols)
  local ret = fu()
  setfenv(fu, oldenv)
  return ret
end
guacyra.wrap = wrap

guacyra.wrap(function()
  guacyra.SetDelayed = SetDelayed
  SetDelayed.holdAll = true
  SetDelayed:addDown(function(exp)
    local cap = {}
    if exp:match(SetDelayed(a_(Symbol), b_), cap) then
      cap.a.value = cap.b
      return cap.b
    elseif exp:match(SetDelayed(f_(), v_(Function)), cap) then
      local ve = cap.v[1]
      cap.f:addDown(function(exp2) return wrap(ve) end)
    elseif exp:match(SetDelayed(f_(p__), v_(Function)), cap) then
      local fe = cap.p:copy()
      fe[0] = cap.f
      local ve = cap.v[1]
      cap.f:addDown(function(exp2)
        local cap2 = {}
        local ret = exp2:match(fe, cap2)
        if ret then return wrap(ve, cap2) end
        return nil
      end)
      return Null
    elseif exp:match(SetDelayed(f_(p__), v_), cap) then
      local fe = cap.p:copy()
      fe[0] = cap.f
      local ve = cap.v
      cap.f:addDown(function(exp2)
        local cap2 = {}
        local ret = exp2:match(fe, cap2)
        if ret then return ve:subst(cap2) end
        return nil
      end)
      return Null
    end
    return nil
  end)
end)

guacyra.wrap(function()
  guacyra.Apply = Apply
  In[1] = SetDelayed(Apply(a_, b_(c___)), function() return a(c) end)
  guacyra.Map = Map
  In[2] = SetDelayed(Map(a_, b_(c___)), function()
    for i = 1, #c do c[i] = a(c[i]) end
    return b(c)
  end)
  guacyra.First = First
  In[3] = SetDelayed(First(a_(b_, c___)), function() return b end)
  guacyra.Rest = Rest
  In[4] = SetDelayed(Rest(a_(b_, c___)), function() return a(c) end)
  guacyra.Fold = Fold
  In[5] = SetDelayed(Fold(a_, b_, c_), function()
    local t = b
    for i = 1, #c do t = a(t, c[i]):eval() end
    return t
  end)
  guacyra.Cat = Cat
  In[6] = SetDelayed(Cat(c___), function()
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
  guacyra.Range = Range
  In[7] = SetDelayed(Range(a_(Number), b_(Number)), function()
    local t = List()
    for i = a[1], b[1] do t[#t + 1] = Number(i) end
    return t
  end)
  guacyra.RandomReal = RandomReal
  In[8] = SetDelayed(RandomReal(), function() return Number(random()) end)
  In[9] = SetDelayed(RandomReal({a_(Number), b_(Number)}),
               function() return Number(a[1] + (b[1] - a[1]) * random()) end)
  In[10] = SetDelayed(RandomReal({a_(Number), b_(Number)}, c_(Number)), function()
    local l = List()
    for i = 1, c[1] do l[i] = Number(a[1] + (b[1] - a[1]) * random()) end
    return l
  end)
  guacyra.Rule = Rule
  Rule.sequenceHold = true
  guacyra.Matches = Matches
  Matches.holdAll = true
  In[11] = SetDelayed(Matches(p_,e_), function()
    local res = e:matches(p)
    local ret = List()
    for i = 1, #res do
      local l = List()
      for k, v in pairs(res[i]) do
        l[#l+1] = Rule(Symbol(k), v)
      end
      ret[#ret+1] = l
    end
    return ret
  end)
end)

guacyra.__add = function(a, b) return Plus(a, b) end
guacyra.__sub = function(a, b) return Plus(a, Times(-1, b)) end
guacyra.__unm = function(a) return Times(-1, a) end
guacyra.__mul = function(a, b) return Times(a, b) end
guacyra.__div = function(a, b) return Times(a, Power(b, -1)) end
guacyra.__pow = function(a, b) return Power(a, b) end

-- Algebra
Plus.flat = true
Plus.orderless = true
guacyra.wrap(function()
  In[1] = SetDelayed(Plus(), 0)
  In[2] = SetDelayed(Plus(a_), a)
  In[3] = SetDelayed(Plus(0, b__), Plus(b))
  In[4] = SetDelayed(Plus(a_(Number), b_(Number), c___),
               function() return Plus(Number(a[1] + b[1]), c) end)
  In[5] = SetDelayed(Plus(a_(Number), p_(Rational), c___), function()
    if isInteger(a[1]) then
      return Plus(Rational(a[1] * p[2] + p[1], p[2]), c)
    else
      return Plus(Number((a[1] * p[2] + p[1]) / p[2]), c)
    end
  end)
  In[6] = SetDelayed(Plus(p_(Rational), a_(Number), c___), function()
    if isInteger(a[1]) then
      return Plus(Rational(a[1] * p[2] + p[1], p[2]), c)
    else
      return Plus(Number((a[1] * p[2] + p[1]) / p[2]), c)
    end
  end)
  In[7] = SetDelayed(Plus(p_(Rational), q_(Rational), c___), function()
    return Plus(Rational(p[1] * q[2] + q[1] * p[2], p[2] * q[2]), c)
  end)
end)

Times.flat = true
Times.orderless = true
guacyra.wrap(function()
  In[1] = SetDelayed(Times(), 1)
  In[2] = SetDelayed(Times(a_), a)
  In[3] = SetDelayed(Times(1, b__), Times(b))
  In[4] = SetDelayed(Times(0, b__), 0)
  In[5] = SetDelayed(Times(a_(Number), b_(Number), c___),
               function() return Times(Number(a[1] * b[1]), c) end)
  In[6] = SetDelayed(Times(a_(Number), p_(Rational), c___), function()
    if isInteger(a[1]) then
      return Times(Rational(a[1] * p[1], p[2]), c)
    else
      return Times(Number(a[1] * p[1] / p[2]), c)
    end
  end)
  In[7] = SetDelayed(Times(p_(Rational), a_(Number), c___), function()
    if isInteger(a[1]) then
      return Times(Rational(a[1] * p[1], p[2]), c)
    else
      return Times(Number(a[1] * p[1] / p[2]), c)
    end
  end)
  In[8] = SetDelayed(Times(p_(Rational), q_(Rational), c___), function()
    return Times(Rational(p[1] * q[1], p[2] * q[2]), c)
  end)
  In[9] = SetDelayed(Times(-1, Plus(a__)), function()
    local r = Plus()
    for i = 1, #a do r[i] = Times(-1, a[i]) end
    return r
  end)
end)

local function ins(t, a, b)
  if t[a:tostring()] == nil then
    t[a:tostring()] = {a, Sequence(b)}
    return false
  else
    local s = t[a:tostring()][2]
    s[#s + 1] = b
    return true
  end
end

guacyra.wrap(function()
  In[1] = SetDelayed(Plus(c___), function()
    local r = Plus()
    local flag = false
    local coefs = {}
    for i = 1, #c do
      local cap = {}
      if c[i]:match(Times(a_(Number), b_), cap) then
        flag = ins(coefs, cap.b, Number(cap.a[1])) or flag
      elseif c[i]:match(Times(a_(Number), b__), cap) then
        flag = ins(coefs, cap.b, Number(cap.a[1])) or flag
      elseif c[i]:match(Times(p_(Rational), b_), cap) then
        flag = ins(coefs, cap.b, Rational(cap.p[1], cap.p[2])) or flag
      elseif c[i]:match(Times(p_(Rational), b__), cap) then
        flag = ins(coefs, cap.b, Rational(cap.p[1], cap.p[2])) or flag
      elseif c[i]:match(Times(b__), cap) then
        flag = ins(coefs, cap.b, Number(1)) or flag
      else
        flag = ins(coefs, c[i], Number(1)) or flag
      end
    end
    if flag then
      for k, v in pairs(coefs) do
        v[2][0] = Plus
        r[#r + 1] = Times(v[2], v[1])
      end
      return r
    end
    return nil
  end)
end)

guacyra.wrap(function()
  In[1] = SetDelayed(Times(c__), function()
    -- collect bases
    local r = Times()
    local flag = false
    local coefs = {}
    for i = 1, #c do
      local cap = {}
      if c[i]:match(Power(a_(Number), b_(Rational)), cap) then
        flag = ins(coefs, Power(cap.a, cap.b), Number(1)) or flag
      elseif c[i]:match(Power(a_, b_), cap) then
        flag = ins(coefs, cap.a, cap.b) or flag
      else
        flag = ins(coefs, c[i], Number(1)) or flag
      end
    end
    if flag then
      for k, v in pairs(coefs) do
        v[2][0] = Plus
        r[#r + 1] = Power(v[1], v[2])
      end
      return r
    end
    return nil
  end)
  In[2] = SetDelayed(Times(c__), function()
    -- collect exponents
    local r = Times()
    local flag = false
    local coefs = {}
    for i = 1, #c do
      local cap = {}
      if c[i]:match(Power(a_(Number), b_), cap) then
        flag = ins(coefs, cap.b, cap.a) or flag
      else
        ins(coefs, Number(1), c[i])
      end
    end
    if flag then
      for k, v in pairs(coefs) do
        v[2][0] = Times
        r[#r + 1] = Power(v[2], v[1])
      end
      return r
    end
    return nil
  end)
end)

guacyra.wrap(function()
  In[1] = SetDelayed(_ ^ 0, 1)
  In[2] = SetDelayed(1 ^ _, 1)
  In[3] = SetDelayed(a_ ^ 1, a)
  In[4] = SetDelayed(a_(Number) ^ b_(Number), function()
    if isInteger(a[1]) and isInteger(b[1]) then
      if b[1] < 0 then
        return Rational(1, floor(a[1] ^ (-b[1])))
      elseif b[1] > 0 then
        return Number(floor(a[1] ^ b[1]))
      end
    else
      return Number(a[1] ^ b[1])
    end
  end)
  In[5] = SetDelayed(p_(Rational) ^ b_(Number), function()
    if isInteger(b[1]) then
      if b[1] < 0 then
        return Rational(floor(p[2] ^ (-b[1])), floor(p[1] ^ (-b[1])))
      elseif b[1] > 0 then
        return Rational(floor(p[1] ^ b[1]), floor(p[2] ^ b[1]))
      end
    else
      return Number((p[1] / p[2]) ^ b[1])
    end
  end)
  In[6] = SetDelayed(a_(Number) ^ p_(Rational), function()
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
    if isInteger(a[1]) then
      if a[1] > 0 then
        if p[1] > 0 then
          local fact = factorization(a[1])
          local u, v = root(fact, p[1], p[2])
          if u == 1 and p[1] == 1 then
            return nil
          else
            return Times(u, Power(v, Rational(1, p[2])))
          end
        else
          local fact = factorization(a[1])
          p[1] = -p[1]
          local k = math.floor(p[1] / p[2])
          local r = p[1] - k * p[2]
          local u, v = root(fact, p[2] - r, p[2])
          return Times(Rational(u, a[1] ^ (k + 1)), Power(v, Rational(1, p[2])))
        end
      end
    else
      return Number(a[1] ^ (p[1] / p[2]))
    end
  end)
  In[7] = SetDelayed(a_(Rational) ^ p_(Rational), function()
    return Times(Power(Number(a[1]), p),
                 Power(Number(a[2]), Rational(-p[1], p[2])))
  end)
  In[8] = SetDelayed(Power(Power(a_, b_), c_), function() return Power(a, b * c) end)
  In[9] = SetDelayed(Power(Times(a__), e_), function()
    local r = Times()
    for i = 1, #a do r[#r + 1] = Power(a[i], e) end
    return r
  end)
end)

guacyra.wrap(function()
  guacyra.Expand = Expand
  In[1] = SetDelayed(Expand(Times(a__)), function()
    local aa = a
    for j = 1, #aa do
      local cap = {}
      if aa[j]:match(Plus(b__), cap) then
        local r = Plus()
        for k = 1, #cap.b do
          local t = aa:copy()
          t[j] = cap.b[k]
          r[#r + 1] = Expand(Times(t))
        end
        return r
      elseif aa[j]:match(Power(Plus(b__), n_(Number)), cap) and
        isInteger(cap.n[1]) and cap.n[1] > 0 then
        local t = aa:copy()
        t[0] = Times
        t[j] = Expand(Power(Plus(cap.b), cap.n[1]))
        return Expand(t)
      end
    end
    return Times(a)
  end)
  In[2] = SetDelayed(Expand(Power(Plus(a_, b__), n_(Number))), function()
    local r = Plus()
    for i = 0, n[1] do
      r[#r + 1] = Expand(Times(binomial(n[1], i), Power(a, n[1] - i),
                               Expand(Power(Plus(b), i))))
    end
    return r
  end)
  In[3] = SetDelayed(Expand(Plus(a_, b__)),
               function() return Plus(Expand(a), Expand(Plus(b))) end)
  In[4] = SetDelayed(Expand(a_), function() return a end)
end)

guacyra.wrap(function ()
  guacyra.NumeratorDenominator = NumeratorDenominator
  In[1] = SetDelayed(NumeratorDenominator(p_(Rational)), function ()
    return List(p[1], p[2])
  end)
  In[2] = SetDelayed(NumeratorDenominator(a_(Number)), function ()
    return List(a[1], 1)
  end)
  In[3] = SetDelayed(NumeratorDenominator(Power(a_, b_(Number))), function ()
    if b[1]<0 then
      return List(1, Power(a, -b[1]))
    else
      return List(Power(a, b), 1)
    end
  end)
  In[4] = SetDelayed(NumeratorDenominator(Times(a__)), function ()
    local e = Map(NumeratorDenominator,List(a)):eval()
    local num = Times()
    local den = Times()
    for i=1,#e do
      num[#num+1] = e[i][1]
      den[#den+1] = e[i][2]
    end
    return List(num,den)
  end)
  In[5] = SetDelayed(NumeratorDenominator(Plus(a__)), function ()
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
  In[6] = SetDelayed(NumeratorDenominator(a_), function ()
    return List(a, 1)
  end)
  guacyra.Denominator = Denominator
  In[7] = SetDelayed(Denominator(a_), function ()
    local l = NumeratorDenominator(a):eval()
    return l[2]
  end)
  guacyra.Numerator = Numerator
  In[8] = SetDelayed(Numerator(a_), function ()
    local l = Numerator(a):eval()
    return l[1]
  end)
  guacyra.Together = Together
  In[9] = SetDelayed(Together(a_), function ()
    local l = NumeratorDenominator(a):eval()
    if l[2][0]==Number then
      return l[1]/l[2]
    else
      return Together(l[1])/Together(l[2])
    end
  end)
  guacyra.Sqrt = Sqrt
  In[10] = SetDelayed(Sqrt(a_), Power(a, Rational(1,2)))
end)

--LaTeX

guacyra.wrap(function ()
  local LaTeXP = Symbol("LaTeXP")
  guacyra.LaTeX = LaTeX
  In[1] = SetDelayed(LaTeXP(Plus(c__)), Cat('(', LaTeX(Plus(c)), ')'))
  In[2] = SetDelayed(LaTeXP(a_), LaTeX(a))
  In[3] = SetDelayed(LaTeX(p_(Rational)), function()
    local a, b = p[1], p[2]
    if a<0 then 
      return String('-\\frac{'..(-a)..'}{'..b..'}')
    else     
      return String('\\frac{'..(a)..'}{'..b..'}')
    end
  end)
  In[4] = SetDelayed(LaTeX(Times(-1,a__)), Cat('-', LaTeXP(Times(a))))
  In[5] = SetDelayed(LaTeX(Times(a__)), function()
    local l = NumeratorDenominator(Times(a)):eval()
    if l[2][0]==Number then
      return Apply(Cat,Map(LaTeXP,List(a)))
    else 
      local num = LaTeX(l[1]):eval()
      local den = LaTeX(l[2]):eval()
      return Cat('\\frac{',num,'}{',den,'}')
    end
  end)
  In[6] = SetDelayed(LaTeX(Power(a_,b_(Rational))), function()
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
  In[7] = SetDelayed(LaTeX(Power(a_, b_(Number))), function()
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
  In[8] = SetDelayed(LaTeX(Plus(c__)), function()
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
  In[9] = SetDelayed(LaTeX(a_), function()
    return String(a:tostring())
  end)
  guacyra.LuaTeX = LuaTeX
  In[10] = SetDelayed(LuaTeX(a_), function()
    local l = LaTeX(a):eval()
    print(string.sub(l[1],1,-1))
    return l
  end)
end)

return guacyra
