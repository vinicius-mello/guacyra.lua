local floor, infinite, random = math.floor, math.huge, math.random
local abs = math.abs

local function gcd(a,b)
    while b~=0 do 
        a,b=b,a%b
    end
    return abs(a)
end

local function isInteger(a)
  return type(a)=='number' and a==floor(a)
end

local function binomial( n, k )
  if k > n then return nil end
  if k > n/2 then k = n - k end 
  numer, denom = 1, 1
  for i = 1, k do
    numer = numer * ( n - i + 1 )
    denom = denom * i
  end
  return numer / denom
end

--- Calculate the modular power for any exponent.
local function fmodpow(bse, exp, mod)
  bse = bse % mod
  local prod = 1
  while exp > 0 do
    if exp % 2 == 1 then
      prod = prod * bse % mod
    end
    exp = floor(exp / 2)
    bse = (bse ^ 2) % mod
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
  local s, d = 0, n-1
  while d%2==0 do
    d, s = d/2, s+1
  end
  for i=1,select('#', ...) do
    local witness = select(i, ...)
    if witness >= n then break end
    local x = fmodpow(witness, d, n)
    if (x ~= 1) then
      local t = s
      while x ~= n - 1 do
        t = t - 1
        if t <= 0 then
          return false
        end
        x = (x * x) % n
        if x == 1 then
          return false
        end
      end
    end
  end
  return true
end

local mrthreshold = 1e3
local isprime

local primes = setmetatable({2,3--[[just hard-code the even special case and following number]]}, {__index = function(self, index)
  if type(index) == 'number' then
    for i=#self,index-1 do local dummy = self[i] end -- Precalculate previous primes to avoid building up a stack
    for candidate = self[index-1] + 2--[[All primes >2 are odd]], infinite do
      if index > mrthreshold then
        if miller_rabin(candidate, witnesses(candidate)) then
          rawset(self, index, candidate)
          return candidate
        end
      else
        local half = floor(candidate/2)
        for i=1,index-1 do
          local div = self[i]
          if div > half then rawset(self, index, candidate); return candidate end -- A number can't possibly be divisible by something greater than its half
          if candidate % div == 0 then break end -- Candidate is divisible by a prime, this not prime itself
        end
      end
    end
  end
end})

local function factorize(subject)
  if subject == 1 then
    return -- Can be ommitted for implicit return ;)
  elseif subject > 0 then
    for i=1, infinite do
      local candidate = primes[i]
        if subject % candidate == 0 then
          return candidate, factorize(subject/candidate)
        end
    end
  else
    return nil, "Can't be bothered to look up if negative numbers have a prime factorization"
  end
end

local function factorization(n) 
  local a = {factorize(n)}
  local count = 0
  local cur = a[1]
  local r = {}
  for i=1,#a+1 do
    local ai = a[i]
    if ai==cur then
      count = count+1
    else
      r[#r+1] = {cur,count}
      cur = ai
      count = 1
    end
  end
  return r
end

return {
  gcd = gcd,
  isInteger = isInteger,
  binomial = binomial,
  primes = primes,
  factorize = factorize,
  factorization = factorization,
}
