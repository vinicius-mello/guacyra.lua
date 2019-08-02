
local function gcd(a,b)
    while b~=0 do 
        a,b=b,a%b
    end
    return math.abs(a)
end

local function isInteger(a)
  return type(a)=='number' and a==math.floor(a)
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

return {
  gcd = gcd,
  isInteger = isInteger,
  binomial = binomial,
}
