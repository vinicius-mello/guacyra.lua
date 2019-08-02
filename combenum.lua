
local function weak_compositions(m, n)
  local first = true
  local it = function(v,i)
    if first then
      first = false
      return v
    end
    if n==0 or v[n]==m then return nil end
    local r
    for k=n-1,1,-1 do
      r = k
      if v[r]~=0 then break end
    end
    v[r] = v[r]-1;
    for j=r+1,n do v[j]=0 end
    v[r+1] = m
    for j=1,r do v[r+1]=v[r+1]-v[j] end
    return v
  end
  local ini = {}
  for i=1,n do ini[i] = 0 end
  if n>0 then ini[1] = m end
  return it,ini,ini
end

local function permutations(n)
  local first = true
  local it = function(v,k)
    if first then
      first = false
      return v
    end
    local i = n
	  while i > 1 and v[i - 1] >= v[i] do
		  i = i-1
		end
	  if (i == 1) then
		  return nil
	  end
	  local j = n
	  while v[j] <= v[i - 1] do
  	  j = j-1
  	end
	  v[i - 1], v[j] = v[j], v[i-1]
    j = n
    while i < j do
		  v[i], v[j] = v[j], v[i]
		  i = i + 1
		  j = j - 1
	  end
	  return v
  end
  local ini = {}
  for i=1,n do ini[i] = i end
  return it,ini,ini
end

return {
  weak_compositions = weak_compositions,
  permutations = permutations,
}
