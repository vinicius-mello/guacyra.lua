local symbols = {}
symbols.__index = function(t,k)
  local s = symbols[k]
  if s == nil then
    s = Symbol(k)
    symbols[k] = s
    return s
  else
    return s
  end
end
i = {}
o = {}
local it = {}
it.__newindex = function(t,k,v)
  print('i['..k..']=',v)
  rawset(t,k,v)
  o[k] = v:eval()
  print('o['..k..']=',o[k])
  return
end
setmetatable(i,it)
setmetatable(_G,symbols)

