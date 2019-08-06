local guacyra = require('guacyra')
local setfenv = guacyra.setfenv

local function SymbEnv(pr)
  local i = {}
  local o = {}
  local symbols = {}
  symbols.In = i
  symbols.Out = o
  local _G = _G
  local st = {}
  st.__index = function(t,k)
    local s = rawget(_G,k)
    if s == nil then
      s = rawget(symbols,k) 
      if s == nil then
        s = guacyra.Symbol(k)
        symbols[k] = s
      end
      return s
    else
      return s
    end
  end
  local it = {}
  it.__newindex = function(t,k,v)
    if pr then print('In['..k..']=',v) end
    rawset(t,k,v)
    o[k] = v:eval()
    if pr then print('Out['..k..']=',o[k]) end
  end
  setmetatable(i,it)
  setmetatable(symbols,st)
  setfenv(2,symbols)
end

return {
  SymbEnv = SymbEnv
}
