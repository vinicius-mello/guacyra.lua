local guacyra = require('guacyra')

local Symbol = guacyra.Symbol
local Number = guacyra.Number
local List = guacyra.List
local Error = guacyra.Error
local Map = guacyra.Map
local Apply = guacyra.Apply

local Range = Symbol('Range')
Range:addDown(function(exp)
  if Match(exp, Range(a_(Number))) then
    local r = List()
    for i=1,a[1] do
      r[i] = Number(i)
    end
    return r
  elseif Match(exp, Range(a_,b_)) then
    local r = List()
    local i = a
    repeat 
      r[#r+1] = i
      i = (i + 1):eval()
    until b:less(i)
    return r
  elseif Match(exp, Range(a_,b_,c_)) then
    local r = List()
    local i = a
    repeat 
      r[#r+1] = i
      i = (i + c):eval()
    until b:less(i)
    return r
  end
  return nil
end)

local Fold = Symbol('Fold')
Fold:addDown(function(exp)
  if Match(exp, Fold(f_,x_, List(a___))) then
    local r = x
    for i=1,#a do
      r = f(r,a[i]):eval()
    end
    return r
  end
  return nil 
end)

local FoldList = Symbol('FoldList')
FoldList:addDown(function(exp)
  if Match(exp, FoldList(f_,x_, List(a__))) then
    local r = x
    local l = List(x)
    for i=1,#a do
      r = f(r,a[i]):eval()
      l[#l+1] = r
    end
    return l
  end
  return nil 
end)

local Nest = Symbol('Nest')
Nest:addDown(function(exp)
  if Match(exp, Nest(f_,x_, n_(Number))) then
    local r = x
    for i=1,n[1] do
      r = f(r):eval()
    end
    return r
  end
  return nil 
end)

local NestList = Symbol('NestList')
NestList:addDown(function(exp)
  if Match(exp, NestList(f_,x_, n_(Number))) then
    local r = x
    local l = List(x)
    for i=1,n[1] do
      r = f(r):eval()
      l[#l+1] = r
    end
    return l
  end
  return nil 
end)

local RandomReal = Symbol('RandomReal')
RandomReal:addDown(function(exp)
  if Match(exp, RandomReal()) then
    return Number(math.random())
  elseif Match(exp, RandomReal(List(a_(Number),b_(Number)))) then
    return Number(a[1]+(b[1]-a[1])*math.random())
  elseif Match(exp, RandomReal(List(a_(Number),b_(Number)),c_(Number))) then
    local l = List()
    for i=1,c[1] do
      l[i] = Number(a[1]+(b[1]-a[1])*math.random())
    end
    return l
  end
  return nil 
end)

local Union = Symbol('Union')
Union:addDown(function(exp)
  if Match(exp, Union(a___)) then
    local l = List()
    for i=1,#a do
      for j=1,#a[i] do
        l[#l+1] = a[i][j]
      end
    end
    table.sort(l,lessTree)
    local r = List()
    if #l>0 then
      local last = l[1]
      r[#r+1] = l[1]
      for i=2,#l do
        local li = l[i]
        if not li:equal(last) then
          r[#r+1] = li
          last = li
        end
      end
    end
    return r
  end
  return nil 
end)


return {
  Range = Range,
  Fold = Fold,
  FoldList = FoldList,
  Nest = Nest,
  NestList = NestList,
  Union = Union,
  RamdomReal = RandomReal,
}
