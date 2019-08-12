local guacyra = require('guacyra')
local algebra = require('algebra')

local Symbol = guacyra.Symbol
local String = guacyra.String
local Plus = guacyra.Plus
local Times = guacyra.Times
local Power = guacyra.Power
local Number = guacyra.Number
local Rational = guacyra.Rational
local Cat = guacyra.Cat
local NumeratorDenominator = algebra.NumeratorDenominator

local LaTeXP = Symbol('LaTeXP')
LaTeXP:addDown(function(exp)
  if Match(exp, LaTeXP(Plus(c__))) then
    return Cat('(',LaTeX(Plus(c)),')')
  elseif Match(exp, LaTeXP(a_)) then
    return LaTeX(a)
  end
  return nil
end)

local LaTeX = Symbol('LaTeX')
LaTeX:addDown(function(exp)
  if Match(exp, LaTeX(p_(Rational))) then
    local a,b = p[1],p[2]
    if a<0 then 
      return String('-\\frac{'..(-a)..'}{'..b..'}')
    else     
      return String('\\frac{'..(a)..'}{'..b..'}')
    end
  elseif Match(exp, LaTeX(Times(-1,a__))) then
    return Cat('-',LaTeXP(Times(a)))
  elseif Match(exp, LaTeX(Times(a__))) then
    local l = NumeratorDenominator(Times(a)):eval()
    if l[2][0]==Number then
      return Apply(Cat,Map(LaTeXP,List(a)))
    else 
      local num = LaTeX(l[1]):eval()
      local den = LaTeX(l[2]):eval()
      return Cat('\\frac{',num,'}{',den,'}')
    end
  elseif Match(exp, LaTeX(Power(a_,b_(Rational)))) and b[1]==1 then
    if b[2]==2 then
      return Cat('\\sqrt{',LaTeX(a),'}')
    else
      return Cat('\\sqrt['..b[2]..']{',LaTeX(a),'}')
    end
  elseif Match(exp, LaTeX(Power(a_,b_(Number)))) then
    if b[1]<0 then
      return Cat('\\frac{1}{',LaTeX(Power(a,-b[1])),'}')
    else 
      b = ''..b[1]
      if #b>1 then
        return Cat(LaTeXP(a),'^{'..b..'}')
      else
        return Cat(LaTeXP(a),'^'..b)
      end
    end
  elseif Match(exp, LaTeX(Plus(c__))) then
    local s = ''
    for i=1,#c do
      local t = LaTeX(c[i]):eval()
      if t[1]:sub(1,1)~='-' and i~=1 then
        s = s..'+'
      end
      s = s..t[1]
    end
    return String(s)
  elseif Match(exp, LaTeX(a_)) then
    return String(a:tostring())
  end
  return nil
end)

return {
  LaTeX = LaTeX
}
