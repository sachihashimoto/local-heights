declare type RngSerAnn[RngSerAnnElt];
declare type RngLaurPol[RngLaurPolElt];

declare attributes RngSerAnn: BaseRing, v1, v2, LaurPolRing, VariableName, p, Generator;
declare attributes RngSerAnnElt: approx, v1, v2, v1AdicPrec, v2AdicPrec, Parent;

// approx::RngLaurPolElt, v_1, v_2, v_p^v_1(f - approx), v_p^v_2(f - approx) represents the infinite power series f that converges on the annulus whose radii have vals v1 and v2

declare attributes RngLaurPol: BaseRing, VariableName, Generator;
declare attributes RngLaurPolElt: coeffs, powers, Parent;

intrinsic Parent(x::RngLaurPolElt) -> RngLaurPol
  {Return the parent of x}
  return x`Parent;
end intrinsic;

intrinsic BaseRing(x::RngLaurPol) -> Any
  {return the base ring}
  return x`BaseRing;
end intrinsic;

intrinsic Consolidate(x::RngLaurPolElt) -> RngLaurPolElt
  {Consolidate x (remove doubles, and remove zero coefficients)}
  sortedPowers := Sort([[x`powers[i], i] :  i in [1 .. #x`powers]]);
  ncoeffs := [];
  npowers := [];
  R := x`Parent`BaseRing;
  i := 1;
  while i le #x`powers do
    j := i;
    c := R!0;
    while j le #x`powers and sortedPowers[j][1] eq sortedPowers[i][1] do
      c := c + x`coeffs[sortedPowers[j][2]];
      j := j + 1;
    end while;
    if c ne R!0 then
      Append(~ncoeffs, c);
      Append(~npowers, sortedPowers[i][1]);
    end if;
    i := j;
  end while;
  y := New(RngLaurPolElt);
  y`coeffs := ncoeffs;
  y`powers := npowers;
  y`Parent := x`Parent;
  return y;
end intrinsic;

function CreateLaurPolElement(D, coeffs, powers)
  x := New(RngLaurPolElt);
  x`coeffs := coeffs;
  x`powers := powers;
  x`Parent := D;
  return Consolidate(x);
end function;

function CreateLaurPolFromPowerSeries(D, f, pAdicPrecLeft, pAdicPrecRight)
  powers := [Precision(f)[1]-Precision(Parent(f)) .. Precision(f)[1] - 1];
  coeffs := [Coefficient(f, i) : i in powers];
  return CreateLaurPolElement(D, coeffs, powers);
end function;

intrinsic IsCoercible(D::RngLaurPol, x::.) -> BoolElt, .
  {Return whether x is coercible into D and the result if so}
  R := D`BaseRing;
  if Type(x) eq RngLaurPolElt then
	return true, CreateLaurPolElement(D, x`coeffs, x`powers);
  end if;
  if IsCoercible(R, x) then
    coeffs := [R!x];
    powers := [0];
    y := CreateLaurPolElement(D, coeffs, powers);
  return true, y;
    end if;
    if Type(x) in [RngSerPowElt, RngSerLaurElt] then
  return true, CreateLaurPolFromPowerSeries(D, x, Infinity(), Infinity());
    end if;
  if Type(x) eq SeqEnum then
    require #x eq 2 : "The input should be a size two list of the list of coefficients resp. powers";
    require Type(x[1]) eq SeqEnum and Type(x[2]) eq SeqEnum : "The input should be a size two list of the list of coefficients resp. powers";
    require #x[1] eq #x[2] : "The list of coefficients and powers should have the same length";
    require &and[IsCoercible(R,a) : a in x[1]] : "Coefficients should be coercible to the base ring";
    return CreateLaurPolElement(D, [R!a : a in x[1]], x[2]);
  end if;
  if Type(x) in [RngSerPowElt, RngSerLaurElt] then
   return true, CreateLaurPolFromPowerSeries(D, x);
  end if;
  return false, "Not implemented";
end intrinsic;

intrinsic LaurentPolynomialRing(BaseRing::Rng, VariableName::MonStgElt) -> RngSerAnn
  {Create the direct product of given rings (a tuple)}
  D := New(RngLaurPol);
  D`BaseRing := BaseRing;
  D`VariableName := VariableName;
  D`Generator := CreateLaurPolElement(D, [BaseRing!1],[1]);
  return D;
end intrinsic;

intrinsic Coefficient(f::RngLaurPolElt, i::RngIntElt) -> .
  {Return the ith coefficient of f}
  if not(i in f`powers) then
    return (f`Parent`BaseRing)!0;
  end if;
  j := Index(f`powers, i);
  return f`coeffs[j];
end intrinsic;

intrinsic Degree(f::RngLaurPolElt) -> RngIntElt
  {Return the degree of f}
  // TODO: needs to return the minimum power whose coefficient is not weakly zero.
  Px := f`powers;
  return Px[#Px];
end intrinsic;

intrinsic Print(x::RngLaurPol)
  {Print x}
  printf "Laurent polynomial ring in %o over %o", x`VariableName, x`BaseRing;
end intrinsic;

intrinsic Print(x::RngLaurPolElt)
  {Print x}
  if #x`powers eq 0 then
    printf "0";
    return;
  end if;
  printf "(%o)*%o^%o", x`coeffs[1], x`Parent`VariableName, x`powers[1];
  for i in [2 .. #x`powers] do
    printf " + (%o)*%o^%o", x`coeffs[i], x`Parent`VariableName, x`powers[i];
  end for;
end intrinsic;

intrinsic IsZero(x::RngLaurPolElt) -> BoolElt
  {Check if x is zero, assuming the base ring is exact. Cf. IsWeaklyZero}
  return #(x`powers) eq 0;
end intrinsic;

intrinsic IsWeaklyZero(x::RngLaurPolElt) -> BoolElt
  {Check if x is weakly zero, i.e. if all coefficients are weakly zero. Cf. IsZero}
  return &and[IsWeaklyZero(c) : c in x`coeffs];
end intrinsic;

intrinsic Add(x::RngLaurPolElt,y::RngLaurPolElt) -> RngLaurPolElt
  {return  x + y}
  D := Parent(x);
  require D cmpeq Parent(y): "Incompatible arguments";
  Cx := x`coeffs;
  Cy := y`coeffs;
  Px := x`powers;
  Py := y`powers;
  Cx := Cx cat Cy;
  Px := Px cat Py;
  xplusy := CreateLaurPolElement(Parent(x), Cx, Px);
  return xplusy;
end intrinsic;

intrinsic '+'(x::., y::RngLaurPolElt) -> RngLaurPolElt
  {Return x + y}
  D := Parent(y);
  b, z := IsCoercible(D,x);
  require b : "The first argument is not coercible to the parent of the second argument";
  return Add(z,y);
end intrinsic;

intrinsic '+'(x::RngLaurPolElt, y::.) -> RngLaurPolElt
  {Return x + y}
  D := Parent(x);
  b, z := IsCoercible(D,y);
  require b : "The second argument is not coercible to the parent of the first argument";
  return Add(x,z);
end intrinsic;

intrinsic AdditiveInverse(x::RngLaurPolElt) -> RngLaurPolElt
  {return -x}
  return CreateLaurPolElement(Parent(x), [-a : a in x`coeffs], x`powers);
end intrinsic;

intrinsic '-'(x::RngLaurPolElt) -> RngLaurPolElt
  {return -x}
  return AdditiveInverse(x);
end intrinsic;

intrinsic '-'(x::., y::RngLaurPolElt) -> RngLaurPolElt
  {Return x - y}
  D := Parent(y);
  b, z := IsCoercible(D,x);
  require b : "The first argument is not coercible to the parent of the second argument";
  return Add(z,AdditiveInverse(y));
end intrinsic;

intrinsic '-'(x::RngLaurPolElt, y::.) -> RngLaurPolElt
  {Return x - y}
  D := Parent(x);
  b, z := IsCoercible(D,y);
  require b : "The first argument is not coercible to the parent of the second argument";
  return Add(x,AdditiveInverse(z));
end intrinsic;

intrinsic Multiply(x::RngLaurPolElt, y::RngLaurPolElt) -> RngLaurPolElt
  {Return x*y}
  D := Parent(x);
  require D cmpeq Parent(y): "Incompatible arguments";
  Cx := x`coeffs;
  Px := x`powers;
  Cy := y`coeffs;
  Py := y`powers;

  prodcoeffs := [];
  prodpowers := [];

  for i in [1..#Cx] do
    for j in [1..#Cy] do //multiply every term with the first
      Append(~prodcoeffs, Cx[i]*Cy[j]);
      Append(~prodpowers, Px[i]+Py[j]);
    end for;
  end for;
  prod := CreateLaurPolElement(D, prodcoeffs, prodpowers);
  return prod;
end intrinsic;

intrinsic '*' (x::., y::RngLaurPolElt) -> RngLaurPolElt
  {Return x * y}
  D := Parent(y);
  b, z := IsCoercible(D,x);
  require b : "The first argument is not coercible to the parent of the second argument";
  return Multiply(z,y);
end intrinsic;

intrinsic '*'(x::RngLaurPolElt, y::.) -> RngLaurPolElt
  {Return x * y}
  D := Parent(x);
  b, z := IsCoercible(D,y);
  require b : "The first argument is not coercible to the parent of the second argument";
  return Multiply(x,z);
end intrinsic;

intrinsic '^'(x::RngLaurPolElt, n::RngIntElt) -> RngLaurPolElt
 {Return x^n}
  z := Parent(x)!x;
  if n lt 0 then
    z := CreateLaurPolElement(Parent(x),[1],[-1]);
    n := -n;
  end if;
  ans := Parent(x)!1;
  while n ne 0 do
    if (n mod 2) ne 0 then
      ans := ans*z;
      end if;
    z := z*z;
    n := Floor(n/2);
  end while;
  return ans;
end intrinsic;

intrinsic Evaluate(g::RngLaurPolElt, z::. : polynomial := true) -> .
  {evaluates g(z). If polynomial eq true, then we assume g is a polynomial. If g is not a polynomial, then y^(-1) needs to be defined or this will give errors}
  D := Parent(g);
  R := D`BaseRing;
  if IsCoercible(R,z) then
	y := R!z;
  elif Type(z) eq Type(R!0) and not IsCoercible(R,z) then
	error "Incompatible arguments: ", z, " not compatible to ", R;
  else
    y := z;
  end if;
  if polynomial then
    require g`powers[1] ge 0 : "g is not a polynomial";
  end if;
  if g`powers[1] lt 0 then
    try
      dummy_variable := y^(-1);
    catch e
      error "Error calling y^(-1): ", e`Object;
    end try;
  end if;

  Cg := g`coeffs;
  Pg := g`powers;

  ans := 0;
  for i in [1..#Cg] do
    ans +:= Cg[i]*y^Pg[i];
  end for;
  return ans;
end intrinsic;

intrinsic NormValuation(x::.) -> .
  {The valuation of x, normalised so that v(p) = 1}
  R := Parent(x);
  p := R!Prime(R);
  return Valuation(x)/Valuation(p);
end intrinsic;

intrinsic NormPrecision(x::.) -> RngIntElt
  {p-adic precision of x}
  prec := Precision(x);
  if Type(prec) eq Tup then
    prec := prec[2];
  end if;
  R := Integers();
  if Type(x) in [RngSerLaur, RngSerPow, FldPad] then
	R := x;
  else
    R := Parent(x);
  end if;
  p := R!Prime(R);
  return prec/Valuation(p);
end intrinsic;

function CreateSerAnnElement(D, coeffs, powers, v1, v2, v1AdicPrec, v2AdicPrec)
  // Create RngSerAnnElt with parent D and given Elements
  x := New(RngSerAnnElt);
  x`approx := CreateLaurPolElement(D`LaurPolRing, coeffs, powers);
  x`v1 := v1;
  x`v2 := v2;
  x`v1AdicPrec := v1AdicPrec;
  x`v2AdicPrec := v2AdicPrec;
  x`Parent := D;
  return Consolidate(x);
end function;

intrinsic Consolidate(z::RngSerAnnElt) -> RngSerAnnElt
  {Throw away zero-ish terms of z}
  x := New(RngSerAnnElt);
  zc := z`approx`coeffs;
  zp := z`approx`powers;
  xc := [];
  xp := [];
  for i in [1 .. #zp] do
    vpv1 := z`v1*zp[i] + NormValuation(zc[i]);
    vpv2 := z`v2*zp[i] + NormValuation(zc[i]);
    if vpv1 ge Minimum(z`v1AdicPrec,NormPrecision(z`Parent`BaseRing)) and vpv2 ge Minimum(z`v1AdicPrec,NormPrecision(z`Parent`BaseRing)) then
      continue;
    end if;
    Append(~xc, zc[i]);
    Append(~xp, zp[i]);
  end for;

  x`approx := CreateLaurPolElement(z`Parent`LaurPolRing, xc, xp);
  x`v1 := z`v1;
  x`v2 := z`v2;
  x`v1AdicPrec := z`v1AdicPrec;
  x`v2AdicPrec := z`v2AdicPrec;
  x`Parent := z`Parent;
  return x;
end intrinsic;

/* Special intrinsics for RngSerAnn */
intrinsic SeriesAnnulusRing(BaseRing::Rng, v1, v2, VariableName::MonStgElt : LaurPolRing := false) -> RngSerAnn
  {Create the direct product of given rings (a tuple)}
  D := New(RngSerAnn);
  D`BaseRing := BaseRing;
  D`v1 := v1;
  D`v2 := v2;
  D`VariableName := VariableName;
  D`p := Prime(BaseRing);
  if Type(LaurPolRing) eq RngLaurPol then
    D`LaurPolRing := LaurentPolynomialRing(BaseRing, VariableName);
  else
    D`LaurPolRing := LaurPolRing;
  end if;
  D`Generator := CreateSerAnnElement(D, [BaseRing!1],[1],v1,v2, Infinity(), Infinity());
  return D;
end intrinsic;

intrinsic SetPrecision(x::RngSerAnnElt, v1AdicPrec::., v2AdicPrec::.) -> RngSerAnnElt
  {Set the p-adic precision of the tails of x}
  x`v1AdicPrec := Min(x`v1AdicPrec, v1AdicPrec);
  x`v2AdicPrec := Min(x`v1AdicPrec, v2AdicPrec);
  return x;
end intrinsic;

intrinsic SetPrecisionV1(x::RngSerAnnElt, v1AdicPrec::.) -> RngSerAnnElt
  {Set the p-adic precision of the left tail of x}
  x`v1AdicPrec := Min(x`v1AdicPrec, v1AdicPrec);
  return x;
end intrinsic;

intrinsic SetPrecisionV2(x::RngSerAnnElt, v2AdicPrec::.) -> RngSerAnnElt
  {Set the p-adic precision of the right tail of x}
  x`v2AdicPrec := Min(x`v2AdicPrec, v2AdicPrec);
  return x;
end intrinsic;

intrinsic Print(x::RngSerAnn)
  {Print x}
  printf "Double Ended Laurent Series Field in %o over %o", x`VariableName, x`BaseRing;
end intrinsic;

intrinsic NormValuation(x::RngLaurPolElt, v::.) -> .
  {Given a point in the Berkovich space (represented as the valuation of the radius of a disk centered at 0),
  and x a Laurent polynomial, return the valuation of x}
  D := (x`Parent)`BaseRing;
  Cx := x`coeffs;
  return (#Cx gt 0) select Minimum([NormValuation(D!Cx[i]) + v*x`powers[i] : i in [1..#Cx]]) else Infinity();
end intrinsic;

intrinsic NormValuation(x::RngSerAnnElt, v::.) -> .
  {Given a point in the Berkovich space (represented as the valuation of the radius of a disk centered at 0),
  and x an annulus power series, return the valuation of x}
  require x`v1 ge v and v ge x`v2 : "v lies outside the annulus of convergence";
  return Minimum(NormValuation(x`approx, v), Minimum(x`v1AdicPrec, x`v2AdicPrec));;
end intrinsic;

intrinsic IsWeaklyZero(x::RngSerAnnElt) -> BoolElt
  {Check if x is weakly zero, i.e. if all coefficients are weakly zero.}
  return (NormValuation(x,x`v1) ge x`v1AdicPrec) and (NormValuation(x,x`v2) ge x`v2AdicPrec);
end intrinsic;

function CreateSerAnnEltFromPowerSeries(D, f, v1, v2)
  powers := [Precision(f)[1]-Precision(Parent(f)) .. Precision(f)[1] - 1];
  coeffs := [Coefficient(f, i) : i in powers];
  return CreateSerAnnElement(D, coeffs, powers, v1, v2, Infinity(), Infinity());
end function;

intrinsic Shrink(z::RngSerAnnElt, v1, v2) -> RngSerAnnElt
{Shrink x to live in the annulus v1 >= ... >= v2}
  x := Parent(z)!z;
  require x`v1 ge v1 and v2 ge x`v2 : "the provided annulus is not smaller than the original annulus";
  if x`v1 gt v1 then
	x`v1AdicPrec := Minimum(x`v1AdicPrec, x`v2AdicPrec);
	x`v1 := v1;
  end if;
  if v2 gt x`v2 then
	x`v2AdicPrec := Minimum(x`v1AdicPrec, x`v2AdicPrec);
	x`v2 := v2;
  end if;
  return x;
end intrinsic;

intrinsic IsCoercible(D::RngSerAnn, x::.) -> BoolElt, .
  {Return whether x is coercible into D and the result if so}
  R := D`BaseRing;
  if Type(x) eq RngSerAnnElt then
    return true, CreateSerAnnElement(D, x`approx`coeffs, x`approx`powers, x`v1, x`v2, x`v1AdicPrec, x`v2AdicPrec);
  end if;
  if IsCoercible(R, x) then
    coeffs := [R!x];
    powers := [0];
    y := CreateSerAnnElement(D, coeffs, powers, D`v1, D`v2, Infinity(), Infinity());
  return true, y;
    end if;
    if Type(x) in [RngSerPowElt, RngSerLaurElt] then
  return true, CreateSerAnnEltFromPowerSeries(D, x, D`v1, D`v2);
    end if;
  return false, "Not implemented";
end intrinsic;

intrinsic ChangeAbsolutePrecision(x::FldPadElt, prec::FldRatElt) -> FldPadElt
  {return x with the absolute precision set to prec}
  R := Parent(x);
  p := R!Prime(R);
  relPrec := Maximum(0,Floor(Valuation(p)*prec-Valuation(x)));
  prec := Minimum(RelativePrecision(x),relPrec);
  return ChangePrecision(x,prec);
end intrinsic;

intrinsic Coefficient(x::RngSerAnnElt, i::RngIntElt) -> .
  {Extract the ith coefficient}
  ans := Coefficient(x`approx, i);
  MaxAbsPrec := Max(-i*x`v1 + x`v1AdicPrec,-i*x`v2 + x`v2AdicPrec);
  ans := ChangeAbsolutePrecision(ans, MaxAbsPrec);
  return ans;
end intrinsic;

intrinsic Print(x::RngSerAnnElt)
  {Print x}
  printf "%o + eps where v_p^%o(eps) >= %o and v_p^%o(eps) >= %o", x`approx, x`v1, x`v1AdicPrec, x`v2, x`v2AdicPrec;
end intrinsic;

intrinsic Parent(x::RngSerAnnElt) -> RngSerAnn
  {Parent of x}
  return x`Parent;
end intrinsic;


intrinsic Add(x::RngSerAnnElt, y::RngSerAnnElt) -> RngSerAnnElt
  { Return x + y}
  D := Parent(x);
  require D cmpeq Parent(y): "Incompatible arguments";
  v1 := Min(x`v1, y`v1);
  v2 := Max(x`v2, y`v2);
  xs := Shrink(x, v1, v2);
  ys := Shrink(y, v1, v2);

  v1AdicPrec := Min(xs`v1AdicPrec, ys`v1AdicPrec);
  v2AdicPrec := Min(xs`v2AdicPrec, ys`v2AdicPrec);

  approx := xs`approx + ys`approx;
  return CreateSerAnnElement(D, approx`coeffs, approx`powers, v1, v2, v1AdicPrec, v2AdicPrec);
end intrinsic;

intrinsic '+'(x::., y::RngSerAnnElt) -> RngSerAnnElt
  {Return x + y}
  D := Parent(y);
  b, z := IsCoercible(D,x);
  require b : "The first argument is not coercible to the parent of the second argument";
  return Add(z,y);
end intrinsic;

intrinsic '+'(x::RngSerAnnElt, y::.) -> RngSerAnnElt
  {Return x + y}
  D := Parent(x);
  b, z := IsCoercible(D,y);
  require b : "The second argument is not coercible to the parent of the first argument";
  return Add(x,z);
end intrinsic;

intrinsic AdditiveInverse(z::RngSerAnnElt) -> RngSerAnnElt
  {return -x}
  x := Parent(z)!z;
  x`approx := AdditiveInverse(x`approx);
  return x;
end intrinsic;

intrinsic '-'(x::RngSerAnnElt) -> RngSerAnnElt
  {return -x}
  return AdditiveInverse(x);
end intrinsic;

intrinsic '-'(x::., y::RngSerAnnElt) -> RngSerAnnElt
  {Return x - y}
  D := Parent(y);
  b, z := IsCoercible(D,x);
  require b : "The first argument is not coercible to the parent of the second argument";
  return Add(z,AdditiveInverse(y));
end intrinsic;

intrinsic '-'(x::RngSerAnnElt, y::.) -> RngSerAnnElt
  {Return x - y}
  D := Parent(x);
  b, z := IsCoercible(D,y);
  require b : "The second argument is not coercible to the parent of the first argument";
  return Add(x,AdditiveInverse(z));
end intrinsic;

intrinsic Multiply(x::RngSerAnnElt, y::RngSerAnnElt) -> RngSerAnnElt
  {Return x * y}
  D := Parent(x);
  require D cmpeq Parent(y): "Incompatible arguments";

  v1 := Min(x`v1, y`v1);
  v2 := Max(x`v2, y`v2);
  xs := Shrink(x, v1, v2);
  ys := Shrink(y, v1, v2);

  xapprox := xs`approx;
  yapprox := ys`approx;
  xy := xapprox*yapprox;

  v1precx := xs`v1AdicPrec;
  v2precx := xs`v2AdicPrec;
  v1precy :=ys`v1AdicPrec;
  v2precy := ys`v2AdicPrec;

  v1xy := Maximum(ys`v1, xs`v1);
  v2xy := Minimum(ys`v2, xs`v2);

  //AB - A'B' = (A-A')B' + (B-B')A' + (A-A')(B-B')
  v1precxy := Min([v1precx + NormValuation(yapprox, v1xy), v1precy + NormValuation(xapprox, v1xy), v1precx + v1precy]);
  v2precxy := Min([v2precx + NormValuation(yapprox, v2xy), v2precy + NormValuation(xapprox, v2xy), v2precx + v2precy]);

  return CreateSerAnnElement(D, xy`coeffs, xy`powers, v1xy, v2xy, v1precxy, v2precxy);
end intrinsic;


intrinsic '*'(x::., y::RngSerAnnElt) -> RngSerAnnElt
  {Return x * y}
  D := Parent(y);
  b, z := IsCoercible(D,x);
  require b : "The first argument is not coercible to the parent of the second argument";
  return Multiply(z,y);
end intrinsic;

intrinsic '*'(x::RngSerAnnElt, y::.) -> RngSerAnnElt
  {Return x * y}
  D := Parent(x);
  b, z := IsCoercible(D,y);
  require b : "The second argument is not coercible to the parent of the first argument";
  return Multiply(x,z);
end intrinsic;

intrinsic '/'(x::RngSerAnnElt, y::.) -> RngSerAnnElt
  {Return x / y}
  D := Parent(x);
  R := D`BaseRing;
  require IsCoercible(R, y) : "y needs to be a scalar";
  require not IsWeaklyZero(R!y) : "you cannot divide by something that's (weakly) zero";
  return Multiply(x,D!((R!y)^(-1)));
end intrinsic;

intrinsic Decomposition(z::RngSerAnnElt) -> ., RngSerAnnElt, RngIntElt
  {Write z as c*(1+a)*x^n, where c is a constant, a is an element of v1-valuation and v2-valuation bigger than zero, and n is an integer. This assumes z has no zeroes on the annulus. Return c, a, n}
  require not IsWeaklyZero(z) : "The input is weakly zero";
  zc := z`approx`coeffs;
  zp := z`approx`powers;
  v1 := z`v1;
  v2 := z`v2;
  minv1ind := 1;
  minv1val := NormValuation(zc[1]) + v1*zp[1];
  minv2ind := 1;
  minv2val := NormValuation(zc[1]) + v2*zp[1];
  zero_on_edge1 := false;
  zero_on_edge2 := false;
  for i in [2 .. #zc] do
	new1val := NormValuation(zc[i]) + v1*zp[i];
	new2val := NormValuation(zc[i]) + v2*zp[i];
    if new1val eq minv1val then
	  zero_on_edge1 := true;
	elif new1val le minv1val then
	  zero_on_edge1 := false;
	  minv1val := new1val;
	  minv1ind := i;
	end if;
    if new2val eq minv2val then
	  zero_on_edge2 := true;
	elif new2val le minv2val then
	  zero_on_edge2 := false;
	  minv2val := new2val;
	  minv2ind := i;
	end if;
  end for;
  require not zero_on_edge1 : "The input has a zero with valuation v1";
  require not zero_on_edge2 : "The input has a zero with valuation v2";
  require minv1ind eq minv2ind : "The input has a zero inside the annulus";
  require minv1val le z`v1AdicPrec : "Due to precision, the input might have a zero with valuation v1";
  require minv2val le z`v2AdicPrec : "Due to precision, the input might have a zero with valuation v2";
  n := zp[minv1ind];
  c := zc[minv1ind];
  zp := [i - n : i in zp];
  zc := [i/c : i in zc];
  newz := CreateSerAnnElement(Parent(z), zc, zp, v1, v2, z`v1AdicPrec - n*v1 - NormValuation(c), z`v2AdicPrec - n*v2 - NormValuation(c));
  return c, newz-1, n;
end intrinsic;

intrinsic Inverse(x::RngSerAnnElt) -> RngSerAnnElt
{return x^(-1)}
  D := x`Parent;
  c, u, n := Decomposition(x);
  ans := D!0;
  powu := D!1;
  for i in [0 .. Ceiling(Minimum(Minimum(Ceiling(x`v2AdicPrec),Ceiling(x`v1AdicPrec)),NormPrecision(x`Parent`BaseRing))/Minimum(NormValuation(u,x`v1),NormValuation(u,x`v2)))] do
    ans := ans + powu;
	powu := -powu*u;
  end for;
  ans := SetPrecision(ans, NormPrecision(x`Parent`BaseRing), NormPrecision(x`Parent`BaseRing));
  z := c^(-1) * ans;
  zp := [i - n : i in z`approx`powers];
  newz := CreateSerAnnElement(Parent(z), z`approx`coeffs, zp, z`v1, z`v2, z`v1AdicPrec - n*z`v1, z`v2AdicPrec - n*z`v2);
  return newz;
end intrinsic;

intrinsic '^'(x::RngSerAnnElt, n::RngIntElt) -> RngSerAnnElt
 {Return x^n}
  z := Parent(x)!x;
  if n lt 0 then
    z := Inverse(z);
	n := -n;
  end if;
  ans := Parent(x)!1;
  while n ne 0 do
    if (n mod 2) ne 0 then
      ans := ans*z;
      end if;
    z := z*z;
    n := Floor(n/2);
  end while;
  return ans;
end intrinsic;

intrinsic SquareRoot(x::RngSerAnnElt : inverse := false, wellDefinedCheck := true) -> RngSerAnnElt
  {Return the square root of x. If inverse eq true, then returns sqrt(x)^(-1). Assumes that in the decomposition of x, the constant is 1}
  c, a, n := Decomposition(x);
  if wellDefinedCheck then
    require NormValuation(c-1) gt 0 : "Square root of the constant factor from the decomposition is not well defined";
  end if;
  require (n mod 2) eq 0 : "The degree from the decomposition is not even";
  sign := inverse select -1 else 1;
  return SquareRoot(c)^sign * SquareRootOnePlusEps(1+a : inverse := inverse) * (x`Parent`Generator)^(sign * Integers()!(n/2));
end intrinsic;

intrinsic SquareRootOnePlusEps(x::RngSerAnnElt : inverse := false) -> RngSerAnnElt
  {Return the square root of x. If inverse eq true, then returns sqrt(x)^(-1). Assumes x = 1 + u, with v_1(u), v_2(u) > 0}
  u := x-1;
  v1 := x`v1;
  v2 := x`v2;
  require NormValuation(u, v1) gt 0 and NormValuation(u, v2) gt 0 : "x needs to be 1 + u where eps has positive valuation";
  binomial := 1;
  answer := (x`Parent)!0;
  powu := 1;
  for i in [0 .. Ceiling(Minimum(Minimum(Ceiling(x`v2AdicPrec),Ceiling(x`v1AdicPrec)),NormPrecision(x`Parent`BaseRing))/Minimum(NormValuation(u,v1),NormValuation(u,v2)))] do
    answer := answer + binomial*powu;
    binomial := binomial*((inverse select -1/2 else 1/2)-i)/(i+1);
    powu := powu*u;
  end for;
  newprec := Minimum([x`v1AdicPrec, x`v2AdicPrec, NormPrecision(x`Parent`BaseRing)]);
  answer := SetPrecision(answer, newprec, newprec);
  return answer;
end intrinsic;

intrinsic Integrate(x::RngLaurPolElt : ignoreMinOne := false) -> RngLaurPolElt
  {Return the integral of x}
  newc := [];
  newp := [];
  for i in [1 .. #x`coeffs] do
    if x`powers[i] eq -1 then
      require ignoreMinOne or IsWeaklyZero(x`coeffs[i]) : "Trying to integrate x^(-1)";
      continue;
    end if;
    Append(~newc, x`coeffs[i]/(x`powers[i] + 1));
    Append(~newp, x`powers[i] + 1);
  end for;
  c := CreateLaurPolElement(x`Parent, newc, newp);
  return c;
end intrinsic;

function MinFuncValue(eps, p)
  // Return the minimum value of eps * i - v_p(i) for i positive
  // This minimum is achieved when i = p^k is a power of p, and eps * p^k is not bigger than k + 1
  k := 0;
  MinEpsI := eps;
  while eps*p^k le k+1 do
    MinEpsI := Minimum(MinEpsI, eps*p^k - k);
    k := k+1;
  end while;
  return MinEpsI;
end function;

intrinsic Integrate(x::RngSerAnnElt : eps := false) -> RngSerAnnElt
  {Return}
  require Type(eps) in [BoolElt, FldRatElt, RngIntElt] : "eps needs to be left empty or be a rational number";
  p := x`Parent`p;
  if Type(eps) eq BoolElt then
    eps := 1/p;
  end if;

  newapprox := Integrate(x`approx);
  v1 := x`v1;
  v2 := x`v2;
  newv1 := x`v1 - eps;
  newv2 := x`v2 + eps;
  //while (newv1 le 0) or (newv2 le 0) or newv1 lt newv2 do
  while newv1 lt newv2 do
    eps := eps*1/p; //decrease eps to make positive radii
    newv1 := x`v1 - eps;
    newv2 := x`v2 + eps;
  end while;

  newV1Prec := Minimum(x`v1AdicPrec + v1 - MinFuncValue(eps, p), x`v2AdicPrec - MinFuncValue(v1-eps-v2, p) + v2);
  newV2Prec := Minimum(x`v2AdicPrec + v2 - MinFuncValue(eps, p), x`v1AdicPrec - MinFuncValue(v1-eps-v2, p) + v1);
  return CreateSerAnnElement(x`Parent, newapprox`coeffs, newapprox`powers, newv1, newv2, newV1Prec, newV2Prec);
end intrinsic;


intrinsic Evaluate(g::RngSerAnnElt, z::. : polynomial := true) -> .
  {evaluates g(z). If polynomial eq true, then we assume g is a polynomial. If g is not a polynomial, then y^(-1) needs to be defined or this will give errors}
  D := Parent(g);
  R := D`LaurPolRing;
  B := R`BaseRing;

  require IsCoercible(D,z) : "z is not coercible to the parent of g";
  z := D!z;

  //require z`v1AdicPrec eq Infinity() and z`v2AdicPrec eq Infinity() : "the element in which we're evaluating needs to be a polynomial";
  gv1 := g`v1;
  gv2 := g`v2;
  zv1 := z`v1;
  zv2 := z`v2;
  zc := z`approx`coeffs;
  zp := z`approx`powers;
  c, a, n := Decomposition(z);
  // This means that z achieves the possible valuations [v_p(c) + n*zv_1, v_p(c) + n*zv_2] on the annulus [v_1, v_2]
  require gv1 ge NormValuation(c) + n*zv1 and NormValuation(c) + n*zv1 ge gv2 : "the power series are not composable on the given annuli";
  require gv1 ge NormValuation(c) + n*zv2 and NormValuation(c) + n*zv2 ge gv2 : "the power series are not composable on the given annuli";


  gapprox := g`approx;

  Cg := gapprox`coeffs;
  Pg := gapprox`powers;

  ans := CreateSerAnnElement(Parent(z), [], [], zv1, zv2, Infinity(), Infinity());;
  if #Cg eq 0 then
    return ans;
  end if;
  //powz := z^Pg[1];
  neg_pows := [i : i in Pg | i lt 0];
  pos_pows := [i : i in Pg | i ge 0];
  nn := #neg_pows;
  np := #pos_pows;
  if nn ne 0 then
	invz := z^(-1);
    powz := invz^(-Pg[nn]);
	ans +:= Cg[nn]*powz;
	for i in [1 .. nn-1] do
      for j in [1 .. - Pg[nn-i] + Pg[nn-i+1]] do
        powz := powz * invz;
	  end for;
	  ans +:= Cg[nn-i]*powz;
	end for;
  end if;
  if np ne 0 then
    powz := z^Pg[nn+1];
	ans +:= Cg[nn+1]*powz;
	for i in [nn + 2 .. #Cg] do
	  for j in [1 .. Pg[i] - Pg[i-1]] do
	    powz := powz * z;
	  end for;
	  ans +:= Cg[i]*powz;
	end for;
  end if;

  ans := SetPrecision(ans, Minimum(g`v1AdicPrec, g`v2AdicPrec), Minimum(g`v1AdicPrec, g`v2AdicPrec));
  return ans;
end intrinsic;
