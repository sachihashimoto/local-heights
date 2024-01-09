print "Computing heights for X_0(93,1)/w_93 at p = 3";
AttachSpec("../spec");
SetVerbose("LocalHeights", 2);
SetVerbose("EndoCheck", 1);
R_Q<x> := PolynomialRing(Rationals());

f := x^6 +2*x^4 +6*x^3 +5*x^2-6*x+1;
p := 3;
X := HyperellipticCurve(f);
print "A model for the curve is y^2 = ",f;
//(* * (* *)_1 (* *)_1)_0
basept := 1;
cd := ClusterData(f, p : prec := 50);
clusters := cd`Clusters;
G := ConstructDualGraph(cd);
AssignSquareRoots(cd);

M := FindEndoMatrix(X : tracezero := true);
print "We choose the endomorphism \n", M;
print "We use the code from HeightsAtRationalPoints(G, M, X), but print more information";

edges := G`Edges;
vertices := G`Vertices;
edgescoords := G`EdgesCoordinates;
allEdges := G`EdgesCoordinates;
genuslist := G`Genus;
fL := cd`Fss;
clusters := cd`Clusters;
anyedge := edgescoords[1];

ComputeDirectionalDerivative := function(poly,edge,vertex)
  //edge is <vertex,cluster,length>
  R<s> := Parent(poly);
  deriv:= -Evaluate(Derivative(poly),0);
  return deriv;
end function;

homologyBasis := HomologyDualGraph(G);
assert #homologyBasis ne 0;

g := (Degree(fL) - 2) div 2;

complement_span := ComplementOfSpanningTree(G);
if #complement_span eq 0 then
  error "There is no action";
end if;

residues :=[];
for e in complement_span do
  ci := EdgeFromCoords(e,G)[2];
  if IsEven(#clusters[ci]) then
      vprintf LocalHeights, 2 : "Computing residue of %o.\n", clusters[ci];
      Append(~residues, EvenResidue(ci, cd));
    else
      Append(~residues, OddResidue(ci,cd));
    end if;
end for;
small_residues := [row[1..g] : row in residues];

res := Matrix(small_residues);
tr := Trace(M);
assert IsZero(tr);// "Must use a trace 0 endomorphism"

print "The matrix of phi_2 is\n", res;
assert Valuation(BaseField(Parent(res[1][1]))!((res[1][1]+306630590263)/BaseField(Parent(res[1][1])).1) +7) ge 3;
assert Valuation(BaseField(Parent(res[1][2]))!((res[1][2]-187945877234)/BaseField(Parent(res[1][2])).1) -2) ge 3;
assert Valuation(BaseField(Parent(res[2][2]))!((res[2][2]+118684713029)/BaseField(Parent(res[1][2])).1) +5) ge 3;

ZonHomGraph := DescendEndomorphism(M,res);
print "And we obtain the action of Z on the dual graph: \n", ZonHomGraph;

print "Using the orthogonal basis";
orthogbasis, change_of_basis := GramSchmidtProcess(homologyBasis, G);
print orthogbasis;

C := Matrix(2,2,[LengthPairing(orthogbasis[i],orthogbasis[j],G): i, j in [1,2]]);
print "The intersection pairing matrix on the orthogonal basis is \n",C;

function CoefficientProjection(v, u, G)
  if &and[IsZero(e[1]) : e in u] then
    return 0;
  end if;
  num := LengthPairing(v, u, G);
  den := LengthPairing(u, u, G);
  return  num/den;
end function;

mu_F := [];
for e in allEdges do
  print "The projection of ", e, "has coefficients ", [CoefficientProjection([<1,e>],b,G) : b in orthogbasis];
  Fstarpie := ComputeFstar(homologyBasis, [<1,e>], G, ZonHomGraph);
  len_e := EdgeFromCoords(e,G)[3];
  pair := 2*LengthPairing([<1,e>],Fstarpie,G)*1/len_e^2;
  Append(~mu_F,pair);
end for;

print "The Laplacian of the height (on ds_e, without the traces) is ", mu_F;

higherGenusVertices := [v : i in [1..#vertices]| genuslist[v[1]] ge 1 where v is vertices[i]];
assert #higherGenusVertices eq 0;
print "There are no higher genus vertices";

allTraces := [*0 : i in [1..#vertices]*];

assert IsZero(&+[mu_F[i]*EdgeFromCoords(e,G)[3]:i -> e in allEdges] + tr); //the total mass

_<s> := PolynomialRing(Parent(mu_F[1]));
f0 := [-mu_F[i]/2 * s * (s - EdgeFromCoords(allEdges[i],G)[3]) : i in [1..#allEdges]];
print "The piecewise polynomial f0 is, ", f0;

deltas := [];
for v in [1..#vertices] do
  adjEdg := FindAdjacentEdges(v,G);
  deltav := -&+[ComputeDirectionalDerivative(f0[Index(allEdges,e)],EdgeFromCoords(e,G),v): e in adjEdg];
  Append(~deltas, deltav);
end for;
print "The delta measures are ", deltas;
deltas := [deltas[i] + allTraces[i] : i in [1..#vertices]];

Q := WeightedLaplacianMatrix(G);
print "The weighted laplacian is ", Q;

E,T := EchelonForm(Q);
deltasMat := Matrix([deltas]);
if BaseRing(deltasMat) cmpeq Integers() then
  Tdelta := ChangeRing(T,Rationals())*Transpose(ChangeRing(deltasMat,Rationals()));
else
  Tdelta := ChangeRing(T,BaseRing(deltasMat))*Transpose(deltasMat);
end if;
print "The solution for L*vector=deltas is vector = ", Tdelta;

if not(BaseRing(Tdelta) cmpeq Parent(f0[1])) then
  _<s> := PolynomialRing(BaseRing(Tdelta));
  f0 := [ChangeRing(f0[i], BaseRing(Tdelta)) :i in [1..#f0]];
end if;

f1 := [];
for e in allEdges do
  edg := EdgeFromCoords(e,G);
  f1base := Tdelta[e[1]][1];
  f1end := Tdelta[edg[1]][1];
  Append(~f1,(f1end-f1base)/edg[3]*s + f1base);
end for;
print "The polynomial f1 is ", f1;

//Now adjust so the function is 0 at the basepoint
edgesBasepoint := FindAdjacentEdges(basept,G);
eBasepoint := edgesBasepoint[1];
index := Index(allEdges,eBasepoint);
if basept eq eBasepoint[1] then //evaluate at 0
  constant := Evaluate(f1[index],0);
else
  len := EdgeFromCoords(eBasepoint,G)[3]; //eval at len
  constant := Evaluate(f0[index],len) + Evaluate(f1[index],len);
end if;
f1 := [ff - constant : ff in f1];
print "After adjusting for the base point, f1' = ", f1;

//return something in the same format as G`Edges (not allEdges)
htlist := [[] : v in vertices];
for i->e in allEdges do
  Append(~htlist[e[1]], f0[i] + f1[i]); //f0, f1 are indexed by all edges
  //need to do this in order of e[2], but allEdges is already in this order
end for;

print "The local heights are ", htlist;

ht_fn := htlist;
d := LCM([Denominator(c): c in Coefficients(f)]);
Xprime := HyperellipticCurve(f* d^2);
b, phi := IsIsomorphic(Xprime, X);
pts := RationalPoints(Xprime : Bound := 1000);
Qpoints := [phi(pt) : pt in pts];
reds := [* ReducePointToDualGraph(P0,G) : P0 in Qpoints *];
htsatpoints := [];
for i->red in reds do
  if red[3] eq "v" then  //P0 reduces to a vertex
    v := Index(vertices, [red[1],red[2]]);
    adj_edg := FindAdjacentEdges(v, G);
    e := adj_edg[1];
    jz := ht_fn[e[1]][e[2]];
    if EdgeFromCoords(e,G)[1] eq v then
      len := edges[e[1]][e[2]][3];
      evalatP := Evaluate(jz, len);
    else
      evalatP := Evaluate(jz, 0);
    end if;
  else //P0 reduces to a point on an edge
    e := red[1];
    jz := ht_fn[e[1]][e[2]];
    dist := red[2];
    evalatP := Evaluate(jz, dist);
  end if;
  Append(~htsatpoints, [* Qpoints[i], evalatP *]);
end for;
print "The values at known rational points are ", htsatpoints;
