print "We compute local heights on the modular curves X0(N)∗, the Atkin–Lehner quotients of X0(N)";

AttachSpec("../spec");
SetVerbose("LocalHeights", 2);
SetVerbose("EndoCheck", 0);
R_Q<x> := PolynomialRing(Rationals());

print "********************\n N = 330\n********************"; f :=  x^6 + 8*x^4 + 10*x^3 + 20*x^2 + 12*x + 9; p := 3; print "p = ",p;

// print "********************\n N = 255\n********************"; f := x^6 - 4*x^5 - 12*x^4 + 2*x^3 + 8*x^2 - 4*x + 1; p := 5; print "p = ",p;

// print "********************\n N = 147\n********************"; f := (x^2 - x + 1)*(x^4 + x^3 - 4*x^2 - 3*x + 9); p := 3;
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
Z := false;

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
print "The basis for the homology is ", homologyBasis;

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

ZonHomGraph := DescendEndomorphism(M,res);
print "And we obtain the action of Z on the dual graph: \n", ZonHomGraph;

orthogbasis, change_of_basis := GramSchmidtProcess(homologyBasis, G);

C := Matrix(2,2,[LengthPairing(orthogbasis[i],orthogbasis[j],G): i, j in [1,2]]);

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
  Fstarpie := ComputeFstar(homologyBasis, [<1,e>], G, ZonHomGraph);
  len_e := EdgeFromCoords(e,G)[3];
  pair := 2*LengthPairing([<1,e>],Fstarpie,G)*1/len_e^2;
  Append(~mu_F,pair);
end for;

higherGenusVertices := [v : i in [1..#vertices]| genuslist[v[1]] ge 1 where v is vertices[i]];

allTraces := [*0 : i in [1..#vertices]*];

assert IsZero(&+[mu_F[i]*EdgeFromCoords(e,G)[3]:i -> e in allEdges] + tr); //the total mass

_<s> := PolynomialRing(Parent(mu_F[1]));
f0 := [-mu_F[i]/2 * s * (s - EdgeFromCoords(allEdges[i],G)[3]) : i in [1..#allEdges]];

deltas := [];
for v in [1..#vertices] do
  adjEdg := FindAdjacentEdges(v,G);
  deltav := -&+[ComputeDirectionalDerivative(f0[Index(allEdges,e)],EdgeFromCoords(e,G),v): e in adjEdg];
  Append(~deltas, deltav);
end for;
deltas := [deltas[i] + allTraces[i] : i in [1..#vertices]];

Q := WeightedLaplacianMatrix(G);

E,T := EchelonForm(Q);
deltasMat := Matrix([deltas]);
if BaseRing(deltasMat) cmpeq Integers() then
  Tdelta := ChangeRing(T,Rationals())*Transpose(ChangeRing(deltasMat,Rationals()));
else
  Tdelta := ChangeRing(T,BaseRing(deltasMat))*Transpose(deltasMat);
end if;

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

//return something in the same format as G`Edges (not allEdges)
htlist := [[] : v in vertices];
for i->e in allEdges do
  Append(~htlist[e[1]], f0[i] + f1[i]); //f0, f1 are indexed by all edges
  //need to do this in order of e[2], but allEdges is already in this order
end for;

assert &and[&and[IsWeaklyZero(h) : h in hv] : hv in htlist | #hv ne 0];
print "The local heights are 0";
