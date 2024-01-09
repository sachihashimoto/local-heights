AttachSpec("../spec");
SetVerbose("LocalHeights", 2);
SetVerbose("EndoCheck", 0);
R_Q<x> := PolynomialRing(Rationals());

f:= x^6 + 18/5*x^4 + 6/5*x^3 + 9/5*x^2 + 6/5*x + 1/5;
// p := 3; basept := 1; traces := [8,-8];
p := 5; basept := 2; traces := [];

cd := ClusterData(f, p : prec := 60);
clusters := cd`Clusters;
G := ConstructDualGraph(cd);
AssignSquareRoots(cd);
X := HyperellipticCurve(f);
M := FindEndoMatrix(X : tracezero := false);
Z, degs := MatrixH1DR(X, M);
Z0 := -4*MakeTraceZero(Z);
M := -4*FindEndoMatrix(X : tracezero := true);

Z := Z0;

print "We chose the endomorphism";
print Z0;

ComputeDirectionalDerivative := function(poly,edge,vertex)
  //edge is <vertex,cluster,length>
  R<s> := Parent(poly);
  deriv:= -Evaluate(Derivative(poly),0);
  return deriv;
end function;

genuslist := G`Genus;
edges := G`Edges;
vertices := G`Vertices;
allEdges := G`EdgesCoordinates;
cd := G`ClusterDiagram;
edges := G`Edges;
vertices := G`Vertices;
edgescoords := G`EdgesCoordinates;
anyedge := edgescoords[1];
f := cd`F;
clusters := cd`Clusters;
childrenOfClusters := cd`Children;
depthClusters := cd`AbsoluteDepths;
fL := cd`Fss;


mu_F := LaplacianOfHeight(G,M);

//now if we have higher genus components, we have to add these in
higherGenusVertices := [v : i in [1..#vertices]| genuslist[v[1]] ge 1 where v is vertices[i]];
highergenusvertices := higherGenusVertices;

function FindBlocks(M, gvlist)
  blocks := [];
  start := 1;
  for v in [1..#gvlist] do
    B := Submatrix(M, [start, start+gvlist[v]*2-1], [start, start+gvlist[v]*2-1]);
    start := start+gvlist[v]*2-1+1;
    Append(~blocks,B);
  end for;
  return blocks;
end function;

if traces eq [] then
  if #highergenusvertices eq 0 then
    traces := [];
  else
    L := BaseRing(fL);
    prec := Precision(BaseRing(L));

    gvlist := [genuslist[v[1]] : v in highergenusvertices];

    clusterindices := [v[1] : v in highergenusvertices];

    globalres0, inclusion := ResidueZeroDifferentials(cd); //ker(phi2)
    allroots := Roots(fL);

    sqrtsgs := cd`SquareRootsgs;
    params := cd`AnnulusParameters;
    AllM1ToXv := [];
    for k->clusterIndex in clusterindices do

      sqrtg := sqrtsgs[clusterIndex];
      localres0 := XsBasisDeRham(sqrtg,clusterIndex, cd, gvlist[k], prec);

      globsymbvect := [];
      for i in [1 ..Nrows(globalres0)] do
        Append(~globsymbvect, []);
        for j in [1..#localres0] do
          vprintf LocalHeights, 2: "Computing global symbol of omega%o paired with eta%o (on X_s for cluster %o).\n", i, j, clusters[clusterIndex];
          Append(~globsymbvect[i], GlobalSymbol1(globalres0[i],localres0[j],clusterIndex, cd) );
        end for;
      end for;

      globalsymbmatrix := [];
      for i in [1 .. #localres0] do
        Append(~globalsymbmatrix, []);
        for j in [1 .. #localres0] do
          vprintf LocalHeights, 2: "Computing global symbol of eta%o paired with eta%o (on X_s for cluster %o).\n", i, j, clusters[clusterIndex];
          gs := GlobalSymbol2(localres0[i],localres0[j],clusterIndex,cd);
          if IsZero(gs) and j ne 1 then
          //magma is a disaster at precision and coercion, so we do a hacky workaround
            Append(~globalsymbmatrix[i], 0);
          else
            Append(~globalsymbmatrix[i],gs);
          end if;
        end for;
      end for;

      GSM := Matrix(globalsymbmatrix);
      MdrtoXv := [];
      for i in [1 .. Nrows(globalres0)] do
        vec := Transpose(Matrix([globsymbvect[i]])); //This is omegai paired with etas through #localres0
        ans := GSM^(-1)*ChangeRing(vec, BaseRing(GSM));
        Append(~MdrtoXv, Eltseq(ans));
      end for;
      MdrtoXv := Transpose(Matrix(MdrtoXv));

      Append(~AllM1ToXv, MdrtoXv);

      assert Nrows(MdrtoXv) eq 2*gvlist[k];
      vprintf LocalHeights, 2: "Matrix of M1 H^1dr(X) to H^1(X_v) %o\n for cluster %o.\n", MdrtoXv, clusters[clusterIndex];
    end for;
    directSum := VerticalJoin([M : M in AllM1ToXv]);
    ZonM1 := RightInverseMatrixFixed(inclusion)*ChangeRing(Z,BaseRing(inclusion))*inclusion;
    matrix := DescendEndomorphism(ZonM1,directSum);
    blocklist := FindBlocks(matrix, gvlist);
    print "The block matrices that we obtain are ",blocklist;
    traces := [Trace(B) : B in blocklist];
    print "Yielding the traces ", traces;
    if #traces ge 1 then
      print "****************\n\n";
      print "Change traces to ", traces, "and rerun the code";
      print "\n\n****************";
    end if;
  end if;
end if;

allTraces := [*0 : i in [1..#vertices]*];
tr := 0;
for i in [1 .. #higherGenusVertices] do
  allTraces[higherGenusVertices[i][1]] := traces[i];
  tr +:= traces[i];
end for;

assert IsZero(&+[mu_F[i]*EdgeFromCoords(e,G)[3]:i -> e in allEdges] + tr);

//mu_F = f0 + f1, where f0=C * s*(s- length)

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
check := ChangeRing(Q, Parent(Tdelta[1][1]))*Tdelta;
assert &and[IsWeaklyZero(check[i][1] - Transpose(Matrix([deltas]))[i][1]): i in [1..Nrows(check)]];

//these don't necessarily have the same base ring, so try to coerce to the same base ring

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

ht_fn := htlist;

print "The height function is";
print ht_fn;

X := HyperellipticCurve(f);
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
htsatpoints;
