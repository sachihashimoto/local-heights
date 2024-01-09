AttachSpec("../spec");
SetVerbose("LocalHeights", 3);
SetVerbose("EndoCheck", 1);
R_Q<x> := PolynomialRing(Rationals());

f := x^16 - 4*x^8 + 16; p := 3;
//https://beta.lmfdb.org/ModularCurve/Q/48.144.7.bgo.1/

cd := ClusterData(f, p : prec := 50);
clusters := cd`Clusters;
G := ConstructDualGraph(cd);
AssignSquareRoots(cd);
X := HyperellipticCurve(f);
M := FindEndoMatrix(X : tracezero := true);
print "The endomorphism is", M;

Qpoints := RationalPoints(X : Bound := 1000);
reds := [* ReducePointToDualGraph(P0,G) : P0 in Qpoints *];
//all known points reduces to the same vertex

edges := G`Edges;
g := 7;

complement_span := ComplementOfSpanningTree(G);


//Run this to check that the following matrix, ZonHomGraphQQ, is correct:

// residues :=[];
// for e in complement_span do
// ci := EdgeFromCoords(e,G)[2];
// if IsEven(#clusters[ci]) then
//     printf "Computing residue of %o.\n", clusters[ci];
//     Append(~residues, EvenResidue(ci, cd));
//   else
//     Append(~residues, OddResidue(ci,cd));
//   end if;
// end for;
// small_residues := [row[1..g] : row in residues];
// res_mat := Matrix(small_residues);
// ZonHomGraph := DescendEndomorphism(M, res_mat);
ZonHomGraphQQ := Matrix(Rationals(),
[
[ 4, 0, 7, 7, 0, 7, 7 ],
[ 0, 4, 7, 7, 0, 7, 7 ],
[ 0, 0, -3, -7, 0, -7, -7 ],
[ 0, 0, -7, -3, 0, -7, -7 ],
[ 0, 0, 7, 7, 4, 7, 7 ],
[ 0, 0, -7, -7, 0, -3, -7 ],
[ 0, 0, -7, -7, 0, -7, -3 ]
]);

//Here we can check.
// print "This is a good approximation by integers," ZonHomGraph-ZonHomGraphQQ;

allEdges := G`EdgesCoordinates;

homologyBasis := HomologyDualGraph(G);

mu_F := [];
for e in allEdges do
	Fstarpie := ComputeFstar(homologyBasis, [<1,e>], G, ZonHomGraphQQ);
	len_e := EdgeFromCoords(e,G)[3];
	pair := 2*LengthPairing([<1,e>],Fstarpie,G)*1/len_e^2;
	Append(~mu_F,pair);
end for;

assert IsZero(&+[mu_F[i]*EdgeFromCoords(e,G)[3]:i -> e in allEdges]);


basept := 9;

ComputeDirectionalDerivative := function(poly,edge,vertex)
//edge is <vertex,cluster,length>
	R<s> := Parent(poly);
	deriv:= -Evaluate(Derivative(poly),0);
	return deriv;
end function;

vertices := G`Vertices;

_<s> := PolynomialRing(Parent(mu_F[1]));
f0 := [-mu_F[i]/2 * s * (s - EdgeFromCoords(allEdges[i],G)[3]) : i in [1..#allEdges]];

deltas := [];
for v in [1..#vertices] do
adjEdg := FindAdjacentEdges(v,G);
deltav := -&+[ComputeDirectionalDerivative(f0[Index(allEdges,e)],EdgeFromCoords(e,G),v): e in adjEdg];
Append(~deltas, deltav);
end for;
vprintf LocalHeights, 2: "The delta measures are %o.\n", deltas;
deltas := [deltas[i]  : i in [1..#vertices]];

Q := WeightedLaplacianMatrix(G);
print "The weighted Laplacian", Q;
E,T := EchelonForm(Q);
deltasMat := Matrix([deltas]);
if BaseRing(deltasMat) cmpeq Integers() then
Tdelta := ChangeRing(T,Rationals())*Transpose(ChangeRing(deltasMat,Rationals()));
else
Tdelta := ChangeRing(T,BaseRing(deltasMat))*Transpose(deltasMat);
end if;
check := ChangeRing(Q, Parent(Tdelta[1][1]))*Tdelta;
assert &and[IsWeaklyZero(check[i][1] - Transpose(Matrix([deltas]))[i][1]): i in [1..Nrows(check)]];


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

print "The height functions are", htlist;
