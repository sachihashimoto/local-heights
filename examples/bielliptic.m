//Bielliptic example 

AttachSpec("../spec");
SetVerbose("LocalHeights", 2);
SetVerbose("EndoCheck", 1);
R_Q<x> := PolynomialRing(Rationals());
f := (x^2 -7^2)*((x-1)^2 - 7)*((x+1)^2 -7); p := 7; //bielliptic q = 7, alpha = 2, beta = 1
M := Matrix(Rationals(),[[-1, 0], [0, 1]]);

cd := ClusterData(f, p : prec := 50);
clusters := cd`Clusters;
G := ConstructDualGraph(cd);
AssignSquareRoots(cd);
X := HyperellipticCurve(f);

time hts := HeightsAtRationalPoints(G, M, X: basept:=3);
print "Check value of local height at point is -2/5:", 2/5+(Qp!hts[1][2]);