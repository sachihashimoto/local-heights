_<x>:=PolynomialRing(Rationals());
X := HyperellipticCurve(1/5*x^6 + 6/5*x^5 + 9/5*x^4 + 6/5*x^3 + 18/5*x^2 + 1);

load "coleman.m";
load "symplectic_basis.m";
load "hecke_correspondence.m";
load "hodge.m";
load "frobenius.m";
load "heights.m";
load "qc_init_g2.m";

f := HyperellipticPolynomials(X);
H :=  HyperellipticCurve(25*f);
ptsH := Points(H:Bound:=1000);
_, rho := IsIsomorphic(H,X);
ptsX := [rho(P): P in ptsH];
J := Jacobian(H);

torsion_bas, torsion_orders, bas := generators(J);
basX := [Pullback(rho^(-1), bas[i]):i in [1,2]];

function normalizeList(list)
  //given a divisor in list form, remove anything of the form (+1, P), (-1,P) that can be canceled and the elements with coefficients 0.
  newlist:=[];
  for pair1 in list do
    pt := pair1[2];
    numofpt := 0;
    for pair2 in list do
      if pair2[2] eq pt then
        numofpt := numofpt + pair2[1];
      end if;
    end for;
    Append(~newlist, <numofpt, pt>);
  end for;
  newlist:=Set(newlist); //get rid of duplicates
  newList:=SetToSequence(newlist);
  return [pair:pair in newList|pair[1] ne 0];
end function;


function divisorAsSumOfPoints(D,points:bound:=10, numberPoints := 6)
  // Input: divisor D of degree 0 as a Jacobian point
  // Output: list of rational points and coefficients that D is equivalent to
  for i in [2..Ceiling(numberPoints/2)] do
    numberOfPoints := i*2;
    points4 := CartesianPower(points, numberOfPoints);
    listCoeff := [i: i in ([0..bound] cat [-bound..-1])];
    coeff := CartesianPower(listCoeff, i);
    for t in points4 do
      for c in coeff do
        divisor := &+[c[j]*(t[2*j-1]-t[2*j]) : j in [1..i]];
        if divisor eq D then
          listOfPoints := &cat[[<c[j],t[2*j-1]>,<-c[j],t[2*j]>] : j in [1..i]];
          listOfPoints := normalizeList(listOfPoints); //get rid of multiples
          return listOfPoints;
        end if;
      end for;
    end for;
  end for;

end function;


// divisorAsSumOfPoints(basX[1], ptsX);
// // [ <1, (1 : -3 : 1)>, <-1, (-2 : 3 : 1)> ]
// divisorAsSumOfPoints(basX[2], ptsX);
// // [ <-1, (0 : -1 : 1)>, <1, (-2 : -3 : 1)> ]

divisorAsSumOfPoints(bas[1], ptsH);
//[ <1, (1 : -15 : 1)>, <-1, (-2 : 15 : 1)> ]
divisorAsSumOfPoints(bas[2], ptsH);
//[ <-1, (0 : -5 : 1)>, <1, (-2 : -15 : 1)> ]


