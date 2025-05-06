declare verbose LocalHeights, 3;

declare type DualGraph;
declare type ClusterDiagram;

declare attributes DualGraph: Edges, Vertices, ClusterDiagram, EdgesCoordinates, Genus;
declare attributes ClusterDiagram: Clusters, Children, RelativeDepths, AbsoluteDepths, Fss, F, Prime, SquareRootsgs, SquareRootshs, AnnulusParameters, Roots, SemistableField, SquareRootsField;

_EPS := 1/10;

intrinsic Print(x::DualGraph)
  {Print x}
  printf "Reduction Graph of %o on %o vertices with %o edges", x`ClusterDiagram, #x`Vertices, #x`EdgesCoordinates;
end intrinsic;

intrinsic Print(x::ClusterDiagram)
  {Print x}
  printf "Cluster Diagram %o from polynomial y^2 =  %o", x`Clusters, x`F;
end intrinsic;

intrinsic SemistableField(f::RngUPolElt, p::RngIntElt : prec := 10, printing := true) ->  RngUPolElt
  {Construct an extension L/Qp over which the curve y^2 = f has semistable reduction.
  Return fL the basechange of f to L.}
  R_Q<x> := PolynomialRing(Rationals());
  prec := prec;
  g := (Degree(f) - 2) div 2; //assume s = 2g+2
  assert g ge 1;
  assert Degree(f) mod 2 eq 0;

  Qp := pAdicField(p,prec);
  R_Qp<xp> := PolynomialRing(Qp);
  fQp := R_Qp!f;

  LL<a>:= SplittingField(fQp);
  if printing then
    vprint LocalHeights, 2: "Is tame:", IsTamelyRamified(LL); //TODO: check semistability over smaller field
  end if;
  pi := UniformizingElement(LL);
  R_LL<xLL> := PolynomialRing(LL);
  quad_eisenstein_poly := xLL^2 - pi; // make a ramified quadratic extension
  assert IsEisenstein(quad_eisenstein_poly);

  //make field over which we know the curve is semistable
  L<c> := TotallyRamifiedExtension(LL, quad_eisenstein_poly);
  if printing then
    vprint LocalHeights, 2: "Semistable extension: ",L;
  end if;

  R_L<xL> := PolynomialRing(L);
  fL := R_L!f;
  return fL;

end intrinsic;

intrinsic ClusterData(f::RngUPolElt, p::RngIntElt : prec := 10) -> ClusterDiagram
  {Construct the clusters data associated to the roots of f a semistable polynomial over a p-adic field L (i.e. the hyperelliptic curve y^2 =f).
  At the moment, this function returns the abstract clusters, the data of the children, and relative depths. This data is given as indices:
  If j is in childrenOfClusters[i] then Clusters[j] is a child of Clusters[i].}

  require IsEven(Degree(f)) : "Functionality for odd degree polynomials is currently not implemented";

  fL := SemistableField(f, p : prec := prec + 30, printing := false);
  roots := Roots(fL);
  Lhighprec := BaseRing(fL);
  L<c> := ChangePrecision(Lhighprec, prec);
  _<a> := BaseRing(L);
  roots := [<L!r[1],r[2]> : r in roots];
  fL := SemistableField(f, p : prec := prec);
  //do a second time because we want the real fL to be over a lower prec field

  vprint LocalHeights, 3: "roots:",roots;

  for root_m in roots do //Check that there are no double roots:
      assert root_m[2] eq 1; // if not we should rerun with larger precision
  end for;

  clusters := [[i] : i in [1 .. #roots]];

  properClusters := [];
  for i in [1 .. #roots] do
    for j in [i+1 .. #roots] do
      childij :=[];
      valij := Valuation(roots[i][1]-roots[j][1]);
      for k in [1 .. #roots] do
        if Valuation(roots[k][1] - roots[i][1]) ge valij then
          Append(~childij,k);
        end if;
      end for;
      Append(~properClusters,childij);
    end for;
  end for;
  properClusters := SetToSequence(Set(properClusters));
  clusters := clusters cat properClusters;
  numClusters := #clusters;

  sortedClusters := [];
  while #sortedClusters ne numClusters do
    index := Max([i : i in [1..#sortedClusters] | Set(clusters[1]) subset sortedClusters[i]] cat [0])+1 ;
    Insert(~sortedClusters, index, clusters[1]);
    Remove(~clusters,1);
  end while;
  clusters := sortedClusters;
  inclusionMatrix := [];
  for i in [1 .. numClusters] do
    inclusionMatrixi := [];
    for j in [1 .. numClusters] do
      Append(~inclusionMatrixi, (i ne j) and (Set(clusters[i]) subset Set(clusters[j])) );
    end for;
    Append(~inclusionMatrix,inclusionMatrixi);
  end for;

  childrenOfClusters := [];
  for i in [1 .. numClusters] do
    childsi := [];
    for j in [1 .. numClusters] do
      if inclusionMatrix[j][i] and &and[not inclusionMatrix[j][k] or not inclusionMatrix[k][i] : k in [1 .. numClusters]] then
        Append(~childsi,j);
      end if;
    end for;
    Append(~childrenOfClusters,childsi);
  end for;

  vprint LocalHeights,1: "cluster structure:", clusters;
  vprint LocalHeights,2: "children:",  childrenOfClusters;

  depthClusters := [Rationals()!Minimum([Valuation(roots[i][1]-roots[j][1]) : i,j in clusters[k]])/Valuation(L!p) : k in [1 .. numClusters]];
  relativeDepthClusters := [Rationals()!(-1) : i in [1 .. numClusters]];
  for i in [1 .. numClusters] do
    for j in childrenOfClusters[i] do
      relativeDepthClusters[j] := depthClusters[j] - depthClusters[i];
    end for;
  end for;

  singletonClusters := [ #clusters[i] eq 1 : i in [1 .. numClusters]];
  evenClusters := [(#clusters[i] mod 2) eq 0: i in [1 .. numClusters] ];
  ueberevenClusters := [ evenClusters[i] and &and[evenClusters[j] : j in childrenOfClusters[i]] : i in [1 .. numClusters]];

  C := New(ClusterDiagram);
  C`Fss := fL;
  C`F := f;
  C`Prime := p;
  C`Clusters := clusters;
  C`Children := childrenOfClusters;
  C`RelativeDepths := relativeDepthClusters;
  C`AbsoluteDepths := depthClusters;
  C`Roots := roots;
  C`SemistableField := Parent(roots[1][1]);
  return C;

end intrinsic;

intrinsic ClusterGenus(cd::ClusterDiagram) -> SeqEnum
  {Returns a list of the genus of each vertex associated to each cluster}

  Clusters := cd`Clusters;
  childrenOfClusters := cd`Children;
  relativeDepthClusters := cd`RelativeDepths;

  genus := [];
  for i->C in Clusters do
    oddChildren := 0;
    for j in childrenOfClusters[i] do
      if IsOdd(#Clusters[j]) then
        oddChildren :=  oddChildren + 1;
      end if;
    end for;
    g := Ceiling(oddChildren / 2) -1;
    if g lt 0 then g := 0; end if;
    Append(~genus, g);
  end for;
  return genus;
end intrinsic;

function getTopOuterRadius(clusterdata)
  // Returns the outer radius for the annulus corresponding to the top cluster
  L := clusterdata`SemistableField;
  depthClusters := clusterdata`AbsoluteDepths;
  relDepth := clusterdata`RelativeDepths;
  pi := UniformizingElement(L);
  nVal := 1/NormValuation(pi);
  topCluster := Index(relDepth, -1);

  outerRadius := depthClusters[topCluster]-1*_EPS;
  d := Denominator(outerRadius);
  if d ge nVal/2 then
    d := d/nVal;
  end if;
  outerRadius := d*outerRadius;
  return outerRadius + _EPS;
end function;

function constructgs(clusterIndex, clusterdata : r0 := false)
  //s cluster of index clusterIndex construct g_s such that u^2 = g_s is the defining equation of X_s
  //recenter g_s around r0 and divide by x - r0 if s is odd
  //also construct h_s = fL/g_s, and recenter around r0, scale to have leading term 1
  //factor h_s into factors based on the children

  allroots := clusterdata`Roots;
  L := clusterdata`SemistableField;

  R := LaurentPolynomialRing(L, "xL");
  xL := R`Generator;
  parameters := clusterdata`AnnulusParameters;

  clusters := clusterdata`Clusters;
  childrenOfClusters := clusterdata`Children;
  relativeDepthClusters := clusterdata`RelativeDepths;
  evenClusters := [(#clusters[i] mod 2) eq 0: i in [1 .. #clusters] ];
  ueberevenClusters := [ evenClusters[i] and &and[evenClusters[j] : j in childrenOfClusters[i]] : i in [1 .. #clusters]];
  topCluster := Index(relativeDepthClusters,-1);
  absDepth := clusterdata`AbsoluteDepths;

  clusterset := [c : c in childrenOfClusters[clusterIndex] | IsOdd(#clusters[c]) ]; //odd children of v

  r0 := parameters[clusterIndex];

  if ueberevenClusters[clusterIndex] then
    gs := R!1;
    usedroots := [];
  elif #clusters[clusterIndex] eq 1 then
    gs := R!1;
    assert allroots[clusters[clusterIndex][1]][1] eq r0;
    //make sure that we are appending the right root
    usedroots := [clusters[clusterIndex][1]];
  else
    gs := R!1;
    usedroots := [];
    for s in clusterset do
      rs := allroots[clusters[s][1]][1]; //pick the first root from each odd child
      if IsOdd(#clusters[clusterIndex]) and rs eq r0 then
        Append(~usedroots, clusters[s][1]);
        continue;
      end if;
      gs := gs*(xL - rs);
      Append(~usedroots, clusters[s][1]);
    end for;
    gs := Evaluate(gs, xL + r0);
  end if;

  hs_factored := [];
  hs_const := [];
  children := childrenOfClusters[clusterIndex];

  if #children ge 1 then
    poly := [xL - allroots[j][1] : j in clusters[children[1]] | (j notin usedroots)] cat [xL - allroots[j][1] : j in [1 .. #allroots] | j notin clusters[clusterIndex] and j notin usedroots];
    if #poly ge 1 then
      poly := &*poly;
      r0child := parameters[children[1]];
      poly := Evaluate(poly, xL + r0child);
      C := Evaluate(poly, 0);
      Append(~hs_const, C);
    else
      poly := R!1;
      Append(~hs_const, L!1);
    end if;
    Append(~hs_factored,poly);
    Remove(~children,1);
    for c in children do
      poly := [xL - allroots[j][1] : j in clusters[c] | (j notin usedroots)];
      if #poly ge 1 then
        poly := &*poly;
        r0child := parameters[c];
        poly := Evaluate(poly, xL + r0child);
        C := Evaluate(poly, 0);
        Append(~hs_const, C);
      else
        poly := R!1;
        Append(~hs_const, L!1);
      end if;
      Append(~hs_factored,poly);
    end for;
  else
    poly := [xL - allroots[j][1] : j in [1 ..#allroots] | (j notin usedroots)];
    if #poly ge 1 then
      poly := &*poly;
      poly := Evaluate(poly, xL + r0);
      C := Evaluate(poly, 0);
      Append(~hs_const, C);
    else
      poly := R!1;
      Append(~hs_const, L!1);
    end if;
    Append(~hs_factored,poly);
  end if;

  return gs, hs_factored, hs_const;
end function;


procedure PickParameters(cd)

  fL := cd`Fss;
  allroots := cd`Roots;
  L := cd`SemistableField;
  R := LaurentPolynomialRing(L, "xL");
  xL := R`Generator;

  clusters := cd`Clusters;
  parameters_on_annuli := AssociativeArray();
  for i in [1..#clusters] do
    r0 := [allroots[j][1] : j in clusters[i]][1]; //pick a parameter in A_s
    parameters_on_annuli[i] := r0;
  end for;

  cd`AnnulusParameters := parameters_on_annuli;
end procedure;

intrinsic FieldSquareRoots(clusterdata::ClusterDiagram) -> Any
  {Returns a p-adic field extension that contains all the square roots needed to compute heights.}

  vprintf LocalHeights, 2 : "Creating a field extension over which all square roots are defined.\n";
  fL := clusterdata`Fss;
  L := clusterdata`SemistableField;
  p := clusterdata`Prime;
  allroots := clusterdata`Roots;

  depthClusters := clusterdata`AbsoluteDepths;
  clusters := clusterdata`Clusters;
  childrenOfClusters := clusterdata`Children;
  params := clusterdata`AnnulusParameters;
  evenClusters := [c : c in clusters | IsEven(#c)];

  R_L<x> := PolynomialRing(L);
  R := LaurentPolynomialRing(L, "xL");
  xL := R`Generator;

  needsSqRoot := [];
  lc := LeadingCoefficient(fL);
  if not IsSquare(lc) then needsSqRoot cat:= [ L!lc ]; end if;

  // This is needed for GlobalSymbol1:
  for evenCluster in evenClusters do
    index := Index(clusters,evenCluster);
    r0 := params[index];
    fshifted := lc * &*[xL-r[1] + r0 : r in allroots];
    C := Evaluate(fshifted, L!0);
    if not IsSquare(C) then needsSqRoot cat:= [ C ]; end if;
  end for;

  // This happens in GlobalSymbol1 and GlobalSymbol2:
  for clusterIndex in [1..#clusters] do
    r0 := params[clusterIndex];
    children := childrenOfClusters[clusterIndex] cat [clusterIndex];
    for childIndex in children do
      if #clusters[childIndex] gt 1 then
        if not IsEven(#clusters[childIndex]) then
          parentIndex := Parent(childIndex, clusterdata);
          gs := R!1;
          clusterSet := [c : c in childrenOfClusters[clusterIndex] | IsOdd(#clusters[c]) ];
          r0child := params[childIndex];
          usedroots := [];
          for s in clusterSet do
            rs := allroots[clusters[s][1]][1]; //pick the first root from each odd child
            if rs eq r0child then
              Append(~usedroots, clusters[s][1]);
              continue;
            end if;
            gs := gs*(xL - rs);
            Append(~usedroots, clusters[s][1]);
          end for;
          gs := Evaluate(gs, xL + r0child);
          C := Evaluate(gs, 0);
          if not IsSquare(C) then needsSqRoot cat:= [ C ]; end if;
        end if;
      end if;
    end for;
  end for;

  if #needsSqRoot eq 0 then
    return [];
  else
    return needsSqRoot;
  end if;
end intrinsic;

intrinsic AssignSquareRoots(cd::ClusterDiagram)
  {Fix an r0, a parameter on each annulus A_s.
  Fix a square root of g_s in each A_s for s even, square root of g_s/(x-a_s) in A_s for s odd.
  Fix a square root of h_s in U_s represented in factored form, factors in D_s^o - D_s'^c for s' child, all s.
  Ensure compatbility criterion over s ueberevens: g_s^1/2 = 1, and h_s^1/2 |A_s' = g_s'^1/2 * (h_s'|A_s')^1/2 for all s' < s.}

  vprintf LocalHeights, 1 : "Assigning square roots...\n";
  clusters := cd`Clusters;
  childrenOfClusters := cd`Children;
  evenClusters := [(#clusters[i] mod 2) eq 0: i in [1 .. #clusters] ];
  ueberevenClusters := [ evenClusters[i] and &and[evenClusters[j] : j in childrenOfClusters[i]] : i in [1 .. #clusters]];
  depthClusters := cd`AbsoluteDepths;
  relDepth := cd`RelativeDepths;
  topCluster := Index(relDepth, -1);
  fL := cd`Fss;
  L := cd`SemistableField;
  R_L<x>:=PolynomialRing(L);
  pi := UniformizingElement(L);
  e := 1/NormValuation(pi);
  PickParameters(cd); //for each cluster, pick an r0 in the cluster
  annulusParameters := cd`AnnulusParameters;

  LL := TotallyRamifiedExtension(L, x^2-pi);
  piLL := UniformizingElement(LL);
  LLx := LaurentPolynomialRing(LL, "x_LL");

  sqrt_gs_on_As := AssociativeArray();
  sqrt_hs_on_Us := AssociativeArray();

  fL := cd`Fss;
  allroots := Roots(fL);

  nonSquares :=[];
  gsList := AssociativeArray();
  hs_factoredList := AssociativeArray();
  hs_constList := AssociativeArray();
  for i in [1 ..#clusters] do
    children_of_i := childrenOfClusters[i];
    gs, hs_factored, hs_const := constructgs(i, cd);
    // Save the information for later, so we don't have to recompute anything.
    gsList[i] := gs;
    hs_factoredList[i] := hs_factored;
    hs_constList[i] := hs_const;

    if #clusters[i] eq 1 then
      continue;
      //actually we won't use the singleton clusters ever, and there is a chance that the square roots break the code
      //in the rare cases where the square roots of the constant terms give a ramified field extension
      //so we'll just skip this case entirely
    end if;
    C := Evaluate(gs, 0);
    if not IsSquare(C) then nonSquares cat:= [ C ]; end if; //work over a field where all const terms and leading term are square roots
    nonSquares cat:= [ Cj : Cj in hs_const | not(IsSquare(Cj))];
  end for;

  nonSquares cat:= FieldSquareRoots(cd);
  baseField := L;
  while #nonSquares gt 0 do
    _, _, E := Factorization(x^2 - nonSquares[1] : Extensions := true);
    K<b> := E[1]`Extension;
    baseField := K;
    nonSquares := Remove(nonSquares,1);
    _<x>:=PolynomialRing(baseField);
  end while;

  K := baseField;
  Kx := LaurentPolynomialRing(K, "x_K");

  cd`SquareRootsField := K;

  for i in [1 ..#clusters] do
    genuslist := ClusterGenus(cd);

    if i eq topCluster and genuslist[i] eq 0 and (not ueberevenClusters[i]) then
      continue;
    end if;

    children_of_i := childrenOfClusters[i];
    gs := gsList[i];
    hs_factored := hs_factoredList[i];
    hs_const := hs_constList[i];

    if #clusters[i] eq 1 then
      continue;
      //actually we won't use the singleton clusters ever, and there is a chance that the square roots break the code
      //in the rare cases where the square roots of the constant terms give a ramified field extension
      //so we'll just skip this case entirely
    end if;
    vprintf LocalHeights, 3 : "Starting cluster %o.\n", clusters[i];

    if i ne topCluster then
      parentindex := Parent(i, cd);
      outerdepth := depthClusters[parentindex] + _EPS;
    else
      outerdepth := getTopOuterRadius(cd);
    end if;

    S := SeriesAnnulusRing(K, depthClusters[i] - _EPS, outerdepth, "T" : LaurPolRing := Kx);
    T := S`Generator;
    gsT := Evaluate(gs,T);
    if ueberevenClusters[i] then
      sqrtgs := S!1;
    else
      sqrtgs := SquareRoot(gsT : inverse := true, wellDefinedCheck := false);
    end if;
    sqrt_gs_on_As[i] := sqrtgs;

    cd`SquareRootsgs := sqrt_gs_on_As;

    sqrt_hs_on_Us[i]:= [* *];
    for j->c in children_of_i do
      hsj := hs_factored[j];
      hsj := hsj;
      S := SeriesAnnulusRing(K, depthClusters[c] - _EPS, outerdepth, "T" : LaurPolRing := Kx);
      T := S`Generator;
      hsT := Evaluate(hsj,T);
      sqrths := SquareRoot(hsT : inverse := true, wellDefinedCheck := false);
      Append(~sqrt_hs_on_Us[i],sqrths);
    end for;
    if #children_of_i eq 0 then
      hs := hs_factored[1];
      S := SeriesAnnulusRing(K, depthClusters[i] - _EPS, outerdepth, "T" : LaurPolRing := Kx);
      T := S`Generator;
      hsT := Evaluate(hs,T);
      sqrths := SquareRoot(hsT : inverse := true, wellDefinedCheck := false);
      Append(~sqrt_hs_on_Us[i],sqrths);
    end if;
  end for;
  vprintf LocalHeights, 2 : "Done assigning square roots of hs and gs.\n";

  vprintf LocalHeights, 2 : "Ensuring compatibility of square roots.\n";
  // Ensure compatbility criterion over s ueberevens: h_s^1/2 |A_s' = g_s'^1/2 * (h_s'|A_s')^1/2 for all s' < s.}
  for i in [1..#clusters] do
    if ueberevenClusters[i] then
      hs_factored := sqrt_hs_on_Us[i]; //used to compute h_s^1/2 |A_s'
      children := childrenOfClusters[i];
      for j in [1 ..#children] do
        c := children[j];
        sqrtgsprime := sqrt_gs_on_As[c]; //g_s'^1/2
        hschild_factored := sqrt_hs_on_Us[c];//used to compute (h_s'|A_s')^1/2
        r0 := annulusParameters[c];
        //find a point in A_s
        pt := piLL^(Integers()!(e*(depthClusters[c] + depthClusters[i])));
        SS := Parent(sqrtgsprime);
        evalsqrtgsprime := Evaluate(sqrtgsprime, SS!pt); // this is like -r0 + r0
        evalsqrtgsprime := Coefficient(evalsqrtgsprime, 0);
        if #childrenOfClusters[c] ge 1 then
          evalsqrthsprime := &*[ Coefficient(Evaluate(hschild_factored[l],Parent(hschild_factored[l])!(pt - annulusParameters[childrenOfClusters[c][l]] + r0)),0) : l in [1..#hschild_factored] ];
        else
          SS := Parent(hschild_factored[1]);
          evalsqrthsprime := Evaluate(hschild_factored[1],SS!pt); //because r0child = r0, so this is pt - r0child + r0
          evalsqrthsprime := Coefficient(evalsqrthsprime, 0);
        end if;
        //now we compute h_s^1/2|A_s'
        evalsqrths := &*[Coefficient(Evaluate(hs_factored[l], Parent(hs_factored[l])!(pt - annulusParameters[children[l]] + r0)),0) : l in [1..#children]];
        //Check compatibility
        if IsZero(evalsqrths +evalsqrthsprime*evalsqrtgsprime) then
          sqrt_hs_on_Us[c][1] := -sqrt_hs_on_Us[c][1];
        elif not(IsZero(evalsqrths - evalsqrthsprime*evalsqrtgsprime)) then
          vprintf LocalHeights, 2 : "Compatability requires %o is equal to %o, but their difference is %o", evalsqrths, evalsqrthsprime*evalsqrtgsprime, evalsqrths-evalsqrthsprime*evalsqrtgsprime;
          assert false;
        end if;
      end for;
    end if;
  end for;
  cd`SquareRootshs := sqrt_hs_on_Us;

end intrinsic;

intrinsic ConstructDualGraph(cd::ClusterDiagram) -> DualGraph
  {Given the cluster structure, construct the dual dual graph of the special fiber of y^2 = f over F_p.
  Returns a list of vertices given as tuples <i, sign> such that Clusters[i] corresponds to the cluster (and sign is 0 if v is not ueber even and +-1 otherwise)
  as well as edges such that the edges[i] = [ <j, s, w_j> ] is a list of tuples
  indicating that vertex[i] is adjacent to vertex[j] by an edge of weight w_j, and corresponds to Cluster[s]
  (in the sense that the annulus A_e labeled by the edge contains the roots of Clusters[s] inside of the annulus).
  The edge is *directed*: it goes from vertices[i] to vertices[j].
  This is not minimal, but it works on more cluster types.}

  clusters := cd`Clusters;
  childrenOfClusters := cd`Children;
  relativeDepthClusters := cd`RelativeDepths;

  numClusters := #clusters;
  singletonClusters := [ #clusters[i] eq 1 : i in [1 .. numClusters]];
  evenClusters := [(#clusters[i] mod 2) eq 0: i in [1 .. numClusters] ];
  ueberevenClusters := [ evenClusters[i] and &and[evenClusters[j] : j in childrenOfClusters[i]] : i in [1 .. numClusters]];

  vertices := [[i,0] : i in [1 .. numClusters] | not ueberevenClusters[i] and not singletonClusters[i]] cat [[i,sign] : i in [1 .. numClusters], sign in [-1,1] | ueberevenClusters[i]];

  edgelist := [[] : i in [1 .. #vertices]];
  for i in [1 .. #vertices] do
    vertexIndex := vertices[i][1];
    for s in childrenOfClusters[vertexIndex] do
      if singletonClusters[s] then
        continue;
      end if;
      vertex_of_s := [s,0];
      if ueberevenClusters[s] then
          vertex_of_s[2] := vertices[i][2];
      end if;
      indexs := Index(vertices, vertex_of_s);
      if not evenClusters[s] then
        Append(~edgelist[indexs], <i,s,relativeDepthClusters[s]/2>);
      else
        Append(~edgelist[indexs], <i,s,relativeDepthClusters[s]>);
        if not ueberevenClusters[vertexIndex] then
          Append(~edgelist[indexs], <i,s,relativeDepthClusters[s]>);
        end if;
      end if;
    end for;
  end for;

  alledges := &cat[[[vi,ei]: ei in [1..#edgelist[vi]]]:vi in [1..#vertices]];
  vertexgenus := ClusterGenus(cd);

  G := New(DualGraph);
  G`Vertices := vertices;
  G`Edges := edgelist;
  G`ClusterDiagram := cd;
  G`EdgesCoordinates := alledges;
  G`Genus :=vertexgenus;
  return G;
end intrinsic;

intrinsic EdgeFromCoords(e::SeqEnum,G::DualGraph) -> Tup
  {Returns the edge corresponding to the coordinates e}
  edges := G`Edges;
  return edges[e[1]][e[2]];
end intrinsic;

intrinsic Parent(clusterIndex::RngIntElt, clusterdata::ClusterDiagram) -> RngIntElt
  {Returns the index of the cluster that goes one level up from the vertex corresponding to the cluster with clusterIndex
  i.e. the Parent Cluster }
  clusters := clusterdata`Clusters;
  childrenOfClusters := clusterdata`Children;
  indexNewCluster := [i : i in [1..#clusters] | clusterIndex in childrenOfClusters[i]][1];
  return indexNewCluster;
end intrinsic;

intrinsic CompatibleSignF(sqrtftinv::RngSerAnnElt, clusterIndex::RngIntElt, clusterdata::ClusterDiagram) -> Bool
  {Given an inverse square root of f on an annulus, returns true if the sign is the
  same as the one preset for sqrt(f).  Otherwise it returns false.}
  childrenOfClusters := clusterdata`Children;
  depthClusters := clusterdata`AbsoluteDepths;
  L := clusterdata`SemistableField;
  annulusParameters := clusterdata`AnnulusParameters;
  sqrtgsOnAs := clusterdata`SquareRootsgs;
  sqrthsOnUs := clusterdata`SquareRootshs;
  relDepths := clusterdata`RelativeDepths;

  pi := UniformizingElement(L);
  e := 1/NormValuation(pi);
  _<x> := PolynomialRing(L);
  LL := TotallyRamifiedExtension(L, x^2-pi);
  piLL := UniformizingElement(LL);
  LLx := LaurentPolynomialRing(LL, "x");

  r0 := annulusParameters[clusterIndex];
  topCluster := Index(relDepths,-1);

  hsFactored := sqrthsOnUs[clusterIndex]; //used to compute h_s^1/2
  children := childrenOfClusters[clusterIndex];

  if clusterIndex ne topCluster then
    parentIndex := Parent(clusterIndex,clusterdata);
    outerdepth := depthClusters[parentIndex] + _EPS;
  else
    outerdepth := getTopOuterRadius(clusterdata);
  end if;
  pt := piLL^(Integers()!(e*(depthClusters[clusterIndex] + outerdepth-_EPS))); //choose a point to compare

  if #children ge 1 then // hs comes factored
    evalsqrths := [];
    for l -> c in children do
      SS := SeriesAnnulusRing(LL, depthClusters[c] - _EPS, depthClusters[clusterIndex] + _EPS, "TT" : LaurPolRing := LLx);
      TT := SS`Generator;
      hsFactor := Evaluate(hsFactored[l], SS!(pt - annulusParameters[c] + r0));
      Append(~evalsqrths, Coefficient(hsFactor,0));
    end for;
    evalsqrths := &*evalsqrths;
  else //hs is already in the annulus
    SS := SeriesAnnulusRing(LL, depthClusters[clusterIndex] - _EPS, outerdepth, "TT" : LaurPolRing := LLx);
    TT := SS`Generator;
    hsFactor := Evaluate(hsFactored[1], SS!(pt));
    evalsqrths := Coefficient(hsFactor,0);
  end if;

  SS := SeriesAnnulusRing(LL, depthClusters[clusterIndex] - _EPS, outerdepth, "TT" : LaurPolRing := LLx);
  TT := SS`Generator;
  sqrtgs := sqrtgsOnAs[clusterIndex];
  evalsqrtgs := Coefficient(Evaluate(sqrtgs, SS!pt),0);

  evalsqrtf := Coefficient(Evaluate(sqrtftinv, SS!pt),0);

  // Now we check signs
  assert Valuation(evalsqrtf) eq Valuation(evalsqrtgs*evalsqrths);
  assert not IsWeaklyZero(evalsqrtf);

  if Valuation(evalsqrtf+evalsqrtgs*evalsqrths) gt Valuation(evalsqrtf) then
    return false;
  elif Valuation(evalsqrtf-evalsqrtgs*evalsqrths) gt Valuation(evalsqrtf) then
    return true;
  end if;
end intrinsic;

intrinsic EvenResidue(clusterindex::RngIntElt, clusterdata::ClusterDiagram) -> SeqEnum
  {Given  index j of a cluster s = Clusters[j] (not the top cluster),
  and the cluster structure of the hyperelliptic curve, return the annular residue of x^i dx/y over
  the annulus A_s := D_s^o - D_s^c where D_s^o is the largest open disc in A^1,an cutting out s and
  D_s^c is the smallest closed disk in A^1,an cutting out s. This function works for even cluster sizes.}

  clusters := clusterdata`Clusters;
  depthClusters := clusterdata`AbsoluteDepths;
  fL := clusterdata`Fss;
  parameters := clusterdata`AnnulusParameters;
  L := clusterdata`SemistableField;
  allroots := clusterdata`Roots;
  p := clusterdata`Prime;
  K := clusterdata`SquareRootsField;
  relDepths := clusterdata`RelativeDepths;
  topCluster := Index(relDepths,-1);

  R_L<x> := PolynomialRing(L);
  g := (Degree(fL) - 2) div 2;
  R := LaurentPolynomialRing(L, "xL");
  xL := R`Generator;

  roots := [allroots[j][1] : j in clusters[clusterindex] ];
  d := #roots;
  require IsEven(d) : "Specified cluster must be even, otherwise call OddResidue";
  if clusterindex ne topCluster then
    parentindex := Parent(clusterindex,clusterdata);
    outerdepth := depthClusters[parentindex] + _EPS;
  else
    outerdepth := getTopOuterRadius(clusterdata);
  end if;

  lc := LeadingCoefficient(fL);
  r0 := parameters[clusterindex];
  fshifted := lc * &*[xL-r[1] +r0 : r in allroots];
  C := Evaluate(fshifted, L!0);
  Kx := LaurentPolynomialRing(K, "x");
  S := SeriesAnnulusRing(K, depthClusters[clusterindex] - _EPS, outerdepth, "T" : LaurPolRing := Kx);
  T := S`Generator;
  fshiftedT := Evaluate(fshifted, T);
  sqrtftinv := SquareRoot(fshiftedT : inverse := true, wellDefinedCheck := false);

  sameSign := CompatibleSignF(sqrtftinv,clusterindex,clusterdata);
  if not sameSign then
    sqrtftinv := -sqrtftinv;
  end if;
  // We choose sqrtftinv and now we just want to check that it equals g*h for the right cluster

  //now check compabitility with chosen square roots
  res := [];
  for i in [0 .. 2*g] do
    Wi := (T+K!r0)^i * (1/2)*sqrtftinv;
    residueir0 := Coefficient(Wi,-1);
    if  IsZero(residueir0) then //precision is weird at 0
      Append(~res,residueir0);
    else
  	 NormPrecCoeff := Maximum(Wi`v1AdicPrec + Wi`v1, Wi`v2AdicPrec + Wi`v2); // c * x^(-1) has v-adic prec v_p(c) - v
      residueir0 := ChangePrecision(residueir0,Minimum(RelativePrecision(residueir0),Floor(NormPrecCoeff * Valuation(Integers(K)!p)-Valuation(residueir0))));
      Append(~res,residueir0);
    end if;
  end for;
  return res;

end intrinsic;


intrinsic OddResidue(clusterindex::RngIntElt, clusterdata::ClusterDiagram) -> SeqEnum
  {Functionality for the case of odd clusters}

  clusters := clusterdata`Clusters;
  fL := clusterdata`Fss;
  g := (Degree(fL) - 2) div 2;
  require IsOdd(#clusters[clusterindex]) : "Specified cluster must be odd, otherwise call EvenResidue";
  res := [Rationals()!0 : i in [0 .. 2*g]];
  return res;

end intrinsic;

intrinsic ComplementOfSpanningTree(G::DualGraph) -> SeqEnum
  {Returns the complement of a spanning tree of the dual graph. The complement of the spanning tree
  is given as a tuple  of the form [v, e]  where the edge corresponds to the eth edge of the vth vertex}

  cd := G`ClusterDiagram;
  clusters := cd`Clusters;
  childrenOfClusters := cd`Children;
  relativeDepthClusters := cd`RelativeDepths;

  numClusters := #clusters;
  evenClusters := [(#clusters[i] mod 2) eq 0: i in [1 .. numClusters] ];
  ueberevenClusters := [ evenClusters[i] and &and[evenClusters[j] : j in childrenOfClusters[i]] : i in [1 .. numClusters]];
  topCluster := Index(relativeDepthClusters,-1);

  vertices := G`Vertices;
  edges := G`Edges;
  alledges := G`EdgesCoordinates;

  span := [];
  for cluster in [i : i in [1..numClusters] | i ne topCluster and #clusters[i] gt 1 ] do //not top cluster or singleton
    vertexCluster := not ueberevenClusters[cluster] select Index(vertices,[cluster,0]) else Index(vertices,[cluster,1]);
    Append(~span,[vertexCluster,1]);
  end for;

  if ueberevenClusters[topCluster] then
    child := childrenOfClusters[topCluster][1];
    if not ueberevenClusters[child] then
      vertexChild := Index(vertices,[child,0]);
    else
      vertexChild := Index(vertices,[child,1]);
    end if;
    Append(~span,[vertexChild,2]);
  end if;

  complement := SequenceToMultiset(alledges) diff SequenceToMultiset(span);

  return MultisetToSequence(complement);
end intrinsic;

intrinsic HomologyDualGraph(G::DualGraph) -> SeqEnum
  {A basis for the homology of the dual graph.  Returns a list of lists.  The
  smaller list represents a homology element as a sum of edges (with coefficients)
  and consists of tuples <a, [v,e]> where a is the coefficient of the edge, v is
  the index of the root vertex of the edge, and e is the index of the edge coming
  out of vertex v.}
  QQ := Rationals(); //coerce to rationals for later arithmetic

  EndpointIndex := function(vertexIndex,edgeIndex,edges)
    // returns the endpoint of the edge edges[vertexIndex][edgeIndex]
    return edges[vertexIndex][edgeIndex][1];
  end function;

  GoOneUp := function(spanningTreeEndPts,endpointIndex:notUsing:=[-1])
    //returns the edge in the spanning tree that ends at endpointIndex
    index := [i : i in [1..#spanningTreeEndPts] | spanningTreeEndPts[i][1] eq endpointIndex and not i in notUsing][1];
    return index, spanningTreeEndPts[index][2];
  end function;

  FindLoopCoords := function(vertexIndex, edgeIndex, topClusterIndices, vertices, edges, spanningTreeEndPts,ueberevenClusters)
    // returns a list <coeff,indexSpanning>, where the edge vertexIndex[edgeIndex]
    // completes a loop, and indexSpanning denotes the index of the necessary edges
    // in the spanning tree, and coeff is the appropiate coefficient (+/- 1).
    loop := [];
    endPoint := EndpointIndex(vertexIndex,edgeIndex,edges);
    if [vertexIndex,endPoint] in spanningTreeEndPts then
      return [<QQ!-1,Index(spanningTreeEndPts,[vertexIndex,endPoint])>];
    end if;
    // We set-up first by having both ends be at the same level of the tree
    // The edge goes [vertexIndex,endPoint]
    if vertexIndex in topClusterIndices then
      // This should not happen since edges go up.
      assert false;
    elif endPoint in topClusterIndices then
      // Only should happen in the uebereven case
      // Go one down first and then go up using another route
      indexDownStart := [i : i in [1..#spanningTreeEndPts] | spanningTreeEndPts[i][2] eq endPoint][1];
      Append(~loop, <QQ!-1,indexDownStart>);
      upEnd := vertexIndex;
      upStart := spanningTreeEndPts[indexDownStart][1];
    else
      indexUp, upEnd := GoOneUp(spanningTreeEndPts,vertexIndex);
      Append(~loop, <QQ!-1,indexUp>);
      upStart := vertexIndex;
    end if;
    // now we are at the same level, just make sure to use another edge to go up
    while upEnd ne upStart do
      // go one up in both and check again
      if upEnd in topClusterIndices then
        indexDownStart := [i : i in [1..#spanningTreeEndPts] | spanningTreeEndPts[i][1] eq upEnd][1];
        Append(~loop, <QQ!-1,indexDownStart>);
        upEnd := EndpointIndex(upEnd,edgeIndex,edges);
        upStart := spanningTreeEndPts[indexDownStart][2];
      elif upStart in topClusterIndices then
        assert false;
      else
        indexUpEnd, upEnd := GoOneUp(spanningTreeEndPts,upEnd : notUsing := [l[2] : l in loop]);
        indexUpStart, upStart := GoOneUp(spanningTreeEndPts,upStart : notUsing := [l[2] : l in loop]);
        // Append the new edges with the right coeffs
        Append(~loop, <QQ!-1,indexUpEnd>);
        Append(~loop, <QQ!1,indexUpStart>);
      end if;
    end while;

    return loop;
  end function;

  cd := G`ClusterDiagram;
  clusters := cd`Clusters;
  childrenOfClusters := cd`Children;
  relativeDepthClusters := cd`RelativeDepths;

  numClusters := #clusters;
  evenClusters := [(#clusters[i] mod 2) eq 0: i in [1 .. numClusters] ];
  ueberevenClusters := [ evenClusters[i] and &and[evenClusters[j] : j in childrenOfClusters[i]] : i in [1 .. numClusters]];
  topCluster := Index(relativeDepthClusters,-1);

  vertices := G`Vertices;
  edges := G`Edges;
  alledges := G`EdgesCoordinates;

  topClusterIndices := [i : i in [1..#vertices] | vertices[i][1] eq topCluster];

  complementspan := ComplementOfSpanningTree(G);
  spanningTree := MultisetToSequence(SequenceToMultiset(alledges) diff SequenceToMultiset(complementspan));
  spanningTreeEndPts := [[ss[1],EndpointIndex(ss[1],ss[2],edges)] : ss in spanningTree];

  homology := [];

  // Loop over all edges and add homology if they aren't in the spanning tree,
  //construct homology in the same order as we do the trace (this is important)
  for T in complementspan do
    vi, edgeIndex := Explode(T);
    // This gives a homology element
    loopCoords := FindLoopCoords(vi, edgeIndex, topClusterIndices, vertices, edges, spanningTreeEndPts,ueberevenClusters);
    loop := [<l[1],[spanningTree[l[2]][1],spanningTree[l[2]][2]]> : l in loopCoords];
    loop cat:= [<QQ!1,[vi,edgeIndex]>];
    Append(~homology, loop);
  end for;
  return homology;
end intrinsic;

intrinsic ResidueZeroDifferentials(clusterdata::ClusterDiagram) -> ModMatFld, ., .
  {Return a matrix K such that each row K_i of K gives a differential form of the second kind
  omega_j :=  sum_(i =0)^(i = 2g+1) K_ij x^(i-1) dx/(2y) of residue 0 on all annuli of X}
  fL := clusterdata`Fss;
  f := clusterdata`F;
  clusters := clusterdata`Clusters;
  childrenOfClusters := clusterdata`Children;
  g := (Degree(fL) - 2) div 2; //assuming even degree
  L := BaseRing(fL);
  G := ConstructDualGraph(clusterdata);

  complement := ComplementOfSpanningTree(G);
  vertices := G`Vertices;
  edges := G`Edges;


  res :=[];
  for e in complement do
      eprime := EdgeFromCoords(e, G);
      if IsEven(#clusters[eprime[2]]) then
        Append(~res, EvenResidue(eprime[2], clusterdata)); //a matrix st each row is [res_As x^idx/(2y)]
      else
        Append(~res, OddResidue(eprime[2], clusterdata));
      end if;
  end for;

//want to turn it into a matrix such that each row is [res_As w_i], w_i second kind
    X := HyperellipticCurve(f);
    Xp, rho := ChangeCoordinatesHyp(X);
    KXp := FunctionField(Xp);
    _, _, changeOfBasis := ConstructDifferentials(X, Xp, rho, KXp);
    //this is a change of basis from x^i dx/(2y) to residue zero differentials ie H^1dr on X

  if #res eq 0 then
    Ker := IdentityMatrix(Rationals(), 2*g);
    K := Matrix([ Transpose(ChangeRing(Transpose(changeOfBasis),BaseRing(Ker))*Transpose(Matrix(Ker[i]))) : i in [1 .. Nrows(Ker)]]);
  else
    secondkindres := (ChangeRing(changeOfBasis, BaseRing(Matrix(res))))*Transpose(Matrix(res));
    Ker := Matrix(Basis(Kernel(secondkindres)));
    //K gives the kernel of phi2 (residue zero second kind differentials)
    K := Matrix([ Transpose(ChangeRing(Transpose(changeOfBasis),BaseRing(Ker))*Transpose(Matrix(Ker[i]))) : i in [1 .. Nrows(Ker)]]);
    //now in the originalbasis of x^i dx/2y
  end if;

  inclusion := Transpose(Ker);

  vprintf LocalHeights, 2 : "The change of basis is \n %o \n", changeOfBasis;
  vprintf LocalHeights, 2 : "The kernel is \n %o \n", K;
  vprintf LocalHeights, 2 : "The inclusion is \n %o \n", inclusion;

  return  K, inclusion;
end intrinsic;

intrinsic XsBasisDeRham(sqrtg::RngSerAnnElt, clusterIndex::RngIntElt,clusterdata::ClusterDiagram, g::RngIntElt, prec::RngIntElt) -> .
  {Compute a basis of de Rham cohomology on X_s of genus g, defined by u^2 = g_s(x).
  Here sqrtg is an inverse square root of g_s}

  clusters := clusterdata`Clusters;
  params := clusterdata`AnnulusParameters;
  r0 := params[clusterIndex];
  A := Parent(sqrtg);
  T := A`Generator;
  Xcoord :=  IsEven(#clusters[clusterIndex]) select T+r0 else T^2 + r0;
  spanningset := [((Xcoord)^i/2)*sqrtg : i in [0 .. 2*g]]; //this is not X^i dx/y
  //need to get rid of the -1 coeff on X^i by finding appropriate linear combinations
  residues := [Coefficient(spanningset[i], -1) : i in [1 .. 2*g+1]];
  //We do linear algebra to zero out residues:
  coeffs := Basis(Kernel(Transpose(Matrix([residues]))));
  return coeffs;
end intrinsic;

intrinsic GlobalSymbol1(coeffs1::ModTupFldElt, coeffs2::ModTupFldElt, clusterIndex::RngIntElt, clusterdata::ClusterDiagram) -> FldPadElt
  {FIX NAME  -- this one is for P(x)/(2y) with y on X and Q(x) / (2y) with y  on X_s
  P(x)dx /(2y) and Q(x) dx/(2y)  are two differential forms on U_s, with s cluster of index clusterindex
  each with residue 0 on each annulus A_s' for s'<s proper. return the global symbol
  <(P(x) dx/(2y), Q(x) dx/(2y)> = sum_(s'<s proper)  Res_(A_s') P(x)dx /(2y) * int Q(x) dx/(2y))
  Note that P, Q should be centered at r0 where r0 is the first root in clusters s
  and they are entered as lists of coeffs coeffs1 and coeffs2, where P(x)dx/(2y) = sum_i coeffs1[i]*x^(i-1)dx/(2y)}

  fL := clusterdata`Fss;
  L := clusterdata`SemistableField;
  p := clusterdata`Prime;
  allroots := clusterdata`Roots;

  depthClusters := clusterdata`AbsoluteDepths;
  relDepths := clusterdata`RelativeDepths;
  clusters := clusterdata`Clusters;
  childrenOfClusters := clusterdata`Children;
  squareRootsgs := clusterdata`SquareRootsgs;
  params := clusterdata`AnnulusParameters;
  K := clusterdata`SquareRootsField;
  R_L<x> := PolynomialRing(L);
  R := LaurentPolynomialRing(L, "xL");
  xL := R`Generator;
  r0 := params[clusterIndex];
  topCluster := Index(relDepths, -1);

  if IsEven(#clusters[clusterIndex]) then
    if clusterIndex ne topCluster then
      parentIndex := Parent(clusterIndex,clusterdata);
      outerdepth := depthClusters[parentIndex] + _EPS;
    else
      outerdepth := getTopOuterRadius(clusterdata);
    end if;
    lc := LeadingCoefficient(fL);
    fshifted := lc * &*[xL-r[1] +r0 : r in allroots];
    C := Evaluate(fshifted, L!0);
    Kx := LaurentPolynomialRing(K, "x");
    S := SeriesAnnulusRing(K, depthClusters[clusterIndex] - _EPS, outerdepth, "T" : LaurPolRing := Kx);
    T := S`Generator;
    fshiftedT := Evaluate(fshifted, T);
    sqrtftinv := SquareRoot(fshiftedT : inverse := true, wellDefinedCheck := false);
    sameSign := CompatibleSignF(sqrtftinv,clusterIndex,clusterdata);
    if not sameSign then
      sqrtftinv := -sqrtftinv;
    end if;
  end if;

  for childindex in childrenOfClusters[clusterIndex] cat [clusterIndex] do
    sum := L!0;
    if #clusters[childindex] gt 1 then
      if IsEven(#clusters[childindex]) then
        sqrtsgs := clusterdata`SquareRootsgs;
        sqrtg := sqrtsgs[clusterIndex];
        Sg := Parent(sqrtg);
        T := Sg`Generator;
      else
        if childindex ne topCluster then
          parentindex := Parent(childindex, clusterdata);
          outerdepth := depthClusters[parentindex] + _EPS;
        else
          vprintf LocalHeights, 3 : "This is the top cluster - this may take longer.\n";
          outerdepth := getTopOuterRadius(clusterdata);
        end if;
        gs := R!1;
        clusterset := [c : c in childrenOfClusters[clusterIndex] | IsOdd(#clusters[c]) ];
        r0child := params[childindex];
        usedroots := [];
        for s in clusterset do
          rs := allroots[clusters[s][1]][1]; //pick the first root from each odd child
          if rs eq r0child then
            Append(~usedroots, clusters[s][1]);
            continue;
          end if;
          gs := gs*(xL - rs);
          Append(~usedroots, clusters[s][1]);
        end for;
        gs := Evaluate(gs, xL + r0child);
        C := Evaluate(gs, 0);
        Kx := LaurentPolynomialRing(K, "x_K");
        Sg := SeriesAnnulusRing(K, (depthClusters[childindex] - _EPS)/2, (outerdepth)/2, "T" : LaurPolRing := Kx);
        T := Sg`Generator;
        gsT := Evaluate(gs,T^2);
        sqrtg := SquareRoot(gsT : inverse := true, wellDefinedCheck := false);

        hs_poly := &*[xL - allroots[j][1] : j in [1 ..#allroots] | (j notin usedroots)];
        hs_poly := Evaluate(hs_poly, xL + r0child);
        hsT := Evaluate(hs_poly, T^2);
        sqrths := SquareRoot(hsT : inverse := true, wellDefinedCheck := false);
        sqrtftinv := sqrths * sqrtg;

      end if;
      Xcoord :=  IsEven(#clusters[childindex]) select T+r0 else T^2 + r0; 
      Ps := &+[coeffs1[i]*(Xcoord^(i-1)/2)*sqrtftinv : i in [1..Ncols(coeffs1)]];
      Qs := &+[coeffs2[i]*(Xcoord^(i-1)/2)*sqrtg : i in [1.. Ncols(coeffs2)]];
      IPs := Integrate(Ps);
      prod := Qs*IPs;

      if IsEven(#clusters[childindex]) and childindex ne clusterIndex then
        sum := sum - 2*Coefficient(prod,-1);
      elif childindex ne clusterIndex then
        sum := sum - 4*Coefficient(prod,-1);
      else
        if IsEven(#clusters[clusterIndex]) then
          sum := sum + 2* Coefficient(prod,-1);
        else
          sum := sum + 4*Coefficient(prod,-1);
        end if;
      end if;

    end if;
  end for;
  return sum;

end intrinsic;

intrinsic GlobalSymbol2(coeffs1::ModTupFldElt, coeffs2::ModTupFldElt, clusterIndex::RngIntElt, clusterdata::ClusterDiagram) -> FldPadElt
  {FIX NAME  -- this one is for Q_1(x)/(2y) with y on X_s and Q_2(x) / (2y) with y  on X_s
  Q_1(x)dx /(2y) and Q_2(x) dx/(2y)  are two differential forms on U_s, with s cluster of index clusterindex
  each with residue 0 on each annulus A_s' for s'<s proper. return the global symbol
  <(Q_1(x)dx /(2y), Q_2(x) dx/(2y> = sum_(s'<s proper)  Res_(A_s') Q_1(x)dx /(2y) * int Q_2(x) dx/(2y))
  Note that Q_1, Q_2 should be centered at r0 where r0 is the first root in clusters s
  and they are entered as lists of coeffs coeffs1 and coeffs2, where Q_1(x)dx/(2y) = sum_i coeffs1[i]*x^(i-1)dx/(2y)}

  fL := clusterdata`Fss;
  allroots := clusterdata`Roots;
  L := clusterdata`SemistableField;
  p := clusterdata`Prime;

  depthClusters := clusterdata`AbsoluteDepths;
  relDepths := clusterdata`RelativeDepths;
  clusters := clusterdata`Clusters;
  childrenOfClusters := clusterdata`Children;
  parentindex := Parent(clusterIndex,clusterdata);
  squareRootsgs := clusterdata`SquareRootsgs;
  params := clusterdata`AnnulusParameters;
  topCluster := Index(relDepths, -1);
  r0 := params[clusterIndex];

  R_L<x>:=PolynomialRing(L);
  R := LaurentPolynomialRing(L, "xL");
  xL := R`Generator;

  K := clusterdata`SquareRootsField;

  for childindex in childrenOfClusters[clusterIndex] cat [clusterIndex] do
    sum := L!0;
    if #clusters[childindex] gt 1 then
      if IsEven(#clusters[childindex]) then
        sqrtsgs := clusterdata`SquareRootsgs;
        sqrtg := sqrtsgs[clusterIndex];
      else
        if childindex ne topCluster then
          parentindex := Parent(childindex, clusterdata);
          outerdepth := depthClusters[parentindex] + _EPS;
        else
          outerdepth := getTopOuterRadius(clusterdata);
        end if;
        gs := R!1;
        clusterset := [c : c in childrenOfClusters[clusterIndex] | IsOdd(#clusters[c]) ];
        r0child := params[childindex];
        for s in clusterset do
          rs := allroots[clusters[s][1]][1]; //pick the first root from each odd child
          if IsOdd(#clusters[clusterIndex]) and rs eq r0child then
            continue;
          end if;
          gs := gs*(xL - rs);
        end for;
        gs := Evaluate(gs, xL + r0child);
        C := Evaluate(gs, 0);
        Kx := LaurentPolynomialRing(K, "x_K");
        Sg := SeriesAnnulusRing(K, (depthClusters[childindex] - _EPS)/2, (outerdepth)/2, "T" : LaurPolRing := Kx);
        T := Sg`Generator;
        gsT := Evaluate(gs,T^2);
        sqrtg := SquareRoot(gsT : inverse := true, wellDefinedCheck := false);
      end if;

      Sg := Parent(sqrtg);
      T := Sg`Generator;
      Xcoord :=  IsEven(#clusters[childindex]) select T+r0 else T^2 + r0;

      Ps := &+[coeffs1[i]*(Xcoord^(i-1)/2)*sqrtg : i in [1.. Ncols(coeffs1)]];
      Qs := &+[coeffs2[i]*(Xcoord^(i-1)/2)*sqrtg : i in [1.. Ncols(coeffs2)]];

      intPs := Integrate(Ps);
      prod := Qs*intPs;

      if IsEven(#clusters[childindex]) and childindex ne clusterIndex then
        sum := sum - 2*Coefficient(prod,-1);
      elif childindex ne clusterIndex then
        sum := sum - 4*Coefficient(prod,-1);
      else
        if IsEven(#clusters[clusterIndex]) then
          sum := sum + 2* Coefficient(prod,-1);
        else
          sum := sum + 4*Coefficient(prod,-1);
        end if;
      end if;

    end if;
  end for;
  return sum;

end intrinsic;

function FindBlocks(M, gvlist)
  blocks := [];
  start := 1;
  for v in [1..#gvlist] do
    B := Submatrix(M, [start, start+gvlist[v]*2-1], [start, start+gvlist[v]*2-1]);
    start := start+gvlist[v]*2-1+1;
    Append(~blocks,B);
    vprintf LocalHeights, 1 : "The %oth action on H1(Gamma) is %o.\n", v, B;
  end for;
  return blocks;
end function;


intrinsic Trace(G::DualGraph,Z::Any) -> SeqEnum
  {Trace calculation for higher genus clusters. Here, Z is the action on all of H^1 de Rham.}

  vprint LocalHeights, 1: "Computing Traces";

  cd := G`ClusterDiagram;
  fL := cd`Fss;
  f := cd`F;
  clusters := cd`Clusters;
  childrenOfClusters := cd`Children;
  depthClusters := cd`AbsoluteDepths;

  L := BaseRing(fL);
  prec := Precision(BaseRing(L));
  vertices := G`Vertices;

  genuslist := G`Genus;
  highergenusvertices := [v : v in vertices | genuslist[v[1]] ge 1];
  gvlist := [genuslist[v[1]] : v in highergenusvertices];
  if #highergenusvertices eq 0 then
    return [];
  end if;
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
  M := DescendEndomorphism(ZonM1,directSum);
  blocklist := FindBlocks(M, gvlist);
  vprintf LocalHeights, 1: "The block matrices Z_vi are %o.\n", blocklist;
  traces := [Trace(B) : B in blocklist];
  return traces;

end intrinsic;

//this is sorta Magma's function, but unrestricted types

intrinsic RightInverseMatrixFixed(inc :: .) -> .
{Given the inclusion map of a subspace into a vector space, the
 function returns a matrix pr with the property that inc*pr is
 the identity map on the subspace.}

  E,T := EchelonForm(inc);
  pr := KMatrixSpace(BaseRing(Parent(inc)), Ncols(inc),Nrows(inc))!0;
  for i := 1 to Nrows(inc) do
     for j := 1 to Ncols(inc) do
        if not  IsZero(E[i,j]) then
           pr[j,i] := 1;
           break j;
        end if;
     end for;
  end for;

  return pr*T;

end intrinsic;

intrinsic DescendEndomorphism(Z::., M::.) -> .
  {Z is a square matrix representing an endomorphism V -> V, M is a matrix representing a surjective map V -> W. Throws an error if Z does not descend along M, returns the descent if it does}
  // We assume Z and M act by left multiplication vectors, so Z* and M*
  if BaseRing(Z) cmpeq Integers() then
    Z := ChangeRing(ChangeRing(Z, Rationals()), BaseRing(M)); //??why
  else
    Z := ChangeRing(Z, BaseRing(M));
  end if;
  require Nrows(Z) eq Ncols(Z) : "Z is not a square matrix";
  n := Nrows(Z);
  require Nrows(Z) eq Ncols(M) : "M does not have the correct number of columns";
  K := Kernel(Transpose(M));
  require Dimension(K) eq Ncols(M) - Nrows(M) : "M is not a surjective map";
  for v in Basis(K) do
    require Vector(Z*Transpose(Matrix(v))) in K : "The endomorphism of Z does not respect the kernel of the map";
  end for;
  // Now we construct a right inverse of M
  Minv := RightInverseMatrixFixed(M);
  return (M*Z)*Minv;
end intrinsic;

intrinsic LengthPairing(edges1::SeqEnum,edges2::SeqEnum,G::DualGraph) -> FldRatElt
  {computes <sum edges1, sum edges2>.  Each edge is ei=<coeffi,[vertexIndexi,edgeIndexi]>.
  For edges ei=[vertexIndexi,edgeIndexi], we have
  <e1,e2> = l(e1) if e1=e2; -l(e1) if e1=e2^-1; 0 otherwise}
  edges := G`Edges;
  pairingEdges := function(e1,e2)
    if e1 eq e2 then
      return edges[e1[1]][e1[2]][3];
    else
      return 0;
    end if;
  end function;

  return &+[&+[e1[1]*e2[1]*pairingEdges([e1[2][1],e1[2][2]],[e2[2][1],e2[2][2]]) : e1 in edges1]:e2 in edges2];
end intrinsic;


function projectontou(v, u, G)
  if &and[IsZero(e[1]) : e in u] then
    return 0;
  end if;

  num := LengthPairing(v, u, G);
  den := LengthPairing(u, u, G);
  return [ <num/den  * e[1], e[2]> : e in u ];
end function;


function multiplycoeff(a, v)
  return [ <a  * e[1], e[2]> : e in v ];
end function;

function simplifysum(v)
  simplified_v := [];
  S := { e[2] : e in v };
  for s in S do
    sum_s := &+[e[1] : e in v | e[2] eq s];
    if sum_s ne 0 then
      Append(~simplified_v, <sum_s, s>);
    end if;
  end for;
return simplified_v;
end function;


function CoefficientProjection(v, u, G)
  if &and[IsZero(e[1]) : e in u] then
    return 0;
  end if;
  num := LengthPairing(v, u, G);
  den := LengthPairing(u, u, G);
  return  num/den;
end function;


intrinsic GramSchmidtProcess(basis::SeqEnum, G::DualGraph) -> SeqEnum, ModMatFldElt
{Create an orthogonal basis for the basis under the intersection pairing.}
  b1 := basis[1];
  change_of_basis :=[];
  basis := Remove(basis, 1);
  Append(~change_of_basis, [Rationals()| 1] cat [Rationals()| 0 : i in [1.. #basis]]); //we removed 1 from basis
  orthogbasis := [b1];
  for i->b in basis do
    rowb := [];
    newb := b;
    for j in [1 .. #orthogbasis] do
      Append(~rowb, -LengthPairing(b, orthogbasis[j], G)/LengthPairing(orthogbasis[j], orthogbasis[j], G));
      negproj := multiplycoeff(-1, projectontou(b, orthogbasis[j], G));
      newb cat:= negproj;
    end for;
    Append(~rowb, 1);
    Append(~change_of_basis, rowb cat [0 : j in [1.. #basis - i]]);
    orthogbasis := Append(orthogbasis, simplifysum(newb));
  end for;
  return orthogbasis, Transpose(Matrix(change_of_basis));
end intrinsic;

intrinsic ComputeFstar(basis::SeqEnum, e::SeqEnum, G ::DualGraph, F::.) -> SeqEnum
{Computes F_*(pi(e)) for an edge e, where F is the endomorphism and pi the projection onto the homology of G}

  orthogbasis, change_of_basis := GramSchmidtProcess(basis, G);
  proj := [CoefficientProjection(e,b,G) : b in orthogbasis];

  //F is in the basis given by complement of spanning tree
  //change_of_basis goes from complement of spanning tree to orthonormal basis
  change_of_basis := ChangeRing(change_of_basis, BaseRing(F));
  Fstar := change_of_basis^(-1)* F* change_of_basis;
  Fstarpie := Fstar * Transpose(Matrix(BaseRing(F),[proj]));
  //now Fstarpie is a set of coeffs on orthogbasis, we want to return the vectors with coeffs
  return &cat[multiplycoeff(Eltseq(Fstarpie)[i], orthogbasis[i]) : i in [1 .. #orthogbasis]];
end intrinsic;

intrinsic ConstructActionOnDualGraph(G::DualGraph, Z::.) -> .
  {Given the action of the endomorphism on cohomology, return the action of Z on homology of the dual graph.}

  cd := G`ClusterDiagram;
  clusters := cd`Clusters;
  fL := cd`Fss;
  edges := G`Edges;
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
  M := Matrix(small_residues);
  tr := Trace(Z);
  require IsZero(tr) : "Must use a trace 0 endomorphism";
  ZonHomGraph := DescendEndomorphism(Z,M);
  return ZonHomGraph;
end intrinsic;

intrinsic LaplacianOfHeight(G::DualGraph, M::.) -> SeqEnum
  {Return the Laplacian of the local height given as a sequence of integers
  which are coefficients of ds_e for each edge e. This is not the full Laplacian
  if there are higher genus vertices (i.e. does not include delta measures).}

  edges := G`Edges;
  vertices := G`Vertices;
  allEdges := G`EdgesCoordinates;
  cd := G`ClusterDiagram;
  genuslist := G`Genus;

  homologyBasis := HomologyDualGraph(G);
  if #homologyBasis eq 0 then
    return [Rationals()!0 : edge in allEdges]; 
  end if;
  ZonHomGraph := ConstructActionOnDualGraph(G,M);

  mu_F := [];
  for e in allEdges do
    Fstarpie := ComputeFstar(homologyBasis, [<1,e>], G, ZonHomGraph);
    len_e := EdgeFromCoords(e,G)[3];
    pair := 2*LengthPairing([<1,e>],Fstarpie,G)*1/len_e^2;
    Append(~mu_F,pair);
  end for;

  return mu_F;
end intrinsic;

intrinsic LengthPairingMatrix(G::DualGraph) -> Any
  {Return the matrix with coefficients <e_i,e_j>, where the set e_i is a basis for homology.}

  edges := G`Edges;
  vertices := G`Vertices;
  allEdges := G`EdgesCoordinates;
  cd := G`ClusterDiagram;

  homologyBasis := HomologyDualGraph(G);
  if #homologyBasis eq 0 then
    return Matrix([Rationals()!0]);
  end if;

  intersection := [];
  for elt in homologyBasis do
    Append(~intersection,[LengthPairing(elt,e,G) : e in homologyBasis]);
  end for;

  return Matrix(intersection);
end intrinsic;

intrinsic FindAdjacentEdges(v::RngIntElt,G::DualGraph) -> SeqEnum
  {Given a graph G and the index of a vertex on this graph, return coordinates for all edges adjacent to v}
  edges := G`Edges;
  vertices := G`Vertices;

  adjEdges := [[v,i] : i in [1..#edges[v]]];
  for j in [1..#vertices] do
    adjEdges cat:= [[j,e] : e in [1..#edges[j]] | edges[j][e][1] eq v];
  end for;

  return adjEdges;
end intrinsic;

intrinsic AreAdjacent(v::RngIntElt,w::RngIntElt,G::DualGraph) -> Bool, SeqEnum
  {For vertex indices v and w, return true if they are adjacent (and the edges coordinates)}
  edgesAdj := Set(FindAdjacentEdges(v,G)) meet Set(FindAdjacentEdges(w,G));
  if #edgesAdj eq 0 then
    return false, [];
  else
    return true, SetToSequence(edgesAdj);
  end if;
end intrinsic;

intrinsic WeightedLaplacianMatrix(G::DualGraph) -> Any
  {Returns the nxn weighted Laplacian of the weighted graph G}

  edges := G`Edges;
  vertices := G`Vertices;

  Q := ZeroMatrix(Rationals(),#vertices);
  for v1 in [1..#vertices] do
    for v2 in [1..#vertices] do
      if v1 ne v2 then
        bool, adjEdges := AreAdjacent(v1,v2,G);
        if bool then
          Q[v1][v2] := &+[1/EdgeFromCoords(e,G)[3]: e in adjEdges];
        end if;
      end if;
    end for;
  end for;
  for v in [1..#vertices] do
    Q[v][v] := - &+[Q[i][v] : i in [1..#vertices]|i ne v];
  end for;
  return Q;
end intrinsic;

intrinsic LocalHeights(G::DualGraph, M::., X::CrvHyp : basept := 1, Z:= false) -> SeqEnum
  {Given the dual graph of a curve. M is the matrix on H^0 de rham.
  By default, basept is chosen to be the first vertex of vertices.
  P0 is a rational point used to construct the correspondence in the case of higher genus vertices}

  genuslist := G`Genus;

  if not &and[IsZero(g) : g in genuslist] and Type(Z) eq BoolElt then
    Z := MatrixH1DR(X, M);
  end if;

  ComputeDirectionalDerivative := function(poly,edge,vertex)
    //edge is <vertex,cluster,length>
    R<s> := Parent(poly);
    deriv:= -Evaluate(Derivative(poly),0);
    return deriv;
  end function;

  edges := G`Edges;
  vertices := G`Vertices;
  allEdges := G`EdgesCoordinates;

  mu_F := LaplacianOfHeight(G,M);
  vprintf LocalHeights, 1: "The Laplacian of the height (on ds_e, without the traces) is %o.\n", mu_F;

  //now if we have higher genus components, we have to add these in
  higherGenusVertices := [v : i in [1..#vertices]| genuslist[v[1]] ge 1 where v is vertices[i]];

  traces := Trace(G,Z);
  allTraces := [*0 : i in [1..#vertices]*];
  tr := 0;
  for i in [1 .. #higherGenusVertices] do
    allTraces[higherGenusVertices[i][1]] := traces[i];
    tr +:= traces[i];
  end for;

  vprintf LocalHeights, 1: "The traces for the higher genus vertices are %o.\n", traces;

  require IsZero(&+[mu_F[i]*EdgeFromCoords(e,G)[3]:i -> e in allEdges] + tr): "The total mass is not zero.\n";

  //mu_F = f0 + f1, where f0=C * s*(s- length)
  _<s> := PolynomialRing(Parent(mu_F[1]));
  f0 := [-mu_F[i]/2 * s * (s - EdgeFromCoords(allEdges[i],G)[3]) : i in [1..#allEdges]];

  deltas := [];
  for v in [1..#vertices] do
    adjEdg := FindAdjacentEdges(v,G);
    deltav := -&+[ComputeDirectionalDerivative(f0[Index(allEdges,e)],EdgeFromCoords(e,G),v): e in adjEdg];
    Append(~deltas, deltav);
  end for;
  vprintf LocalHeights, 1: "The delta measures are %o.\n", deltas;
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
  require &and[IsWeaklyZero(check[i][1] - Transpose(Matrix([deltas]))[i][1]): i in [1..Nrows(check)]] : "Unable to find a solution for %o w= %o", Q, deltas;

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
  return htlist;

end intrinsic;

intrinsic ReducePointToDualGraph(P::PtHyp, G::DualGraph) -> SeqEnum
  {Given a point, return the component (vertex) of the dual graph it reduces to
  or else the edge (in coords), and distance along the edge.}

  cd := G`ClusterDiagram;
  abs_depths := cd`AbsoluteDepths;
  rel_depths := cd`RelativeDepths;
  fL := cd`Fss;
  g := (Degree(fL) - 2) div 2;
  allroots := cd`Roots;
  L := cd`SemistableField;
  K := cd`SquareRootsField;
  clusters := cd`Clusters;
  children := cd`Children;
  vertices := G`Vertices;
  edges := G`Edges;
  params := cd`AnnulusParameters;
  sqrtshs := cd`SquareRootshs;

  evenClusters := [(#clusters[i] mod 2) eq 0: i in [1 .. #clusters] ];
  ueberevenClusters := [ evenClusters[i] and &and[evenClusters[j] : j in children[i]] : i in [1 .. #clusters]];
  topCluster := Index(rel_depths,-1);

  if not IsZero(P[3]) then
    x := P[1]/P[3];
    y := P[2]/P[3]^(g+1);
  else
    if ueberevenClusters[topCluster] then
    //a point (X:Y:0) at infinity reduces onto the + component attached to the top cluster if Y/lc^{1/2}X^{g+1} = +1,
    //and reduces onto the - component if Y/lc^{1/2}X^{g+1} = -1.
    lc := LeadingCoefficient(fL);
    if IsWeaklyZero(P[2]/Sqrt((K!(lc))*P[1]^(g+1)) - 1) then
      return [* topCluster, 1, "v" *];
    elif IsWeaklyZero(P[2]/(Sqrt(K!lc)*P[1]^(g+1)) + 1) then
      return [* topCluster, -1, "v" *];
    end if;
    else
      return [* topCluster, 0, "v" *];
    end if;
  end if;

  //Does P belong to U_s for any s in children?
  curr_children := children[topCluster];
  smallest_Us_containing_P := topCluster;

  function CheckChildrenOfS(childset, cluster, x)
    //check if P is contained in Us for any child s in the childset of some cluster
    for s in childset do
      if #children[clusters[s]] eq 1 then
        continue;
      end if;
      r0 := [allroots[j][1] : j in clusters[s]][1]; //pick a parameter in s
      if NormValuation(Parent(r0)!x -  r0) gt abs_depths[cluster] then
        return s;
      end if;
    end for;
     return -1;
  end function;

  smaller_Us := CheckChildrenOfS(curr_children, topCluster, x);
  while smaller_Us ne -1 do
    smallest_Us_containing_P := smaller_Us;
    curr_children := children[smaller_Us];
    smaller_Us := CheckChildrenOfS(curr_children, smaller_Us, x);
  end while;

  r0 := [allroots[j][1] : j in clusters[smallest_Us_containing_P]][1];

  //now check if we lie in the bounding annulus A_s of this smallest U_s
  if NormValuation(x - r0) lt abs_depths[smallest_Us_containing_P] and smallest_Us_containing_P ne topCluster then
    //we belong to A_s, now we want to return an edge, and how far along the edge.
    dist := (abs_depths[smallest_Us_containing_P] - NormValuation(x - r0));
    parentindex := Parent(smallest_Us_containing_P, cd);
    v := Index(vertices, [parentindex, 0] );
    //find edge corresponding to s goes from s to its parent
    if IsOdd(#clusters[smallest_Us_containing_P]) then
      return [* [smallest_Us_containing_P,1], (1/2)*dist, "e" *];
    else
      //check if uebereven, because then we have to satisfy compatibility criterion
      R_L<x> := PolynomialRing(L);
      R := LaurentPolynomialRing(L, "xL");
      xL := R`Generator;
      r0 := params[smallest_Us_containing_P];
      lc := LeadingCoefficient(fL);
      fshifted := lc * &*[xL-r[1] +r0 : r in allroots];
      C := Evaluate(fshifted, L!0);
      Kx := LaurentPolynomialRing(K, "x");
      S := SeriesAnnulusRing(K, abs_depths[smallest_Us_containing_P] - _EPS, abs_depths[parentindex] + _EPS, "T" : LaurPolRing := Kx);
      T := S`Generator;
      fshiftedT := Evaluate(fshifted, T);
      sqrtftinv := SquareRoot(fshiftedT : inverse := true, wellDefinedCheck := false);
      sameSign := CompatibleSignF(sqrtftinv,smallest_Us_containing_P,cd);
      if not sameSign then
        sqrtftinv := -sqrtftinv;
      end if;

      evalsqrtf := Evaluate(sqrtftinv, x - r0); // I think, since x isn't centered

      if IsWeaklyZero(y*evalsqrtf, -1) then
        return [* [smallest_Us_containing_P,1], dist, "e" *];
      elif IsWeaklyZero(y*evalsqrtf + 1) then
        return [* [smallest_Us_containing_P,2], dist, "e" *];
      else
        error "The value %o does not equal -1 or 1.\n", y*evalsqrtf;
      end if;
    end if;
  else //not in A_s
    if ueberevenClusters[smallest_Us_containing_P] then
        sqrth_factored := sqrtshs[smallest_Us_containing_P];
        children_of_s := children[smallest_Us_containing_P];
        evalsqrth := 1;
        for i->c in children_of_s do
          ri := params[c];
          evalsqrth *:= Evaluate(sqrth_factored[i], x - ri); //since x isn't centered
        end for;
      if IsWeaklyZero(y*evalsqrth -1) then
          return [* smallest_Us_containing_P, 1, "v" *];
      elif IsWeaklyZero(y*evalsqrth + 1) then
         return [* smallest_Us_containing_P, -1, "v" *];
      else
        error "The value %o does not equal -1 or 1.\n", y*evalsqrth;
      end if;
    else
      return [* smallest_Us_containing_P, 0, "v" *]; //the vertex that P reduces to
    end if;
  end if;

end intrinsic;


intrinsic HeightsAtRationalPoints(G::DualGraph, M::.,  X::CrvHyp : basept := 1, Z:= false) -> SeqEnum
  {Given the dual graph of the curve, the matrix of the endomorphism on H^0 de rham, and the curve,
  return the local height evaluated at each known rational point.
  By default, basept is chosen to be the first vertex of the vertices.
  P0 is an optional rational point used to construct the correspondence in the case of higher genus vertices}

  cd := G`ClusterDiagram;
  edges := G`Edges;
  vertices := G`Vertices;
  edgescoords := G`EdgesCoordinates;
  anyedge := edgescoords[1];
  f := cd`F;
  ht_fn := LocalHeights(G, M, X : basept := basept, Z:= Z);
  vprintf LocalHeights, 1: "The height functions on the edges are %o.", ht_fn;
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
  return htsatpoints;
end intrinsic;
