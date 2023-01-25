module TestPBPO 

using Test
using AlgebraicRewriting
using Catlab, Catlab.CategoricalAlgebra, Catlab.Graphs, Catlab.Graphics
const hom = homomorphism
const homs = homomorphisms
using AlgebraicRewriting.Rewrite.Utils: get_matches

# Example from Fig. 7 of "A PBPO+ Graph Rewriting Tutorial"
###########################################################
"""
The pattern L requires any host graph GL to contain three nodes, and two of
these nodes have an edge targeting the third node. This example illustrates 
application conditions, duplicating and deleting elements, identifying and 
adding elements, and edge redirection.
"""

L = @acset Graph begin V=3;E=2;src=[1,3];tgt=[2,2] end 
K = Graph(5)
R = @acset Graph begin V=4;E=1;src=4;tgt=4 end
l = CSetTransformation(K,L;V=[1,2,2,3,1])
r = CSetTransformation(K,R;V=[1,2,4,1,4])
L′ = @acset Graph begin V=4;E=7;src=[1,1,2,2,3,4,4];tgt=[2,4,1,3,2,3,4] end
K′ = @acset Graph begin V=6;E=5;src=[1,2,3,5,6];tgt=[5,1,4,5,5] end
tl = hom(L,L′; initial=(V=[1,2,3],))
tk = CSetTransformation(K,K′; V=[1,2,3,4,6])
l′ = hom(K′,L′; initial=(V=[1,2,2,3,4,1],))
rule = PBPORule(l,r,tl,tk,l′)

G = @acset Graph begin V=5;E=11;
  src=[1,1,1,2,2,2,3,4,5,5,5]; tgt=[2,4,5,1,3,3,2,5,3,3,5] 
end

res = rewrite(rule,G; initial=(V=[1,2,3],)=>(V=[1,2,3,4,4],))
expected = @acset Graph begin V=6;E=10;
  src=[1,3,3,4,5,6,6,6,6,6];tgt=[3,4,5,5,5,3,3,4,5,6] 
end
@test is_isomorphic(res, expected) && is_isomorphic(res, rewrite(rule, G))
@test length(get_matches(rule, G)) == 1

# Example from Fig 15 of "Graph Rewriting and Relabeling with PBPO+"
####################################################################
"""
This example illustrates (i) how permitted patches can be constrained (e.g.,
L′ forbids patch edges targeting y), (ii) how patch edge endpoints that lie in the
image of tL can be redefined, (iii) how patch edges can be deleted, and (iv) how
patch edges can be duplicated.
"""
L = path_graph(Graph, 2)
K = Graph(3)
R = @acset Graph begin V=3;E=1;src=2;tgt=2 end
l = CSetTransformation(K,L; V=[1,1,2])
r = CSetTransformation(K,R; V=[1,2,1])
L′ = @acset Graph begin V=3;E=5; src=[1,2,2,3,3];tgt=[2,1,3,1,3] end
K′ = @acset Graph begin V=4;E=4;src=[3,3,4,4];tgt=[2,2,1,4] end
tl = hom(L,L′; initial=(V=[1,2],))
tk = CSetTransformation(K,K′; V=[1,2,3])
l′ = hom(K′,L′; initial=(V=[1,1,2,3],));
rule = PBPORule(l,r,tl,tk,l′)

G = @acset Graph begin V=5; E=8; 
  src=[1,2,2,2,4,4,5,5]; tgt=[2,1,1,5,1,5,1,4] 
end

expected = @acset Graph begin V=6;E=9;
  src=[1,1,1,1,2,4,4,5,5];tgt=[2,2,2,2,2,1,5,1,4] 
end
@test is_isomorphic(rewrite(rule, G), expected)

# Modification of example from slide 68 of "An introduction to graph rewriting"
##############################################################################
L = Graph(1)
K = R = Graph(2)
l = hom(K,L)
r = id(K)

# 1 = root of the deep copy, 2 = children of #1, 3 = everything else 
L′ = @acset Graph begin V=3;E=5;src=[1,2,3,3,3];tgt=[2,2,1,2,3] end
tl = ACSetTransformation(L,L′;V=[1])
K′ = @acset Graph begin V=5;E=9 ;src=[1,2,3,3,4,3,5,3,3];tgt=[2,2,3,2,5,5,5,1,4] end
tk = ACSetTransformation(K,K′;V=[1,4])
l′ = hom(K′,L′; initial=(V=[1,2,3,1,2],))

"""      ∀₂                  ∀₂
    [•] ---> G         [•] ---> G
    ₄↓  ↗∃₃  ↓ λ₁  or  ₄↓  ↗∃₃  ↓ λ₁
   [•→•] --> L′       [•→•] --> L′
    1 2  ⁵            2 2    ⁶
"""
G1, arr = Graph(1), path_graph(Graph,2)
vertical = ACSetTransformation(G1, arr; V=[2])
bottom_5 = hom(arr, L′; initial=(V=[1,2],))
bottom_6 = hom(arr, L′;initial=(V=[2,2],))

cg = @acset CGraph begin V=4; E=6; src=[2,1,3,1,3,3]; tgt=[3,2,2,3,4,4];
  vlabel=[G1, nothing, arr, L′]; 
  elabel=[AttrVar(1), nothing,  nothing, vertical, bottom_5, bottom_6]
end

expr = Forall(2, Exists(3, 
                        BoolAnd(Commutes([4,3],[2]), 
                                BoolOr(Commutes([3,1],[6]),Commutes([3,1],[5]))));
              st=Commutes([2,1],[4,5]))


lc = Constraint(cg, expr)
rule = PBPORule(l,r,tl,tk,l′; lcs = [lc])

G = @acset Graph begin V=8; E=8; src=[1,1,2,2,3,4,4,5]; tgt=[2,3,4,5,6,5,7,8] end
ms = get_matches(rule,G; initial=Dict(:V=>[2])=>Dict()) 

G′ = rewrite_match(rule, only(ms))
G′′ = rewrite(rule, G; initial=Dict(:V=>[2])=>Dict())
expected = @acset Graph begin V=13;E=14;
  src=[7,7,7,1,1,3,3,4,2,2,10,10,11,8];tgt=[1,2,8,3,4,5,4,6,10,11,12,11,13,9] 
end
@test is_isomorphic(expected,G′) && is_isomorphic(G′,G′′)

# Example 20 from "Graph Rewriting and Relabeling with PBPO+"
#############################################################
L = apex(terminal(Graph))
K = R = Graph(1)
l = hom(K,L)
r = hom(K,R)
L′ = L ⊕ L 
K′ = K ⊕ L 
tl = hom(L,L′)
tk = hom(K,K′)
l′ = hom(K′,L′; initial=(V=[1,2],)) 
rule = PBPORule(l,r,tl,tk,l′)

G = @acset Graph begin V=3;E=5;src=[1,2,3,1,2];tgt=[1,2,3,2,3] end

# We can only remove self loops from isolated edges
@test isempty(get_matches(rule, G))

G2 = G⊕L
res = rewrite_match(rule, only(get_matches(rule, G2)))
expected = G ⊕ Graph(1)

# Modify to allow incident *tgt* on self loop vertex
L = apex(terminal(Graph))
K = R = Graph(1)
l = hom(K,L)
r = hom(K,R)
L′ = @acset Graph begin V=2; E=3; src=[1,2,2]; tgt=[1,2,1] end 
K′ = @acset Graph begin V=2; E=2; src=[2,2]; tgt=[2,1] end 
tl = hom(L,L′)
tk = CSetTransformation(K,K′; V=[1])
l′ = hom(K′,L′; initial=(V=[1,2],))
rule = PBPORule(l,r,tl,tk,l′)
@test length(get_matches(rule,G)) == 1
expected = @acset Graph begin V=3;E=4;src=[1,2,1,2];tgt=[1,2,2,3] end 
@test is_isomorphic(rewrite(rule, G), expected)

# Attributed problem
##############################################################################
const WG = WeightedGraph{Float64}

L = @acset WG begin V=2; E=1; Weight=1; src=1; tgt=2; weight=[AttrVar(1)] end
K = WG(2)
R = WG(1)
l = hom(K, L; monic=true)
r = hom(K, R)
L′ = @acset WG begin V=4; E=10; Weight=10;
  src=[1,1,2,3,3,3,3,4,4,4]; tgt=[2,4,4,1,4,3,2,2,3,4]; weight=AttrVar.(1:10)
end
tl = hom(L, L′)
K′ = @acset WG begin V=4; E=9; Weight=9;
  src=[1,2,3,3,3,3,4,4,4]; tgt=[4,4,1,4,3,2,2,3,4]; weight=AttrVar.(1:9)
end
tk = ACSetTransformation(K, K′; V=[1,2])
l′ = hom(K′,L′; monic=true, initial=(V=[1,2,3,4],)) 

loop = @acset WG begin V=1;E=1;Weight=1;src=1;tgt=1;weight=[AttrVar(1)]end 
ac = AppCond(homomorphism(L,loop), false) # cannot bind pattern to loop

"""
        ∀
   [•] ----> G 
   s↓   ↗∃   ↓ λ
   [•→•] ↪ [↻•→•->• ]
           [ ↖↘↓ ↗↙ ]
           [   •    ]

"""
lc = LiftCond(homomorphism(R,L), # vertical
              homomorphism(L,L′;initial=(E=[4],)))

kx = Any[fill(nothing, 9)...]
kx[3] =  ((x,vs))->x*vs[1]
rule = PBPORule(l,r,tl,tk,l′; k_expr=(Weight=kx,),acs=[ac], lcs=[lc])

G = @acset WG begin V=5; E=7; src=[1,3,4,3,3,4,5]; tgt=[2,1,1,4,5,2,2]; 
  weight=[2.,3.,4.,5.,6.,7.,9.] 
end
expected = @acset WG begin V=4; E=6; src=[2,2,2,3,3,4]; tgt=[1,3,4,1,1,1]; 
  weight=[6.,5.,6.,8.,7.,9.]
end
@test is_isomorphic(expected, rewrite(rule,G))

# Test canonization: TODO

end # module
