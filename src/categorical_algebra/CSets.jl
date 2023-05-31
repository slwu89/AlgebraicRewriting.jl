module CSets
export extend_morphism, pushout_complement,
       can_pushout_complement, dangling_condition, invert_hom, check_pb,
       gluing_conditions, extend_morphisms, postcompose_partial, sub_vars,
       Migrate, invert_iso, deattr, var_pullback, remove_freevars

using Catlab, Catlab.Theories, Catlab.Schemas
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.FinSets: IdentityFunction, VarSet
using Catlab.CategoricalAlgebra.Chase: extend_morphism, extend_morphism_constraints
using Catlab.CategoricalAlgebra.CSets: unpack_diagram, type_components, abstract_attributes
import ..FinSets: pushout_complement, can_pushout_complement, id_condition
import Catlab.ACSetInterface: acset_schema
import Catlab.CategoricalAlgebra.FinSets: predicate
import Catlab.CategoricalAlgebra: is_natural, Slice, SliceHom, components,
                                  LooseACSetTransformation, homomorphisms, 
                                  homomorphism
using Catlab.DenseACSets: attrtype_type, datatypes, constructor

import Base: getindex
using DataStructures: OrderedSet
using StructEquality

# Morphism search 
#################

"""
Given a span of morphisms, we seek to find morphisms B → C that make a
commuting triangle if possible.

    B
 g ↗ ↘ ?
 A ⟶ C
   f
  
Accepts homomorphism search keyword arguments to constrain the Hom(B,C) search.
"""
function extend_morphisms(f::ACSetTransformation, g::ACSetTransformation;
                          initial=Dict(), kw...
                          )::Vector{ACSetTransformation}
  init = combine_dicts!(extend_morphism_constraints(f,g), initial)
  isnothing(init) ? [] : homomorphisms(codom(g), codom(f); initial=init, kw...)
end
 
"""
Combine a user-specified initial dict with that generated by constraints
`Initial` could contain vectors or int-keyed dicts as its data for each object.  
"""
function combine_dicts!(init, initial)
  if isnothing(init) return nothing end
  for (k,vs) in collect(initial)
    for (i, v) in (vs isa AbstractVector ? enumerate : collect)(vs)
      if haskey(init[k], i)
        if init[k][i] != v return nothing end 
      else 
        init[k][i]  = v 
      end
    end
  end
  return NamedTuple(init)
end 

# default behavior for types that don't explicitly implement `is_isomorphic`
is_isomorphic(x) = is_monic(x) && is_epic(x) # should be upstreamed
"""
Convert a morphism X->A to a morphism L->H using a partial morphism G->H, 
if possible.

       A ↩ C → B
       ↑   ↑ 
       X ↩⌜Y
         ≅

This is a more categorical way to compute `update_agent` but for now will 
remain unused unless we want to generalize rewriting schedules beyond ACSet 
rewriting.
"""
function postcompose_partial(ACB::Span, XA::ACSetTransformation)
  S = acset_schema(dom(XA))
  YX, YC = var_pullback(Cospan(XA, left(ACB)))
  if all(o->is_isomorphic(YX[o]), ob(S))
    return invert_iso(YX) ⋅ YC ⋅ right(ACB)
  end
end


"""
Invert some (presumed iso) components of an ACSetTransformation (given by s)
"""
function invert_iso(f::ACSetTransformation,
                    s::Union{Nothing,AbstractVector{Symbol}}=nothing)
  S = acset_schema(dom(f))
  s_obs = isnothing(s) ? ob(S) : s
  d = Dict(map(ob(S)) do o 
    o => o ∈ s_obs ? Base.invperm(collect(f[o])) : collect(f[o])
  end)
  return only(homomorphisms(codom(f), dom(f); initial=d))
end

"""
Invert a morphism which may not be monic nor epic. When the morphism is not 
monic, an arbitrary element of the preimage is mapped to. When it is not epic,
a completely arbitrary element is mapped to.
"""
function invert_hom(f::ACSetTransformation; epic::Bool=true,
                    monic::Bool=true, check::Bool=false)
  S = acset_schema(dom(f))
  !check || is_natural(f) || error("inverting unnatural hom")
  if epic && monic return invert_iso(f) end # efficient
  A, B = dom(f), codom(f)
  d = NamedTuple(Dict{Symbol, Vector{Int}}(map(ob(S)) do o 
    o => map(parts(B, o)) do b
      p = preimage(f[o], b)
      if length(p) == 1 return only(p)
      elseif length(p) > 1 return monic ? error("f not monic") : first(p)
      else return epic ? error("f not epic") : 1
      end
    end
  end))

  d2 = NamedTuple(Dict(map(attrtypes(S)) do o 
    o => map(parts(B, o)) do b
      p = preimage(f[o], AttrVar(b))
      if length(p) == 1 return AttrVar(only(p))
      elseif length(p) > 1 return monic ? error("f not monic") : first(p)
      else return epic ? error("f not epic") : AttrVar(1)
      end
    end
  end))
  return ACSetTransformation(B, A; merge(d,d2)...)
end

"""
 Y
  i↘  f_
    X → •
 g_ ↓ ⌟ ↓ f
    • → •   
      g

Check whether (X, f_,g_) is the pullback of (f,g), up to isomorphism (i.e. the 
pullback of f and g produces (Y,π₁,π₂), where Y is isomorphic to X and 
i⋅f_ = π₁ & i⋅g_ = π₂.
"""
function check_pb(f,g,f_,g_)
  @info "checking pb with f $f\ng $g\nf_ $f_\ng_ $g_"
  codom(f)==codom(g) || error("f,g must be cospan")
  dom(f_)==dom(g_)   || error("f_,g_ must be span")
  codom(f_)==dom(f)  || error("f_,f must compose")
  codom(g_)==dom(g)  || error("g_,g must compose")

  pb_check = limit(Cospan(f, g))
  @info "apex(pb_check) $(apex(pb_check))"
  isos = isomorphisms(apex(pb_check), dom(f_))
  return any(isos) do i
    all(zip(force.(legs(pb_check)), [f_, g_])) do (leg, h)
      i ⋅ h == leg
    end
  end 
end

# Pushout complement
####################

""" Compute pushout complement of attributed C-sets, if possible.

The pushout complement is constructed pointwise from pushout complements of
finite sets. If any of the pointwise identification conditions fail (in FinSet),
this method will raise an error. If the dangling condition fails, the resulting
C-set will be only partially defined. To check all these conditions in advance,
use the function [`can_pushout_complement`](@ref).

Because Subobject does not work well with AttrVars, a correction is made
"""
function pushout_complement(pair::ComposablePair{<:ACSet, <:TightACSetTransformation})
  p1,p2 = pair 
  I,G = dom(p1), codom(p2)
  S = acset_schema(I)
  # Compute pushout complements pointwise in FinSet.
  components = NamedTuple(Dict([o=>pushout_complement(ComposablePair(p1[o],p2[o])) 
                                for o in types(S)]))
  k_components, g_components = map(first, components), map(last, components)

  # Reassemble components into natural transformations.
  g = hom(Subobject(G, NamedTuple(Dict(o=>g_components[o] for o in ob(S)))))
  K = dom(g)
  
  for at in attrtypes(S)
    add_parts!(K, at, codom(k_components[at]).n)
  end

  for (a, d, at) in attrs(S)
    # force k to be natural
    for p in parts(I, d)
      K[k_components[d](p),a] = k_components[at](I[p, a])
    end
    # force g to be natural 
    for p in parts(K, d)
      gval = G[g_components[d](p), a]
      preim = preimage(g_components[at], gval)
      if !isempty(preim) && gval isa AttrVar
        K[p,a] = AttrVar(only(preim))
      end
    end
  end 

  k = ACSetTransformation(I, K; k_components...)
  g = ACSetTransformation(K, G; g_components...)

  force(compose(k,g)) == force(compose(p1,p2)) || error("Square doesn't commute")
  is_natural(k) || error("k unnatural")
  is_natural(g) || error("g unnatural")
  return ComposablePair(k, g)
end


function can_pushout_complement(pair::ComposablePair{<:ACSet})
  S = acset_schema(dom(pair))
  Ts = datatypes(dom(pair))

  all(can_pushout_complement, unpack_diagram(pair; S=S, Ts=Ts)) &&
    isempty(dangling_condition(pair))
end

gluing_conditions(pair::ComposablePair{<:Slice}) =
  gluing_conditions(ComposablePair(pair[1].f, pair[2].f))

"""Check both id condition and dangling condition"""
function gluing_conditions(pair::ComposablePair{<:ACSet})
  viols = []
  S = acset_schema(dom(pair))
  Ts = datatypes(dom(pair))
  for (k,x) in pairs(unpack_diagram(pair; S=S, Ts=Ts))
    a,b = collect.(id_condition(x))
    append!(viols, [("Id: nondeleted ↦ deleted ", k, aa) for aa in a])
    append!(viols,[("Id: nonmonic deleted", k, bb) for bb in b])
  end
  append!(viols, [("Dangling", d...) for d in dangling_condition(pair)])
  return viols
end


"""    pushout_complement(f::SliceHom, g::SliceHom)
Compute a pushout complement in a slice category by using the pushout complement
in the underlying category.

     f
  B <-- A ---⌝
  | ↘ ↙      |
 g|  X       | f′
  ↓ ↗  ↖ cx  |
  D <--- C <--
      g′

"""
function pushout_complement(fg::ComposablePair{Slice})
    f, g = fg
    f′, g′ = pushout_complement(ComposablePair(f.f, g.f))
    D = codom(g)
    C = Slice(compose(g′, D.slice))
    return SliceHom(dom(f), C, f′) => SliceHom(C, D, g′)
end

""" Pushout complement: extend composable pair to a pushout square.

[Pushout complements](https://ncatlab.org/nlab/show/pushout+complement) are the
essential ingredient for double pushout (DPO) rewriting.
"""
pushout_complement(f, g) = pushout_complement(ComposablePair(f, g))

""" Can a pushout complement be constructed for a composable pair?

Even in nice categories, this is not generally possible.
"""
can_pushout_complement(f, g) = can_pushout_complement(ComposablePair(f, g))

"""
Check the dangling condition for a pushout comlement: m doesn't map a deleted
element d to an element m(d) ∈ G if m(d) is connected to something outside the
image of m.

For example, in the C-Set of graphs,

   e1
v1 --> v2

if e1 is not matched but either v1 or v2 are deleted, then e1 is dangling.
"""
function dangling_condition(pair::ComposablePair{<:ACSet})
  S = acset_schema(dom(pair))
  l, m = pair
  orphans = Dict(map(ob(S)) do o
    l_comp,m_comp = l[o], m[o]
    image = Set(collect(l_comp))
    o=>Set([ m_comp(x) for x in codom(l_comp) if x ∉ image ])
  end)
  # check that for all morphisms in C, we do not map to an orphan
  results = Tuple{Symbol,Int,Int}[]
  for (morph, src_obj, tgt_obj) in homs(S)
    n_src = parts(codom(m), src_obj)
    unmatched_vals = setdiff(n_src, collect(m[src_obj]))
    unmatched_tgt = map(x -> codom(m)[x,morph], collect(unmatched_vals))
    for unmatched_val in setdiff(n_src, collect(m[src_obj]))  # G/m(L) src
      unmatched_tgt = codom(m)[unmatched_val,morph]
      if unmatched_tgt in orphans[tgt_obj]
        push!(results, (morph, unmatched_val, unmatched_tgt))
      end
    end
  end
  results
end

# Subobjects
############

function predicate(A::Subobject{VarSet{T}}) where T
  f = hom(A)
  pred = falses(length(codom(f)))
  for x in dom(f)
    pred[f(x)] = true
  end
  pred
end

"""Modification of `Subobject` to have proper behavior with variables"""
function subobj(X::ACSet, d)
  S = acset_schema(X)
  sX = Subobject(X; d...) |> hom |> dom # has no variables 
  for d in attrtypes(S) 
    add_parts!(sX, d, nparts(X,d))
  end
  sX′, _ = remove_freevars(sX)
  return only(homomorphisms(sX′, X; initial=d))
end

"""Recursively include anything, e.g. and edge includes its vertices """
function complete_subobj(X::ACSet, sub)
  sub = Dict([k=>Set(v) for (k,v) in pairs(sub)])
  S = acset_schema(X)
  change = true 
  while change
    change = false 
    for (f,c,d) in homs(S)
      new_d = setdiff(Set(X[collect(sub[c]),f]), sub[d])
      if !isempty(new_d)
        change = true 
        union!(sub[d], new_d)
      end
    end
  end 
  return Dict([k=>collect(v) for (k,v) in pairs(sub)])
end 
"""Recursively delete anything, e.g. deleting a vertex deletes its edge"""
function cascade_subobj(X::ACSet, sub)
  sub = Dict([k=>Set(v) for (k,v) in pairs(sub)])
  S = acset_schema(X)
  change = true 
  while change
    change = false 
    for (f,c,d) in homs(S)
      for c_part in sub[c]
        if X[c_part,f] ∉ sub[d]
          change = true 
          delete!(sub[c], c_part)
        end
      end
    end
  end 
  return Dict([k => collect(v) for (k,v) in pairs(sub)])
end

  
  
# Variables
###########

"""
Given a value for each variable, create a morphism X → X′ which applies the 
substitution. We do this via pushout. 

`subs` is a dictionary (keyed by attrtype names) of int-keyed dictionaries
"""
function sub_vars(X::ACSet, subs::AbstractDict) 
  S = acset_schema(X)
  O, C = [constructor(X)() for _ in 1:2]
  ox_, oc_ = Dict(), Dict()
  for at in attrtypes(S)
    d = get(subs, at, Dict())
    ox_[at] = AttrVar.(filter(p->p ∈ keys(d) && !(d[p] isa AttrVar), parts(X,at)))
    oc_[at] = [d[p.val] for p in ox_[at]]
    add_parts!(O, at, length(oc_[at]))
  end 
  ox = ACSetTransformation(O,X; ox_...)
  oc = ACSetTransformation(O,C; oc_...)
  return first(legs(pushout(ox, oc)))
end 

# """
# For any ACSet, X, a canonical map A→X where A has distinct variables for all
# subparts.
# """
# function abstract(X::StructACSet{S,Ts}; check::Bool=false) where {S,Ts} 
#   A = deepcopy(X); 
#   comps = Dict{Any,Any}(map(attrtypes(S)) do at
#     rem_parts!(A, at, parts(A,at))
#     comp = Union{AttrVar,attrtype_instantiation(S,Ts,at)}[]
#     for (f, d, _) in attrs(S; to=at)
#       append!(comp, A[f])
#       A[f] = AttrVar.(add_parts!(A, at, nparts(A,d)))
#     end 
#     at => comp
#   end)
#   for o in ob(S) comps[o]=parts(X,o) end
#   res = ACSetTransformation(A,X; comps...)
#   !check || is_natural(res) || error("bad abstract $comps")
#   return res
# end 


"""
Take an ACSet pullback combinatorially and freely add variables for all 
attribute subparts.

TODO do var_limit, more generally

This relies on implementation details of `abstract`.
"""
function var_pullback(c::Cospan{<:StructACSet{S,Ts}}) where {S,Ts}
  f, g = deattr.(c)
  legs = pullback(f,g)
  new_apex = typeof(dom(first(c)))()
  copy_parts!(new_apex, dom(first(legs))) # has everything except attributes
  for at in attrtypes(S) add_part!(new_apex, at) end 
  for (at,c,_) in attrs(S) 
    new_apex[:,at] = fill(AttrVar(1), nparts(new_apex,c))
  end 
  A = abstract_attributes(new_apex)
  map(zip(legs,c)) do (p,f)
    X = dom(f)
    attr_components = Dict(map(attrtypes(S)) do at
      comp = Union{AttrVar,attrtype_instantiation(S,Ts,at)}[]
      for (f, c, _) in attrs(S; to=at)
        append!(comp, X[f][collect(A[c]⋅p[c])])
      end
      return at => comp
    end)
    ACSetTransformation(dom(A),X; components(p)...,attr_components...)
  end
end


"""
We may replace some ...
"""
function remove_freevars(X::StructACSet{S}) where S 
  X = deepcopy(X)
  d = Dict(map(attrtypes(S)) do at
    vs = Set{Int}()
    for f in attrs(S; to=at, just_names=true)
      for v in filter(x->x isa AttrVar, X[f])
        push!(vs, v.val)
      end
    end
    # Get new variable IDs 
    svs = sort(collect(vs))
    vdict = Dict(v=>k for (k,v) in enumerate(svs))
    n_v = length(vdict)
    rem_parts!(X,at, parts(X,at)[n_v+1:end])
    for f in attrs(S; to=at, just_names=true)
      for (v,fv) in filter(v_->v_[2] isa AttrVar,collect(enumerate(X[f])))
        X[v,f] = AttrVar(vdict[fv.val])
      end
    end
    return at => svs
  end)
  return X => d
end 

function remove_freevars(f::ACSetTransformation; check::Bool=false)
  S = acset_schema(dom(f))
  !check || is_natural(f) || error("unnatural freevars input")
  X, d = remove_freevars(dom(f))
  comps = Dict{Symbol,Any}(o=>collect(f[o]) for o in ob(S))
  for at in attrtypes(S)
    comps[at] = collect(f[at])[d[at]]
  end 
  res = ACSetTransformation(X, codom(f); comps...)
  !check || is_natural(res) || error("unnatural freevars output")
  return res 
end

function deattr(X::StructACSet{S})::AnonACSet where S
  P = Presentation(FreeSchema)
  add_generators!(P, Ob(FreeSchema, objects(S)...))
  for (h,s,t) in homs(S)
    add_generator!(P, Hom(h, Ob(FreeSchema,s), Ob(FreeSchema,t)))
  end
  aa = AnonACSet(P) # indexing?
  copy_parts!(aa, X)
  return aa
end 

function deattr(f::ACSetTransformation)
  X, Y = deattr.([dom(f),codom(f)])
  S = acset_schema(X)
  return ACSetTransformation(X,Y; Dict(o=>f[o] for o in ob(S))...)
end 

# Slices
########
acset_schema(x::Slice) = acset_schema(dom(x))
is_natural(x::SliceHom) = is_natural(x.f)
components(x::SliceHom) = components(x.f)
Base.getindex(x::SliceHom, c) = x.f[c]

"""
This could be made more efficient as a constraint during homomorphism finding.
"""
function homomorphisms(X::Slice,Y::Slice; kw...)
  map(filter(h->force(X.slice)==force(h⋅Y.slice),
         homomorphisms(dom(X), dom(Y); kw...)) ) do h
    SliceHom(X, Y, h)
  end |> collect
end

function homomorphism(X::Slice,Y::Slice; kw...)
  hs = homomorphisms(X,Y; kw...)
  return isempty(hs) ? nothing : first(hs)
end

# Simple Δ migrations (or limited case Σ)
#########################################

"""To do: check if functorial"""
@struct_hash_equal struct Migrate
  obs::Dict{Symbol, Symbol}
  homs::Dict{Symbol, Symbol}
  T1::Type 
  T2::Type 
  delta::Bool 
  Migrate(o,h,t1,t2=nothing; delta::Bool=true) = new(
    Dict(collect(pairs(o))),Dict(collect(pairs(h))),t1,isnothing(t2) ? t1 : t2, delta)
end 

(F::Migrate)(d::Dict{V,<:ACSet}) where V = Dict([k=>F(v) for (k,v) in collect(d)])
(F::Migrate)(d::Dict{<:ACSet,V}) where V = Dict([F(k)=>v for (k,v) in collect(d)])
(m::Migrate)(::Nothing) = nothing
function (m::Migrate)(Y::ACSet)
  if m.delta
     typeof(Y) <: m.T1 || error("Cannot Δ migrate a $(typeof(Y))")
  end
  S = acset_schema(Y)
  X = m.T2()
  partsX = Dict(c => add_parts!(X, c, nparts(Y, get(m.obs,c,c)))
                for c in ob(S) ∪ attrtypes(S))
  for (f,c,d) in homs(S)
    set_subpart!(X, partsX[c], f, partsX[d][subpart(Y, get(m.homs,f,f))])
  end
  for (f,c,_) in attrs(S)
    set_subpart!(X, partsX[c], f, subpart(Y, get(m.homs,f,f)))
  end
  if !m.delta 
    # undefined attrs (Σ migration) get replaced with free variables
    for (f,c,d) in attrs(acset_schema(X))
      for i in setdiff(parts(X,c), X.subparts[f].m.defined)
        X[i,f] = AttrVar(add_part!(X,d))
      end
    end
  end 
  return X
end 

function (F::Migrate)(f::ACSetTransformation)
  S = acset_schema(dom(f))
  d = Dict(map(collect(pairs(components(f)))) do (k,v)
    get(F.obs,k,k) => collect(v)
  end)
  only(homomorphisms(F(dom(f)), F(codom(f)), initial=d))
end

(F::Migrate)(s::Multispan) = Multispan(apex(s), F.(collect(s)))
(F::Migrate)(s::Multicospan) = Multicospan(apex(s), F.(collect(s)))
(F::Migrate)(d::AbstractDict) = Dict(get(F.obs,k, k)=>v for (k,v) in collect(d))

end # module
