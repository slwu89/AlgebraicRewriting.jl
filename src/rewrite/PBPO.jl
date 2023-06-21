module PBPO 
export PBPORule

using Catlab, Catlab.CategoricalAlgebra
import Catlab.CategoricalAlgebra: left, right
using Catlab.CategoricalAlgebra.CSets: backtracking_search, abstract_attributes

using StructEquality

using ..Utils
import ..Utils: 
  rewrite_match_maps, get_matches, get_expr_binding_map, AbsRule, ruletype
using ..Constraints
using ...CategoricalAlgebra
using ...CategoricalAlgebra.CSets: 
  extend_morphism_constraints, var_pullback, remove_freevars, 
  combine_dicts!
  

"""
      l    r 
   L  ⟵ K ⟶ R 
tl ↓     ↓ tk     <== tl, tk must be monic 
   L' ⟵ K'

It is assumed we never want the typing/adherence match to be monic, but we 
can optionally restrict the match L → G to be monic.

We can attach application conditions to both the match morphism as well as the 
adherence morphism. Until morphism search under constraints becomes efficient,
it's sometimes needed to just directly state the adherence morphism as a 
function of the match morphism.
"""
@struct_hash_equal struct PBPORule <: AbsRule
  l::ACSetTransformation
  r::ACSetTransformation
  tl::ACSetTransformation
  tk::ACSetTransformation
  l′::ACSetTransformation
  monic::Union{Bool, Vector{Symbol}}
  acs::Vector{Constraint}
  lcs::Vector{Constraint}
  exprs::Dict 
  k_exprs::Dict
  adherence::Union{Nothing, Function}
  function PBPORule(l,r,tl,tk,l′; monic=true, acs=[], lcs=[], 
                    expr=nothing,k_expr=nothing, adherence=nothing)
    # check things match up
    S = acset_schema(dom(l))
    all(is_natural, [l,r,tl,tk,l′]) || error("Unnatural")
    dom(l) == dom(r) == dom(tk) || error("bad K")
    codom(l) == dom(tl) || error("bad L")
    codom(tk) == dom(l′) || error("bad K'")
    codom(l′) == codom(tl) || error("bad L'")
    check_pb(deattr.([tl,l′,l,tk])...) || error("(l,tk) not the pullback of (tl,l′)")
    all(o->is_monic(tl[o]), ob(S)) || error("tl map must be monic $tl")
    all(o->is_monic(tk[o]), ob(S)) || error("tk map must be monic $tk")
    # check adherence conditions?
    exprs = isnothing(expr) ? Dict() : Dict(pairs(expr))
    k_exprs = isnothing(k_expr) ? Dict() : Dict(pairs(k_expr))

    return new(l,r,tl,tk,l′, monic, acs, lcs, exprs, k_exprs, adherence)
  end
end

ruletype(::PBPORule) = :PBPO
left(r::PBPORule) = r.l 
right(r::PBPORule) = r.r

(F::Migrate)(r::PBPORule) =
  PBPORule(F(r.l), F(r.r), F(r.tl), F(r.tk), F(r.l′); monic=r.monic,
           acs=F.(r.acs), lcs=F.(r.lcs), expr=F(r.exprs), k_expr=F(r.k_exprs), 
           adherence=r.adherence)


"""
Take a PBPO rule and put into normal form, i.e. 
where the lower square forms a pullback

See Prop 2.4 of "The PBPO graph transformation approach"
"""
function canon(l,r,tl,tk,l′)::PBPORule
  new_l , new_tk = pb = pullback(tl, l′)
  ns = filter(n->force(n⋅new_tk)==force(tk), 
              homomorphisms(dom(l), apex(pb)))
  n = only(ns) # is there a better way to get this via pullback?
  new_r, _ = pushout(n, r)
  PBPORule(force.([new_l, new_r, tl, new_tk,l′])...)
end

"""
PBPO matches consist of *two* morphisms. First, a match L → G and secondly 
a typing G → L′. With attributes, it is not so simple because G has concrete 
values for attributes and L′ may have variables. Therefore, we actually the 
typing to map out of A, an abstracted version of G (with its attributes replaced 
by variables). So we lift matches L->G to matches L->A, then search α∈Hom(A,L′).

In general, we want α to be uniquely determined by m, so by default `α_unique`  
is set to true.

     m
  L⌟ ⟶ G 
 ||     ↓ α
  L  ⟶ L′
     tl

     ∀m
   L ⟶ G 
tl ↓ ↘a ↑ (abstraction)
   L′⟵ A 
      α

The "strong match" condition we enforce is that: tl⁻¹(α(A)) = a⁻¹(A). This means 
we can deduce precisely what m is by looking at α.

"""
function get_matches(rule::PBPORule, G::ACSet;  initial=nothing, 
                     α_unique=true, random=false, n=-1, kw...)
  S = acset_schema(G)
  res = [] # Pairs of (m,α)
  L = codom(left(rule))

  # Process the initial constraints for match morphism and typing morphism
  if isnothing(initial)
    matchinit, typinit = Dict(), Dict()
  elseif initial isa Union{NamedTuple,AbstractDict}
    matchinit, typinit = Dict(pairs(initial)), Dict()
  elseif length(initial)==2
    matchinit, typinit = [Dict(pairs(x)) for x in initial]
  else 
    error("Unexpected type for `initial` keyword: $initial")
  end 

  # Search for each match morphism
  backtracking_search(L, G; monic=rule.monic, initial=NamedTuple(matchinit),
                      random=random) do m
    m_seen = false # keeps track if α_unique is violated for each new m
    if all(ac->apply_constraint(ac, m), rule.acs)
      @info "m:  $([k=>collect(v) for (k,v) in pairs(components(m))])"
      # Construct abtract version of G. ab: A->G 
      ab = abstract_attributes(G)
      A = dom(ab) # not completely abstract: fill in where L has concrete attrs
      for (a, cd, _) in attrs(S)
        for (v, fv) in filter(v_->!(v_[2] isa AttrVar),collect(enumerate(L[a])))
          A[m[cd](v), a] = fv
        end
      end
      ab = remove_freevars(ab)
      A = dom(ab) # now with free variables removed
      # Construct a:L->A such that m = a;ab
      ainit = NamedTuple(Dict(o=>collect(m[o]) for o in ob(S)))
      a = only(homomorphisms(L, A; initial=ainit))
      # Search for maps α: A -> L′ such that a;α=tl 
      init = combine_dicts!(extend_morphism_constraints(rule.tl,a), typinit)
      if !isnothing(init) 
        # If we have a built in function to deduce the adherence from the match
        if !isnothing(rule.adherence)
          init = rule.adherence(m) # return nothing if failure
          if !isnothing(init)
            αs = homomorphisms(codom(a), codom(rule.tl); initial=init)
            if length(αs) ==1 
              push!(res, deepcopy((m,a,ab,only(αs)))) 
            end 
          end
        else 
          # Search for adherence morphisms.
          backtracking_search(codom(a), codom(rule.tl); initial=init, kw...) do α
            @info "\tα: ", [k=>collect(v) for (k,v) in pairs(components(α))] 
            strong_match = all(ob(S)) do o 
              all(parts(A,o)) do i 
                p1 = preimage(rule.tl[o],α[o](i))
                p2 = preimage(a[o], i)
                sort(p1) == sort(p2)
              end
            end
            if strong_match && all(lc -> apply_constraint(lc, α), rule.lcs)
              all(is_natural, [m,a,ab,α]) || error("Unnatural match")
              if m_seen  error("Multiple α for a single match $m") end 
              @info "\tSUCCESS"
              push!(res, deepcopy((m,a,ab,α)))
              m_seen |= α_unique
              return length(res) == n
            else
              @info "\tFAILURE (strong $strong_match)"
              return false
            end
          end
        end
      end
    end
    return length(res) == n
  end 
  return res
end

""" 
             r
          K ----> R
    gₗ    u ↓ gᵣ ⌜ ↓ w
Gₗ <---- Gk ----> Gᵣ
α ↓    ⌞ ↓ u'
 L′ <--  K′
     tₗ

For the adherence morphism α to be valid, it must satisfy a condition with 
m, tₗ. This is checked for matches provided by get_matches, so by default 
we do not check it.

  L <--⌞•
m ↓     ↓
  G ⟵ Gk
"""
function rewrite_match_maps(rule::PBPORule,mα; check=false, kw...)
  _, _, _, α = mα 
  S = acset_schema(dom(left(rule)))
  gl, u′ = var_pullback(Cospan(α, rule.l′)) # A <-- Gk --> K'
  abs_K = abstract_attributes(dom(left(rule))) # absK -> K 
  u = only(filter(u->force(compose(u,u′))==force(compose(abs_K,rule.tk)), 
                  homomorphisms(dom(abs_K), dom(u′))))
  abs_r = homomorphism(dom(abs_K), codom(right(rule)); 
                       initial=Dict([o=>collect(right(rule)[o]) for o in ob(S)]))
  w, gr = pushout(abs_r, u)

  return Dict(:gl=>gl, :u′=>u′, :u=>u, :gr=>gr, :w=>w)
end


"""
Use exprs and k_exprs to fill in variables introduced by applying the rw rule.
"""
function get_expr_binding_map(rule::PBPORule, mtch, res) 
  # unpack data
  X = codom(res[:w])
  (m, _, ab, _) = mtch

  comps = Dict(map(attrtypes(acset_schema(X))) do at 
    # match morphism data
    bound_vars = Vector{Any}(collect(m[at]))
    # For each variable in the intermediate rewrite state, determine what 
    # it refers to in the original graph and what in K′ it refers to, too.
    G_bound_vars = Vector{Any}(collect(compose(res[:gl][at],ab[at])))
    K_bound_vars = [k isa AttrVar ? k.val : k for k in collect(res[:u′][at])]
    # Functions we associate with K′ variables 
    exprs = haskey(rule.k_exprs,at) ? rule.k_exprs[at] : Dict()
    # Compute a value for each variable in the result
    at => map(parts(X, at)) do x 
      p_r = preimage(res[:w][at], AttrVar(x))
      # If the variable was introduced via R, try to use rule.exprs
      if !isempty(p_r) 
        v = only(p_r)
        if haskey(rule.exprs,at)
          rx = rule.exprs[at]
          rexpr = rx isa AbstractVector ? rx[v] : get(rx, v, nothing)
          if !isnothing(rexpr)
            return rexpr(bound_vars)
          end
        end
      end 
      # Try to get value via the intermediate graph
      p_k = only(preimage(res[:gr][at], AttrVar(x)))
      ik = K_bound_vars[p_k]
      k_expr = exprs isa AbstractVector ? exprs[ik] : get(exprs, ik, nothing)
      if isnothing(k_expr)
        return G_bound_vars[p_k] # default to corresponding attr in original G
      else 
        return k_expr(G_bound_vars[p_k], bound_vars) # apply custom function
      end
    end
  end)
  return sub_vars(X, comps)
end

end # module 