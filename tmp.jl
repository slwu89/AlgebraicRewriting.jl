# rm AlgPetri dep when done
using AlgebraicRewriting
using Catlab, AlgebraicPetri
using SpecialFunctions, Fleck
using Random
using Distributions

# matches(h::IncSumHomSet) = map(Iterators.product(matches.(h.ihs)...)) do comps
#     h.iso ⋅ universal(h.coprod, Multicospan(collect(comps)))
#   end


# get_matches(h::IncSumHomSet, matches)

# --------------------------------------------------------------------------------
# we want a PN with a marking
@present SchMarkedLabelledPetriNet <: SchLabelledPetriNet begin
    M::Ob
    m::Hom(M,S)
end

@acset_type MarkedLabelledPetriNet(SchMarkedLabelledPetriNet, index=[:it, :is, :ot, :os]) <: AbstractLabelledPetriNet

to_graphviz(SchMarkedLabelledPetriNet)

# a little function to see how many tokens are in each place
function marking(pn)
    names = Tuple(pn[:,:sname])
    vals = length.(incident(pn, parts(pn,:S), :m))
    return NamedTuple{names}(vals)
end

# --------------------------------------------------------------------------------
# an SIR model with demography (birth and death)
sirpn = @acset MarkedLabelledPetriNet{Symbol} begin
    S=3
    sname=[:S,:I,:R]
    T=6
    tname=[:inf,:rec,:birth,:deathS,:deathI,:deathR]
    I=6
    it=[1,1,2,4,5,6]
    is=[1,2,2,1,2,3]
    O=4
    ot=[1,1,2,3]
    os=[2,2,3,1]
end

to_graphviz(sirpn)

# add a marking
add_parts!(sirpn, :M, 1000, m=[fill(1,980); fill(2,20)])

# check the marking
marking(sirpn)

# --------------------------------------------------------------------------------
# make the set of rewrite rules

# function to make a DPO rule for a transition in a marked PN
function make_rule(pn::T, t) where {T<:MarkedLabelledPetriNet}
    input_m = inputs(pn, t)
    output_m = outputs(pn, t)

    # get L
    L = MarkedLabelledPetriNet{Symbol}()
    copy_parts!(L, pn, S=:)

    if length(input_m) > 0
        # add tokens
        add_parts!(
            L, :M, length(input_m),
            m = vcat(incident(L, pn[input_m, :sname], :sname)...)
        )
    end

    # get R
    R = MarkedLabelledPetriNet{Symbol}()
    copy_parts!(R, pn, S=:)

    if length(output_m) > 0
        # add tokens
        add_parts!(
            R, :M, length(output_m),
            m = vcat(incident(R, pn[output_m, :sname], :sname)...)
        )
    end

    _, span = only(maximum_common_subobject([L,R], abstract=false))

    return Rule(legs(first(span))[1], legs(first(span))[2])
end

# # -----------------
# # test manual updates

# # rewrite rules for our model
# sirpn_rules = Dict([
#     sirpn[t,:tname] => make_rule(sirpn, t)
#     for t in parts(sirpn, :T)
# ])

# # ---------------
# # "manual" update

# # sirpn = deepcopy(sirpn0)
# sirpn0 = deepcopy(sirpn)

# marking(sirpn)

# hset_inf = IncHomSet(codom(sirpn_rules[:inf].L), [sirpn_rules[t].R for t in sirpn[:,:tname]], sirpn, single=true)

# # my homs and clock (IDs) at time 0
# matches0 = Incremental.matches(hset_inf)
# clocks0 = collect(keys(hset_inf))

# @assert length(matches0) == marking(sirpn).S * marking(sirpn).I

# # make an infection happen
# event_maps = rewrite_match_maps(sirpn_rules[:inf], matches0[3])

# # the new state
# sirpn = codom(event_maps[:kh])
# marking(sirpn)

# # update the homset
# matches_del = Incremental.deletion!(hset_inf, event_maps[:kg])
# matches_add = Incremental.addition!(hset_inf, 1, event_maps[:rh], event_maps[:kh])

# # get all the matches after the event rewrites state
# matches1 = Incremental.matches(hset_inf)
# clocks1 = collect(keys(hset_inf))




# --------------------------------------------------------------------------------
# we want something to store the rules, clocks associated to each, and their type

@present SchClockSystem(FreeSchema) begin
    (Clock,Event)::Ob # clock is a single ID, event is an entire class of clocks (e.g. "typed" clocks)
    NameType::AttrType # each event has a name
    RuleType::AttrType # each event has a rewrite rule
    DistType::AttrType # each event has a function that returns a firing time when it's enabled
    MatchType::AttrType # each event has set of matches associated with it (in theory, this would instead be bijective with Clock)
    KeyType::AttrType
    event::Hom(Clock,Event)
    key::Attr(Clock,KeyType)
    name::Attr(Event,NameType)
    rule::Attr(Event,RuleType)
    dist::Attr(Event,DistType)
    match::Attr(Event,MatchType)
end

to_graphviz(SchClockSystem)

@acset_type ClockSystem(SchClockSystem, index=[:event,:type], unique_index=[:name])

sirclock = @acset ClockSystem{Symbol,Rule,Function,Incremental.IncCCHomSet,Tuple{Int,Int,Int}} begin
    Event=nt(sirpn)
    name=sirpn[:,:tname]
end

for t in parts(sirclock,:Event)
    sirclock[t,:rule] = make_rule(sirpn, t)
end

# --------------------------------------------------------------------------------
# add the distribution functions

pop = nparts(sirpn, :M)
lifespan = 65*365
μ = 1/lifespan

β = 0.05*5

# should somehow check that if this fn returns Exponential, its mapped to type Markov
sirclock[only(incident(sirclock, :inf, :name)), :dist] = (t) -> Exponential(1 / β)
sirclock[only(incident(sirclock, :birth, :name)), :dist] = (t) -> Exponential(1 / (μ*pop))
sirclock[only(incident(sirclock, :deathS, :name)), :dist] = (t) -> Exponential(1 / μ)
sirclock[only(incident(sirclock, :deathI, :name)), :dist] = (t) -> Exponential(1 / μ)
sirclock[only(incident(sirclock, :deathR, :name)), :dist] = (t) -> Exponential(1 / μ)

# get parameters of a Weibull (from https://github.com/cran/mixdist/blob/master/R/weibullpar.R)
function weibullpar(mu, sigma)
    cv = sigma / mu
    if cv < 1e-06
        nu = cv / (sqrt(trigamma(1)) - cv * digamma(1))
        shape = 1 / nu
        scale = mu / (1 + nu * digamma(1))
    else
        aa = log(cv^2 + 1)
        nu = 2 * cv / (1 + cv)
        while true
            gb = (lgamma(1 + 2 * nu) - 2 * lgamma(1 + nu) - aa) / (2 * (digamma(1 + 2 * nu) - digamma(1 + nu)))
            nu -= gb
            if abs(gb) < 1e-12
                break
            end
        end
        shape = 1 / nu
        scale = exp(log(mu) - lgamma(1 + nu))
    end
    return shape, scale
end

α, θ = weibullpar(7, 2.6)

# the non Markovian clock
sirclock[only(incident(sirclock, :rec, :name)), :dist] = (t) -> Weibull(α,θ)


# --------------------------------------------------------------------------------
# add the incremental homset structs

for t in parts(sirclock,:Event)
    sirclock[t,:match] = IncHomSet(codom(sirclock[t,:rule].L), getfield.(sirclock[:,:rule], :R), sirpn, single=true)
end

# --------------------------------------------------------------------------------
# add the clocks and sampler

# Fleck sampler
sampler = FirstToFire{Tuple{Int,Int,Int}, Float64}()
rng = Random.RandomDevice()
tnow::Float64 = 0.0
tmax::Float64 = 500

for t in parts(sirclock,:Event)
    newkeys = collect(keys(sirclock[t,:match]))
    newkeys = map(newkeys) do k
        (t,k...)
    end
    add_parts!(
        sirclock, :Clock, length(newkeys),
        key = newkeys, event = fill(t, length(newkeys))
    )
    for c in newkeys
        enable!(sampler, c, sirclock[t, :dist](tnow), tnow, tnow, rng)
    end
end

# record initial state
output = Vector{typeof((t=0.0,marking(sirpn)...))}()
push!(output, (t=0.0,marking(sirpn)...))

# when and what will happen next?
(tnow, which) = next(sampler, tnow, rng)

while tnow < tmax
    println("event fired at $tnow")
    event = first(which)
    update_maps = rewrite_match_maps(
        sirclock[event, :rule], 
        sirclock[event, :match][Pair(which[2:end]...)]
    )
    sirpn = codom(update_maps[:rh])
    push!(output, (t=tnow,marking(sirpn)...))

    # update matches for all events
    for t in parts(sirclock, :Event)
        del = Incremental.deletion!(sirclock[t,:match], update_maps[:kg])
        add = Incremental.addition!(sirclock[t,:match], event, update_maps[:rh], update_maps[:kh])
        del = map(del) do k
            (t,k...)
        end
        add = map(add) do k
            (t,k...)
        end
        # disable clocks
        for c in del
            disable!(sampler, c, tnow)
        end        
        # enable clocks
        for c in add
            enable!(sampler, c, sirclock[t, :dist](tnow), tnow, tnow, rng)
        end
    end
    (tnow, which) = next(sampler, tnow, rng)
end


