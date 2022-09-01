module AlgebraicRewriting
using Reexport
using Requires

include("Variables.jl")
include("FinSets.jl")
include("Search.jl")
include("CSets.jl")
include("StructuredCospans.jl")
include("PartialMap.jl")
include("Rewrite.jl")
include("Schedules.jl")

@reexport using .Variables
@reexport using .FinSets
@reexport using .Search
@reexport using .CSets
@reexport using .StructuredCospans
@reexport using .PartialMap
@reexport using .Rewrite
@reexport using .Schedules

function __init__()
  @require Interact = "c601a237-2ae4-5e1e-952c-7a85b0c7eef1" begin
    include("Visuals.jl")
    @reexport using .Visuals
  end
end

end # module
