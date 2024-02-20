"""
    Lit(varIdx, isPos)

Literal struct

# Arguments
- `varIdx`: Variable of literal
- `isPos`: If occurring as positive literal
"""
mutable struct Lit
    varIdx::Int 
    isPos::Bool
end


"""
    Var(value, posOcc, negOcc)

Variable struct

# Arguments
- `value`: Enum to store if variable is not (:Free), negatively (:Zero) or positively (:One) assigned
- `posOcc`: Vector of clauses where the variable occurs as positive literal
- `negOcc`: Vector of clauses where the variable occurs as negative literal
- `isForced`: If variable is forced by unit or pure literal elimination
"""
mutable struct Var
    value::Symbol
    posOcc::Set{Int}
    negOcc::Set{Int}
    isForced::Bool
end


"""
    Clause(lits, isSat, act)

Clause struct

# Arguments
- `lits`: Vector of literals in the clause
- `isSat`: If clause is satisfied the variable satisfying it, otherwise Nothing
- `act`: The number of active, so unassigned literals in the clause
"""
mutable struct Clause
    lits::Vector{Lit}
    isSat::Union{Var, Nothing}
    act::Int
end


"""
    assign!(var, value, isForced, clauses, assignmentStack)

Assign value to variable and check for conflict

# Arguments
- `var`: Variable to assign
- `value`: Value to be assigned, either :One or :Zero
- `isForced`: If variable is forced by unit or pure literal elimination
- `clauses`: Vector of clauses
- `assignmentStack`: Stack of currently assigned variables
"""
function assign!(var::Var, value::Symbol, isForced::Bool, clauses::Vector{Clause}, assignmentStack::Vector{Var})
    var.isForced = isForced
    var.value = value
    push!(assignmentStack, var)
    
    noConflict = true

    if value == :One
        # update number of active literals in unsatisfied clauses
        for cIdx in var.negOcc
            if isnothing(clauses[cIdx].isSat)
                clauses[cIdx].act -= 1
                if clauses[cIdx].act == 0
                    noConflict = false
                end
            end
        end

        # satisfy clauses
        for cIdx in var.posOcc
            if isnothing(clauses[cIdx].isSat)
                clauses[cIdx].isSat = var
            end
        end
    elseif value == :Zero
        # update number of active literals in unsatisfied clauses
        for cIdx in var.posOcc
            if isnothing(clauses[cIdx].isSat)
                clauses[cIdx].act -= 1
                if clauses[cIdx].act == 0
                    noConflict = false
                end
            end
        end

        # satisfy clauses
        for cIdx in var.negOcc
            if isnothing(clauses[cIdx].isSat)
                clauses[cIdx].isSat = var
            end
        end
    end

    return noConflict
end


"""
    unassign!(var, clauses)

Unassign variable (set to :Free)

# Arguments
- `var`: Variable to unassign
- `clauses`: Vector of clauses
"""
function unassign!(var::Var, clauses::Vector{Clause})
    if var.value == :One
        # unsatisfy clauses
        for cIdx in var.posOcc
            if clauses[cIdx].isSat == var
                clauses[cIdx].isSat = nothing
            end
        end

        # update number of active literals in unsatisfied clauses
        for cIdx in var.negOcc
            if isnothing(clauses[cIdx].isSat)
                clauses[cIdx].act += 1
            end
        end
    elseif var.value == :Zero
        # unsatisfy clauses
        for cIdx in var.negOcc
            if clauses[cIdx].isSat == var
                clauses[cIdx].isSat = nothing
            end
        end

        # update number of active literals in unsatisfied clauses
        for cIdx in var.posOcc
            if isnothing(clauses[cIdx].isSat)
                clauses[cIdx].act += 1
            end
        end
    end
    var.value = :Free
end


"""
    backtrack!(clauses, assignmentStack)

Reverse assignments on the assignment stack until an unforced variable is found, where the inverse assignment
does not result in a conflict.

# Arguments
- `clauses`: Vector of clauses
- `assignmentStack`: Stack of currently assigned variables
"""
function backtrack!(clauses::Vector{Clause}, assignmentStack::Vector{Var})
    while !isempty(assignmentStack)
        # reverse last assignment
        var = pop!(assignmentStack)
        valueToUnassign = var.value
        unassign!(var, clauses)

        # variable was choosen and not forced
        if !var.isForced
            newValue = valueToUnassign == :Zero ? :One : :Zero

            if assign!(var, newValue, true, clauses, assignmentStack)
                return true
            else
                continue  # Inverse assignments also needs to conflict, backtrack further
            end
        end
    end

    return false  # Assignment stack is empty, problem is unsatisfiable
end


"""
    selectVar(variables)

Heuristic to select next variable to be assigned and which value to assign

# Arguments
- `variables`: Vector of variables
"""
function selectVar(variables::Vector{Var})
    for var in variables
        if var.value == :Free
            return var, :One
        end
    end
    return nothing, :One
end


"""
    dpll!(variables, clauses)

DPLL algorithm to solve the CNF formula encoded in variables and clauses

# Arguments
- `variables`: Vector of variables
- `clauses`: Vector of clauses
"""
function dpll!(variables::Vector{Var}, clauses::Vector{Clause})
    assignmentStack = Var[]

    while true
        #debugPrint(variables, clauses) # TEMP
        var, value = selectVar(variables)

        # all variables are assigned without conflict, so satisfying assignment is found
        if isnothing(var) 
            #debugPrint(variables) # TEMP
            return true
        end

        if !assign!(var, value, false, clauses, assignmentStack)
            if !backtrack!(clauses, assignmentStack)
                return false
            end
            continue
        end
    end
end


"""
    importCNF(filepath)

Read file DIMACS CNF format

# Arguments
- `filepath`: Relative or absolute path of CNF file
"""
function importCNF(filepath::String)
    variables = Var[]
    clauses = Clause[]

    open(filepath, "r") do file
        for line in eachline(file)
            if startswith(line, "c") || isempty(line)  # comments
                continue
            elseif startswith(line, "p")  # problem line
                _, _, num_vars, _ = split(line)
                for _ in 1 : parse(Int, num_vars)
                    push!(variables, Var(:Free, Set{Int}(), Set{Int}(), false))
                end
            else  # clause line
                literals = split(line)
                clauseLits = Lit[]
                for lit in literals
                    litNum = parse(Int, lit)
                    if litNum == 0
                        break
                    end
                    varIndex = abs(litNum)
                    isPos = litNum > 0
                    push!(clauseLits, Lit(varIndex, isPos))
                    if isPos
                        push!(variables[varIndex].posOcc, length(clauses) + 1)
                    else
                        push!(variables[varIndex].negOcc, length(clauses) + 1)
                    end
                end
                push!(clauses, Clause(clauseLits, nothing, length(clauseLits)))
            end
        end
    end

    return variables, clauses
end


"""
    exportResult(variables, filepath, satisfiable)

Write solution in DIMACS result format

# Arguments
- `variables`: Vector of variables
- `filepath`: Relative or absolute path of result file
- `satisfiable`: Result of DPLL algorithm
"""
function exportResult(variables::Vector{Var}, filepath::String, satisfiable::Bool)
    open(filepath, "w") do file
        if satisfiable
            write(file, "SAT\n")
            for (idx, var) in enumerate(variables)
                if var.value == :One
                    write(file, "$idx ")
                elseif var.value == :Zero
                    write(file, "-$idx ")
                end
            end
            write(file, "0\n")
        else
            write(file, "UNSAT\n")
        end
    end
end


function debugPrint(variables::Vector{Var})
    assignedVars = Int[]
    for (idx, var) in enumerate(variables)
        if var.value == :One
            push!(assignedVars, idx)
        elseif var.value == :Zero
            push!(assignedVars, -idx)
        end
    end
    println("Assigned Variables: ", assignedVars)
end

function debugPrint(variables::Vector{Var}, clauses::Vector{Clause})
    assignedVars = Int[]
    for (idx, var) in enumerate(variables)
        if var.value == :One
            push!(assignedVars, idx)
        elseif var.value == :Zero
            push!(assignedVars, -idx)
        end
    end
    println("Assigned Variables: ", assignedVars)

    satisfiedClauses = [(idx, clause.act) for (idx, clause) in enumerate(clauses) if !isnothing(clause.isSat)]
    println("Satisfied Clauses: ", satisfiedClauses)
end


"""
    main(filepath)

Read CNF file, solve it using DPLL and write solution to result file

# Arguments
- `cnfPath`: Relative or absolute path of CNF file
- `resPath`: Relative or absolute path of result file
"""
function main(cnfPath::String, resPath::String)
    variables, clauses = importCNF(cnfPath)
    
    satisfiable = dpll!(variables, clauses)

    exportResult(variables, resPath, satisfiable)

    if satisfiable
        println("Satisfiable")
    else
        println("Unsatisfiable")
    end
end


"""
    runTestInstances()

Run test instances and print results
"""
function runTestInstances()
    for file in readdir("input/test/sat", join=true)
        if endswith(file, ".cnf")
            println("Processing file: $file")
            fileRes = replace(file, r"\.cnf$" => ".txt")
            main(file, fileRes)
        end
    end

    for file in readdir("input/test/unsat", join=true)
        if endswith(file, ".cnf")
            println("Processing file: $file")
            fileRes = replace(file, r"\.cnf$" => ".txt")
            main(file, fileRes)
        end
    end
end

runTestInstances()

# (c) Mia Muessig