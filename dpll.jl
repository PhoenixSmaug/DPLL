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
    assign!(var, value, isForced, forceQueue, variables, clauses, assignmentStack)

Assign value to variable and check for conflict

# Arguments
- `var`: Variable to assign
- `value`: Value to be assigned, either :One or :Zero
- `isForced`: If variable is forced by unit or pure literal elimination
- `forceQueue`: Vector as FIFO queue of forced literals (by unit propagation or pure literal elimination)
- `variables`: Vector of variables
- `clauses`: Vector of clauses
- `assignmentStack`: Stack of currently assigned variables
"""
function assign!(var::Var, value::Symbol, isForced::Bool, forceQueue::Vector{Lit}, variables::Vector{Var}, clauses::Vector{Clause}, assignmentStack::Vector{Var})
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
                elseif clauses[cIdx].act == 1  # unit clause
                    # find last active literal and add to foreced queue
                    for lit in clauses[cIdx].lits
                        if variables[lit.varIdx].value == :Free
                            push!(forceQueue, lit)
                        end
                    end
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
                elseif clauses[cIdx].act == 1  # unit clause
                    # find last active literal and add to foreced queue
                    for lit in clauses[cIdx].lits
                        if variables[lit.varIdx].value == :Free
                            push!(forceQueue, lit)
                        end
                    end
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
    backtrack!(variables, clauses, forceQueue, assignmentStack)

Reverse assignments on the assignment stack until an unforced variable is found, where the inverse assignment
does not result in a conflict.

# Arguments
- `variables`: Vector of variables
- `clauses`: Vector of clauses
- `forceQueue`: Vector as FIFO queue of forced literals (by unit propagation or pure literal elimination) 
- `assignmentStack`: Stack of currently assigned variables
"""
function backtrack!(variables::Vector{Var}, clauses::Vector{Clause}, forceQueue::Vector{Lit}, assignmentStack::Vector{Var})
    while !isempty(assignmentStack)
        # reverse last assignment
        var = pop!(assignmentStack)
        valueToUnassign = var.value
        unassign!(var, clauses)

        # variable was choosen and not forced
        if !var.isForced
            empty!(forceQueue)  # clear unit queue

            newValue = valueToUnassign == :Zero ? :One : :Zero

            if assign!(var, newValue, true, forceQueue, variables, clauses, assignmentStack)
                if forced_prop!(variables, clauses, forceQueue, assignmentStack)
                    return true
                end

                continue  # Forced propagation of assignments also leads to conflict, backtrack further
            else
                continue  # Inverse assignments also leads to conflict, backtrack further
            end
        end
    end

    return false  # Assignment stack is empty, problem is unsatisfiable
end


"""
    forced_prop!(variables, clauses, forceQueue, assignmentStack)

Assing forced variables from queue and stop at possible conflicts

# Arguments
- `variables`: Vector of variables
- `clauses`: Vector of clauses
- `forceQueue`: Vector as FIFO queue of forced literals (by unit propagation or pure literal elimination) 
- `assignmentStack`: Stack of currently assigned variables
"""
function forced_prop!(variables::Vector{Var}, clauses::Vector{Clause}, forceQueue::Vector{Lit}, assignmentStack::Vector{Var})
    noConflict = true

    while !isempty(forceQueue)
        forceLit = pop!(forceQueue)
        forceVar = variables[forceLit.varIdx]

        # Check if the variable was already propagated
        if forceVar.value != :Free
            continue
        end

        # Determine the value to assign based on the literal's sign
        value = forceLit.isPos ? :One : :Zero

        noConflict = assign!(forceVar, value, true, forceQueue, variables, clauses, assignmentStack)

        if !noConflict
            break
        end
    end

    return noConflict
end


"""
    selectVar(variables, clauses)

Select next value to be assigned and value to assign. Use DLIS heuristic, so choose free literal
occurring most often in unsatisfied clauses.

# Arguments
- `variables`: Vector of variables
- `clauses`: Vector of clauses
"""
function selectVar(variables::Vector{Var}, clauses::Vector{Clause})
    maxOccurrence = -1
    selectedVar = nothing
    selectedValue = :One  # Default value, in case all variables are assigned

    posLiteralCounts = Dict{Int, Int}()
    negLiteralCounts = Dict{Int, Int}()

    for clause in clauses
        for lit in clause.lits
            # Only consider literals from clauses that are not yet satisfied
            if isnothing(clause.isSat)
                varIdx = lit.varIdx
                var = variables[varIdx]
                if var.value == :Free
                    if lit.isPos
                        posLiteralCounts[varIdx] = get(posLiteralCounts, varIdx, 0) + 1  # start at 0 if entry at varIdx does not exist yet
                        
                        if posLiteralCounts[varIdx] > maxOccurrence
                            maxOccurrence = posLiteralCounts[varIdx]
                            selectedVar = var
                            selectedValue = :One
                        end
                    else
                        negLiteralCounts[varIdx] = get(negLiteralCounts, varIdx, 0) + 1

                        if negLiteralCounts[varIdx] > maxOccurrence
                            maxOccurrence = negLiteralCounts[varIdx]
                            selectedVar = var
                            selectedValue = :Zero
                        end
                    end
                end
            end
        end
    end

    return selectedVar, selectedValue
end


"""
    dpll!(variables, clauses, forceQueue, timeout)

DPLL algorithm to solve the CNF formula encoded in variables and clauses

# Arguments
- `variables`: Vector of variables
- `clauses`: Vector of clauses
- `forceQueue`: Vector as FIFO queue of forced literals (by unit propagation or pure literal elimination) 
- `timeout`: Timeout in seconds
"""
function dpll!(variables::Vector{Var}, clauses::Vector{Clause}, forceQueue::Vector{Lit}, timeout::Int)
    assignmentStack = Var[]
    startTime = time()

    #debugPrint(variables, clauses)  # TEMP
    #println(forceQueue)

    # initial forced propagation
    if !forced_prop!(variables, clauses, forceQueue, assignmentStack)
        return false, time() - startTime  # unsatisfiable
    end

    while true
        #debugPrint(variables, clauses) # TEMP
        #println(forceQueue)

        # Check for timeout
        if time() - startTime > timeout
            return false, nothing  # timed out
        end
        
        var, value = selectVar(variables, clauses)

        # All variables are assigned without conflict, so satisfying assignment is found
        if isnothing(var) 
            return true, time() - startTime  # satisfied
        end

        if !assign!(var, value, false, forceQueue, variables, clauses, assignmentStack)
            # conflict in assignment
            if !backtrack!(variables, clauses, forceQueue, assignmentStack)
                return false, time() - startTime  # unsatisfiable
            end
            continue
        end

        if !forced_prop!(variables, clauses, forceQueue, assignmentStack)
            # conflict in forced propagation
            if !backtrack!(variables, clauses, forceQueue, assignmentStack)
                return false, time() - startTime  # unsatisfiable
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
    forceQueue = Lit[]

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

                    if length(literals) == 2  # unit clause
                        push!(forceQueue, Lit(varIndex, isPos))
                    end
                end
                push!(clauses, Clause(clauseLits, nothing, length(clauseLits)))
            end
        end
    end

    return variables, clauses, forceQueue
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

    satisfiedClauses = [clause.act for (idx, clause) in enumerate(clauses) if !isnothing(clause.isSat)]
    #satisfiedClauses = [(idx, clause.act) for (idx, clause) in enumerate(clauses) if !isnothing(clause.isSat)]
    println("Satisfied Clauses: ", satisfiedClauses)
end


"""
    main(filepath)

Read CNF file, solve it using DPLL and write solution to result file

# Arguments
- `cnfPath`: Relative or absolute path of CNF file
- `resPath`: Relative or absolute path of result file
- `timeout`: Timeout in seconds
"""
function main(cnfPath::String, resPath::String, timeout::Int)
    variables, clauses, forceQueue = importCNF(cnfPath)
    
    satisfiable, time = dpll!(variables, clauses, forceQueue, timeout)

    if !isnothing(time)
        exportResult(variables, resPath, satisfiable)

        timeStr = string(round(time, digits=2))
        if satisfiable
            println("Satisfiable: " * timeStr  * "s")
        else
            println("Unsatisfiable: " * timeStr  * "s")
        end
    else
        println("Timed out.")
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
            main(file, fileRes, 3)
        end
    end

    for file in readdir("input/test/unsat", join=true)
        if endswith(file, ".cnf")
            println("Processing file: $file")
            fileRes = replace(file, r"\.cnf$" => ".txt")
            main(file, fileRes, 3)
        end
    end
end

runTestInstances()
#main("input/test/unsat/tent2_2.cnf", "test.txt", 10)

# (c) Mia Muessig