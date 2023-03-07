import numpy

def load_dimacs(filename):
    with open(filename) as f:
        lines = f.readlines()
        f.close()

    clauseSet = []
    # n is the number of the largest variable, and
    # m is the total number of clauses in the clause-set
    for line in lines:
        if line[0] == "c" or line[0] == "p":
            continue
        sections = line.strip('\n').split(" ")
        clause = [int(literal) for literal in sections if literal != "0"]
        clauseSet.append(clause)
        
    return clauseSet

def getOccurrence(clause_set):
    occurrence = {}
    for clause in clause_set:
        for literal in clause:
            absoluteLiteral = abs(literal)
            if literal in occurrence:
                occurrence[absoluteLiteral] += 1
            else:
                occurrence[absoluteLiteral] = 1
    return occurrence

def watchElse(partial_assignment, watchedLiteral, negUnitLiteral):
    unitPropQueue = []
    watchedClause = watchedLiteral[negUnitLiteral].copy()
    
    for clause in watchedClause:
        canWatchElse = False
        canWatchWatched = False
        
        for literal in clause:
            if literal in partial_assignment:
                canWatchElse = True
                break
            
            elif -literal in partial_assignment or literal == negUnitLiteral:
                continue
            
            elif literal in watchedLiteral and clause in watchedLiteral[literal]:
                canWatchWatched = literal
                
            else:
                canWatchElse = True
                watchedLiteral[negUnitLiteral].remove(clause)
                if literal not in watchedLiteral:
                    watchedLiteral[literal] = [clause]
                else:
                    watchedLiteral[literal].append(clause)
                break
        
        if canWatchWatched and not canWatchElse:
            unitPropQueue.append(canWatchWatched)
            
        elif not canWatchElse and not canWatchWatched:
            return False
            
    if unitPropQueue:
        return unitPropQueue
    else:
        return True

def unitPropagateWL(partial_assignment, watchedLiteral, literalAssignment):
    if literalAssignment != 0:
        unitPropQueue = [literalAssignment]
        
        while unitPropQueue:
            literalAssignment = unitPropQueue.pop(0)
            partial_assignment.add(literalAssignment)
            
            if -literalAssignment in partial_assignment:
                return False
            
            if -literalAssignment in watchedLiteral:
                updateWatched = watchElse(partial_assignment, watchedLiteral, -literalAssignment)
                
                if not updateWatched:
                    return False
                
                if isinstance(updateWatched, list):
                    unitPropQueue = unitPropQueue + updateWatched
        
        return True

def dpll_sat_solve_WL(clause_set, partial_assignment=set(), watchedLiteral={}, occurrence=[], cardinality=0, nextLiteral=0):
    # Initialize watched literals
    if watchedLiteral == {}:
        literalOccurrence = getOccurrence(clause_set)
        occurrence = [sorted(literalOccurrence, key=literalOccurrence.get, reverse=True), 0]
        cardinality = max(max(occurrence[0]),-min(occurrence[0]))
        unitPropQueue = []
        
        for clause in clause_set:
            if len(clause) == 1:
                unitPropQueue.append(clause[0])
                continue
            
            for i in range(2):
                if clause[i] in watchedLiteral:
                    watchedLiteral[clause[i]].append(clause)
                else:
                    watchedLiteral[clause[i]] = [clause]
        
        while unitPropQueue:
            literalAssignment = unitPropQueue.pop()
            
            if literalAssignment in partial_assignment:
                continue
            
            if -literalAssignment in partial_assignment:
                return False
            
            if unitPropagateWL(partial_assignment, watchedLiteral, literalAssignment) == False:
                return False
            
    
    # Unit prop and check if unsat
    if unitPropagateWL(partial_assignment, watchedLiteral, nextLiteral) == False:
        return False
    
    # Check if sat
    if len(partial_assignment) == cardinality:
        return partial_assignment
    
    # Choose next literal
    prevOccurrenceCount = occurrence[1]
    for i in range(occurrence[1], len(occurrence[0])):
        literal = occurrence[0][i]
        if literal not in partial_assignment and -literal not in partial_assignment:
            nextLiteral = literal
            occurrence[1] += 1
            break
    
    # For reset
    previousPartialAssignment = partial_assignment.copy()
    
    branch1 = dpll_sat_solve_WL(clause_set, partial_assignment, watchedLiteral, occurrence, cardinality, nextLiteral)
    if branch1:
        return branch1
    
    # Reset
    partial_assignment = previousPartialAssignment
    occurrence[1] = prevOccurrenceCount
    
    branch2 = dpll_sat_solve_WL(clause_set, partial_assignment, watchedLiteral, occurrence, cardinality, -nextLiteral)
    if branch2:
        return branch2
    
    return False

def sat_checker(clause_set, truthAssignment):
    if type(truthAssignment) == bool:
        return "Does not solve"
    resolvedClauseSet = set()

    for clause in clause_set:
        resolvedClause = 0

        for literal in clause:
            if literal in truthAssignment:
                resolvedClause = 1
                break

        resolvedClauseSet.add(resolvedClause)

    if 0 not in resolvedClauseSet:
        return "Solves"

    return "Does not solve"

#problem = load_dimacs("sat.txt")
#problem = load_dimacs("unsat.txt")
#problem = load_dimacs("W_2,3_n=8.txt")
#problem = load_dimacs("PHP-5-4.txt")
problem = load_dimacs("8queens.txt")
#problem = load_dimacs("LNP-6.txt")
#problem = load_dimacs("gt.txt")

#print(simple_sat_solve(problem))
#print(branching_sat_solve(problem, []))
#print(unit_propagate(problem))
#print(dpll_sat_solve_WL(problem))
#print(sat_checker(problem, dpll_sat_solve_WL(problem)))
print(sat_checker(problem, [-28, -37, -29, -36, -19, -46, -20, -38, -21, -27, -30, -35, -43, -22, -44, -45, -10, -55, -11, -18, -26, -34, 42, -47, -50, 12, -39, -51, -13, -31, -52, -14, 23, 53, -15, -54, -1, -2, -3, -4, -5, 6, -7, -8, -9, -17, 25, -33, -41, -49, -57, -64, -56, -58, -48, 59, 40, -60, -32, -61, -24, -62, -16, -63]))