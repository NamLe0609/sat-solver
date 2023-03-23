import numpy


def load_dimacs(filename):
    lines = filter(None, (line.rstrip() for line in open(filename)))

    clauseSet = []
    # n is the number of the largest variable, and
    # m is the total number of clauses in the clause-set
    ignored = {"c", "p", "%", "0"}
    for line in lines or line:
        if line[0] in ignored:
            continue
        sections = line.strip('\n').strip(" ").split()
        clause = [int(literal) for literal in sections if literal != "0"]
        clauseSet.append(clause)

    return clauseSet


def getOccurrence(clause_set):
    occurrence = {}
    for clause in clause_set:
        for literal in clause:
            if literal in occurrence:
                occurrence[literal] += 1
            else:
                occurrence[literal] = 1
    return occurrence


def learnConflict(partial_assignment, conflictClause, decisionLevel, watchedLiteral, antecedent, assigned):
    if decisionLevel == 0:
        return -1
    
    learnedClause = set()
    varQueue = set()
    for literal in conflictClause:
        if abs(literal) in antecedent:
            varQueue.add(abs(literal))
        else:
            learnedClause.add(literal)
        
    largest = [0, decisionLevel]
    while varQueue:
        latestAssignedLit = assigned.pop()
        if len(varQueue) == 1 and abs(latestAssignedLit) in varQueue:
            largest[0] = -latestAssignedLit
            break
            
        latestAssignedVar = abs(latestAssignedLit)
        if latestAssignedVar in varQueue:
            varQueue.remove(latestAssignedVar)
            varAntecedent = antecedent[latestAssignedVar]
            
            for literal in varAntecedent:
                if abs(literal) == latestAssignedVar:
                    continue
                elif abs(literal) in antecedent:
                    varQueue.add(abs(literal))
                elif -literal in learnedClause:
                    learnedClause.remove(literal)
                else:
                    learnedClause.add(literal)
    
    if not learnedClause:
        watchedLiteral[0].add(largest[0])
        return 0
        
    secondLargest = [0, 0]
    for literal in learnedClause:
        literalDecisionLevel = partial_assignment[-literal]
        
        if literalDecisionLevel >= secondLargest[1]:
            secondLargest = [literal, literalDecisionLevel]

    watchedLearnedClause = [largest[0], secondLargest[0]]
    learnedClause.remove(secondLargest[0])
    watchedLearnedClause += list(learnedClause)

    for i in range(2):
        if watchedLearnedClause[i] in watchedLiteral:
            watchedLiteral[watchedLearnedClause[i]].append(watchedLearnedClause)
        else:
            watchedLiteral[watchedLearnedClause[i]] = [watchedLearnedClause]

    return secondLargest[1]


def watchElse(partial_assignment, watchedLiteral, negUnitLiteral):
    unitPropQueue = []
    if negUnitLiteral not in watchedLiteral:
        return unitPropQueue
    watchedClause = watchedLiteral[negUnitLiteral].copy()

    for clause in watchedClause:
        if clause[0] in partial_assignment or clause[1] in partial_assignment:
            continue

        changeIndex = 0
        if clause[1] == negUnitLiteral:
            changeIndex = 1

        for i in range(2, len(clause)):
            if -clause[i] not in partial_assignment or clause[i] in partial_assignment:
                watchedLiteral[negUnitLiteral].remove(clause)
                if clause[i] not in watchedLiteral:
                    watchedLiteral[clause[i]] = [clause]
                else:
                    watchedLiteral[clause[i]].append(clause)
                clause[i], clause[changeIndex] = clause[changeIndex], clause[i]
                break

        if clause[changeIndex] == negUnitLiteral:
            if -clause[1-changeIndex] in partial_assignment:
                return tuple(clause)
            else:
                unitPropQueue.append((clause[1-changeIndex], clause))
                
    return unitPropQueue


def unitPropagateWL(partial_assignment, watchedLiteral, literalAssignment):
    if literalAssignment == 0:
        unitPropQueue = []
        decisionLevel = 0
        for unit in watchedLiteral[0]:
            unitPropQueue.append((unit, []))
    else:
        unitPropQueue = [(literalAssignment, [])]
        decisionLevel = len(set(partial_assignment.values())) + 1
        
    antecedent = {}
    assigned = []
    while unitPropQueue:
        unitLiteral = unitPropQueue.pop(0)
        literalAssignment = unitLiteral[0]
        if literalAssignment in partial_assignment:
            continue
        
        if -literalAssignment in partial_assignment:
            print("hi")
        
        assigned.append(literalAssignment)
        antecedent[abs(literalAssignment)] = unitLiteral[1]
            
        partial_assignment[literalAssignment] = decisionLevel
        
        if -literalAssignment in watchedLiteral:
            updateWatched = watchElse(
                partial_assignment, watchedLiteral, -literalAssignment)

            if isinstance(updateWatched, tuple):
                return learnConflict(partial_assignment, updateWatched, decisionLevel, watchedLiteral, antecedent, assigned)

            if updateWatched:
                unitPropQueue = unitPropQueue + updateWatched

    return True


def dpll_sat_solve(clause_set, partial_assignment):
    return dpll_sat_solve_WL(clause_set, [], {}, [], 0, 0)

def dpll_sat_solve_WL(clause_set, partial_assignment, watchedLiteral={}, occurrence=[], cardinality=0, nextLiteral=0):
    # Initialize watched literals
    if watchedLiteral == {}:
        partial_assignment = {}
        literalOccurrence = getOccurrence(clause_set)
        occurrence = sorted(literalOccurrence,
                            key=literalOccurrence.get, reverse=True)
        cardinality = max(max(occurrence), -min(occurrence))
        watchedLiteral[0] = set()

        for clause in clause_set:
            if len(clause) == 1:
                watchedLiteral[0].add(clause[0])
                continue

            for i in range(2):
                if clause[i] in watchedLiteral:
                    watchedLiteral[clause[i]].append(clause)
                else:
                    watchedLiteral[clause[i]] = [clause]

    # Unit prop and check if unsat
    unitPropResult = unitPropagateWL(partial_assignment, watchedLiteral, nextLiteral)
    if not isinstance(unitPropResult, bool):
        return unitPropResult

    # Check if sat
    if len(partial_assignment) == cardinality:
        return list(partial_assignment)

    # Choose next literal
    for i in range(len(occurrence)):
        literal = occurrence[i]
        if literal not in partial_assignment and -literal not in partial_assignment:
            nextLiteral = literal
            break

    # For reset
    previousPartialAssignment = partial_assignment.copy()

    branch1 = dpll_sat_solve_WL(
        clause_set, partial_assignment, watchedLiteral, occurrence, cardinality, nextLiteral)
    
    while True:  
        if branch1 == -1:
            return False
        
        if isinstance(branch1, list):
            return list(branch1)
        
        if branch1 == 0:
            if len(previousPartialAssignment.values()) == 0 or max(set(previousPartialAssignment.values())) == 0:
                nextLiteral = 0
                previousPartialAssignment = {}
            else:
                return branch1
        else:
            if branch1 - 1 < len(set(previousPartialAssignment.values())):
                return branch1
        
        partial_assignment = previousPartialAssignment.copy()
        
        branch1 = dpll_sat_solve_WL(
            clause_set, partial_assignment, watchedLiteral, occurrence, cardinality, nextLiteral)


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