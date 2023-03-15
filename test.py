import numpy


def load_dimacs(filename):
    lines = filter(None, (line.rstrip() for line in open(filename)))

    clauseSet = []
    # n is the number of the largest variable, and
    # m is the total number of clauses in the clause-set
    ignored = {"c", "p", "%", "0", "", " "}
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
    if decisionLevel == 1:
        return False
    
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
        if len(varQueue) == 1:
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
        watchedLiteral[0].add(varQueue.pop())
        return 0
        
    secondLargest = [0, 0]
    for literal in learnedClause:
        literalDecisionLevel = partial_assignment[-literal]
        
        if literalDecisionLevel > secondLargest[1]:
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
        decisionLevel = max(set(partial_assignment.values())) + 1
        
    antecedent = {}
    assigned = []
    while unitPropQueue:
        unitLiteral = unitPropQueue.pop(0)
        literalAssignment = unitLiteral[0]
        if literalAssignment in partial_assignment:
            continue
        
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
    if type(unitPropResult) == int:
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
    
    while type(branch1) == int:
        if isinstance(branch1, list):
            return list(branch1)
        
        if branch1 == 0:
            if max(set(previousPartialAssignment.values())) == 0:
                nextLiteral = 0
            else:
                return branch1
        else:
            if branch1 - 1 < max(set(previousPartialAssignment.values())):
                return branch1
        
        partial_assignment = previousPartialAssignment.copy()
        
        branch1 = dpll_sat_solve_WL(
            clause_set, partial_assignment, watchedLiteral, occurrence, cardinality, nextLiteral)
        
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
#problem = load_dimacs("8queens.txt")
problem = load_dimacs("LNP-6.txt")
#problem = load_dimacs("gt.txt")
#problem = load_dimacs("uf20-099.txt")
#problem = load_dimacs("CBS_k3_n100_m403_b10_0.txt")
#problem = load_dimacs("n100.txt")
#problem = load_dimacs("uf20-0101.txt")

#print(problem)
#print(simple_sat_solve(problem))
#print(branching_sat_solve(problem, []))
print(dpll_sat_solve(problem,[]))
#print(sat_checker(problem, dpll_sat_solve(problem,[])))
#print(sat_checker(problem, [-28, -37, -29, -36, -19, -46, -20, -38, -21, -27, -30, -35, -43, -22, -44, -45, -10, -55, -11, -18, -26, -34, 42, -47, -50, 12, -39, -51, -13, -31, -52, -14, 23, 53, -15, -54, -1, -2, -3, -4, -5, 6, -7, -8, -9, -17, 25, -33, -41, -49, -57, -64, -56, -58, -48, 59, 40, -60, -32, -61, -24, -62, -16, -63]))

from itertools import chain
from os import listdir

# if you store them in folder `tests`, like:
# sat_solve_folder
# | sat_solver_.py
# | tests
# | | uf_20
# | | | > the uf20 files
# | | uf_50
# | | | > the uf50 files
# | | uuf_50
# | | | > the uuf50 files
""" uf_twenty = map(lambda x: ("uf20/" + x[:-4], True), listdir("tests/uf20"))
uf_fifty = map(lambda x: ("uf50/" + x[:-4], True), listdir("tests/uf50"))
uuf_fifty = map(lambda x: ("uuf50/" + x[:-4], False), listdir("tests/uuf50"))


def runall():
    for name, sat in chain(
        uf_twenty,
        uuf_fifty,
        uf_fifty,
    ):
        sat_instance = load_dimacs(f"tests/{name}.cnf")
        print(name, end="")
        sat_res = dpll_sat_solve(sat_instance, [])
        if sat:
            assert type(sat_res) == list
            # if you unit propagate after assigning it should be empty
            # assert len(unit_propagate(sat_instance, set(sat_res))) == 0
        else:
            assert sat_res == None
        print("\r", end="")
        
runall() """