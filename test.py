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


def learnConflict(partial_assignment, conflictClause, decisionLevel, watchedLiteral):
    learnedClause = set(trail.pop())

    while (trail):
        supportClauses = trail.pop()
        if len(supportClauses) == 1:
            trail = []
        for clause in supportClauses:
            for literal in clause:
                if -literal in learnedClause:
                    learnedClause.remove(-literal)
                else:
                    learnedClause.add(literal)

    secondLargest = [0, 0]
    largest = [0, 0]
    if len(learnedClause) == 1:
        secondLargest = [learnedClause[0], 0]
        watchedLiteral[0].append(learnedClause[0])
        return secondLargest
    else:
        for literal in learnedClause:
            if literal in partial_assignment or -literal in partial_assignment:
                literalDecisionLevel = partial_assignment[-literal]
                if literalDecisionLevel < decisionLevel:
                    if literalDecisionLevel > secondLargest[1]:
                        secondLargest = (literal, literalDecisionLevel)
                else:
                    largest = [literal, decisionLevel]

    watchedLearnedClause = [largest[0], secondLargest[0]]
    learnedClause.remove(largest[0])
    learnedClause.remove(secondLargest[0])
    watchedLearnedClause += list(learnedClause)

    for i in range(2):
        if watchedLearnedClause[i] in watchedLiteral:
            watchedLiteral[watchedLearnedClause[i]].append(watchedLearnedClause)
        else:
            watchedLiteral[watchedLearnedClause[i]] = [watchedLearnedClause]

    return largest


def watchElse(partial_assignment, watchedLiteral, negUnitLiteral):
    unitPropQueue = [[], []]
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
                unitPropQueue[0].append(clause[1-changeIndex])
                unitPropQueue[1].append(clause)

    return unitPropQueue


def unitPropagateWL(partial_assignment, watchedLiteral, literalAssignment):
    if literalAssignment == 0:
        unitPropQueue = watchedLiteral[0]
    else:
        unitPropQueue = [literalAssignment]

    decisionLevel = len(partial_assignment.values()) + 1
    antecedent = {}
    while unitPropQueue:
        literalAssignment = unitPropQueue.pop(0)

        if -literalAssignment in partial_assignment:
            return False

        partial_assignment[literalAssignment] = decisionLevel

        if -literalAssignment in watchedLiteral:
            updateWatched = watchElse(
                partial_assignment, watchedLiteral, -literalAssignment)

            if isinstance(updateWatched, tuple):
                if (decisionLevel == 1):
                    return False
                return learnConflict(partial_assignment, updateWatched, decisionLevel, watchedLiteral)

            if updateWatched[0]:
                unitPropQueue = unitPropQueue + updateWatched[0]
                for i in range(len(updateWatched[0])):
                    antecedent[updateWatched[0][i]] = updateWatched[1][i]

    return True


def dpll_sat_solve_WL(clause_set, partial_assignment={}, watchedLiteral={}, occurrence=[], cardinality=0, nextLiteral=0):
    # Initialize watched literals
    if watchedLiteral == {}:
        literalOccurrence = getOccurrence(clause_set)
        occurrence = sorted(literalOccurrence,
                            key=literalOccurrence.get, reverse=True)
        cardinality = max(max(occurrence), -min(occurrence))
        watchedLiteral[0] = []

        for clause in clause_set:
            if len(clause) == 1:
                watchedLiteral[0].append(clause[0])
                continue

            for i in range(2):
                if clause[i] in watchedLiteral:
                    watchedLiteral[clause[i]].append(clause)
                else:
                    watchedLiteral[clause[i]] = [clause]

    # Unit prop and check if unsat
    if unitPropagateWL(partial_assignment, watchedLiteral, nextLiteral) == False:
        return False

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
    while branch1:
        if len(partial_assignment) == cardinality:
            return list(branch1)

        if branch1[1] > len(previousPartialAssignment.values()):
            return branch1

        branch1 = dpll_sat_solve_WL(
            clause_set, partial_assignment, watchedLiteral, occurrence, cardinality, nextLiteral)

    # Reset
    partial_assignment = previousPartialAssignment

    branch2 = dpll_sat_solve_WL(
        clause_set, partial_assignment, watchedLiteral, occurrence, cardinality, -nextLiteral)
    while branch2:
        if len(partial_assignment) == cardinality:
            return list(branch2)

        if branch2[1] > len(previousPartialAssignment.values()):
            return branch2

        branch2 = dpll_sat_solve_WL(
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
problem = load_dimacs("8queens.txt")
#problem = load_dimacs("LNP-6.txt")
#problem = load_dimacs("gt.txt")
#problem = load_dimacs("uf20-099.txt")
#problem = load_dimacs("CBS_k3_n100_m403_b10_0.txt")

#print(problem)
#print(simple_sat_solve(problem))
#print(branching_sat_solve(problem, []))
print(dpll_sat_solve_WL(problem))
#print(sat_checker(problem, dpll_sat_solve_WL(problem)))
#print(sat_checker(problem, [-28, -37, -29, -36, -19, -46, -20, -38, -21, -27, -30, -35, -43, -22, -44, -45, -10, -55, -11, -18, -26, -34, 42, -47, -50, 12, -39, -51, -13, -31, -52, -14, 23, 53, -15, -54, -1, -2, -3, -4, -5, 6, -7, -8, -9, -17, 25, -33, -41, -49, -57, -64, -56, -58, -48, 59, 40, -60, -32, -61, -24, -62, -16, -63]))
