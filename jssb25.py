# This is an implementation of a SAT solver by Nam Le

#################
#   References  #
#################

""" 
https://en.wikipedia.org/wiki/DPLL_algorithm 
https://en.wikipedia.org/wiki/Backjumping
https://cs.stackexchange.com/questions/63954/best-improvements-to-do-to-the-dpll-sat-algorithm
https://cs.stackexchange.com/questions/150557/what-are-efficient-approaches-to-implement-unit-propagation-in-dpll-based-sat-so
https://en.wikipedia.org/wiki/Conflict-driven_clause_learning
https://baldur.iti.kit.edu/sat/files/2019/l05.pdf
https://www.researchgate.net/publication/220565739_Propositional_Satisfiability_and_Constraint_Programming_A_comparative_survey
https://www.iospress.com/catalog/books/handbook-of-satisfiability-2
https://www.cs.cornell.edu/courses/cs4860/2009sp/lec-04.pdf
"""

import itertools

#################
# DIMACS OPENER #
#################

def load_dimacs(filename):
    with open(filename) as f:
        lines = f.readlines()
        f.close()

    clauseSet = []
    # n is the number of the largest variable, and
    # m is the total number of clauses in the clause-set
    ignored = {"c", "p", "%"}
    for line in lines:
        if line[0] in ignored:
            continue
        sections = line.strip('\n').split(" ")
        clause = [int(literal) for literal in sections if literal != "0"]
        clauseSet.append(clause)
        
    return clauseSet

#################
#  Brute force  #
#################

# Converts a literal into its appropriate
# logical assignment depending on the given permutation
def literalConverter(permutation, literal):
    logicalAssignment = int(permutation[-abs(literal)])
    return logicalAssignment if literal > 0 else 1 - logicalAssignment


def permutationConverter(permutation):
    convertedPermutation = []
    permutation = permutation[::-1]
    for i in range(len(permutation)):
        if permutation[i] == "0":
            convertedPermutation.append(-(i+1))
        else:
            convertedPermutation.append(i+1)

    return convertedPermutation

# Solves a sat by going through every possible permutations
# of truth assignments and applying them to literals in each clause
def simple_sat_solve(clause_set):
    # Flatten clause set and get the largest number
    n = max([abs(literal) for clause in clause_set for literal in clause])

    # Code from https://stackoverflow.com/questions/4928297/all-permutations-of-a-binary-sequence-x-bits-long
    permutations = ("".join(seq) for seq in itertools.product("01", repeat=n))
    for permutation in permutations:
        resolvedClauseSet = set()

        for clause in clause_set:
            resolvedClause = 0

            for literal in clause:
                if literalConverter(permutation, literal) == 1:
                    resolvedClause = 1
                    break

            resolvedClauseSet.add(resolvedClause)

        if 0 in resolvedClauseSet:
            continue
        else:
            return permutationConverter(permutation)

    return False

##################
#Branching solver#
##################
    
def branching_sat_solve(clause_set, partial_assignment):
    newClauseSet = clause_set
    if partial_assignment != []:
        literalAssignment = partial_assignment[-1]
        newClauseSet = eliminate(clause_set, literalAssignment)

    if newClauseSet == []:
        return partial_assignment

    if [] in newClauseSet:
        partial_assignment.pop()
        return
    
    partial_assignment.append(len(partial_assignment) + 1)
    branch0 = branching_sat_solve(
        newClauseSet, partial_assignment)

    if branch0:
        return branch0
    
    partial_assignment.append(-(len(partial_assignment) + 1))
    branch1 = branching_sat_solve(
        newClauseSet, partial_assignment)

    if branch1:
        return branch1
    
    if partial_assignment:
        partial_assignment.pop()
    else:
        return False
    
def eliminate(clause_set, literalAssignment):
    newClauseSet = []
    
    for clause in clause_set:
        
        if literalAssignment not in clause and -literalAssignment not in clause:
            newClauseSet.append(clause)

        elif literalAssignment not in clause and -literalAssignment in clause:
            newClauseSet.append(
                [literal for literal in clause if literal != -literalAssignment])
        
    return newClauseSet

##################
# Basic unitProp # 
##################

def unit_propagate(clause_set):
    propagateClause = next((clause for clause in clause_set if len(clause) == 1), None)
    while propagateClause:
        clause_set = eliminate(clause_set, propagateClause[0])
        propagateClause = next((clause for clause in clause_set if len(clause) == 1), None)
        
    return clause_set

##################
#   Main DPLL    #
##################

#
#   Get occurrence of literals in clause set algorithm
#

def getOccurrence(clause_set):
    occurrence = {}
    for clause in clause_set:
        for literal in clause:
            if literal in occurrence:
                occurrence[literal] += 1
            else:
                occurrence[literal] = 1
    return occurrence


#
#   Learn conflict algorithm
#

def learnConflict(partial_assignment, conflictClause, decisionLevel, watchedLiteral, antecedent, assigned):
    
    # If there is a conflict at without making any decisions, 
    # Then there must be an inherent contradiction and thus 
    # The sat solver must return false
    
    if decisionLevel == 0:
        return -1
    
    # Finds the 1-UIP to learn the clause from
    
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
    
    # If the learnt clause is empty, then that means there is a unit clause to learn
    # Add this to WL[0] (which keeps track of which literal has to be a unit)
    # And backtracks to first level (before any assignments)
    
    if not learnedClause:
        watchedLiteral[0].add(largest[0])
        return 0
        
    secondLargest = [0, 0]
    for literal in learnedClause:
        literalDecisionLevel = partial_assignment[-literal]
        
        if literalDecisionLevel >= secondLargest[1]:
            secondLargest = [literal, literalDecisionLevel]


    # Watch the new clause that has been learnt
    
    watchedLearnedClause = [largest[0], secondLargest[0]]
    learnedClause.remove(secondLargest[0])
    watchedLearnedClause += list(learnedClause)

    for i in range(2):
        if watchedLearnedClause[i] in watchedLiteral:
            watchedLiteral[watchedLearnedClause[i]].append(watchedLearnedClause)
        else:
            watchedLiteral[watchedLearnedClause[i]] = [watchedLearnedClause]

    return secondLargest[1]


#
#   Process watched literal algorithm
#

def watchElse(partial_assignment, watchedLiteral, negUnitLiteral):
    unitPropQueue = []
    if negUnitLiteral not in watchedLiteral:
        return unitPropQueue
    watchedClause = watchedLiteral[negUnitLiteral].copy()

    for clause in watchedClause:
        
        # Both watched literals in a clause are placed at the beginning of the clause
        # As such, we can check whether a clause is sat or not by checking if either 
        # Is in partial assignment
        
        if clause[0] in partial_assignment or clause[1] in partial_assignment:
            continue

        # Check to see which literal is the one that needs to change watched status
        changeIndex = 0
        if clause[1] == negUnitLiteral:
            changeIndex = 1

        # Check to see if another literal can be watched
        # If it can, swap its place with the wl that needs changing
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
            
            # If the wl that needs changing has not been swapped
            # And the other wl is false then return the conflicting clause
            if -clause[1-changeIndex] in partial_assignment:
                return tuple(clause)
            
            # Otherwise add to unitProp queue the other wl
            else:
                unitPropQueue.append((clause[1-changeIndex], clause))
                
    return unitPropQueue

#
#   Unit propagation algorithm
#

def unitPropagateWL(partial_assignment, watchedLiteral, literalAssignment):
    
    # Cases for beginning/ from beginning unit prop and normal unit prop
    if literalAssignment == 0:
        unitPropQueue = []
        decisionLevel = 0
        for unit in watchedLiteral[0]:
            unitPropQueue.append((unit, []))
    else:
        unitPropQueue = [(literalAssignment, [])]
        decisionLevel = len(set(partial_assignment.values())) + 1
    
    # Antecedent keeps track of which clause propagated to give the unit literal
    antecedent = {}
    
    # Assigned keeps track of the order at which clauses were found through unit propagation
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
            
            # Updates watched literals if the negation of the unit literal is watched
            updateWatched = watchElse(
                partial_assignment, watchedLiteral, -literalAssignment)

            # Does clause learning if a tuple is returned
            # UpdateWatched either returns a list of tuples containing the possible unit literal and its antecedent if successful
            # or a tuple representing the conflict clause.
            # The reason why its a tuple (conflicting) is to discern it from the list (non-conflicting) 
            
            if isinstance(updateWatched, tuple):
                return learnConflict(partial_assignment, updateWatched, decisionLevel, watchedLiteral, antecedent, assigned)

            if updateWatched:
                unitPropQueue = unitPropQueue + updateWatched

    return True

#
#   DPLL+ algorithm with watched literals, clause learning and backtracking using basic most common occurrence heuristics
#

def dpll_sat_solve_WL(clause_set, partial_assignment, watchedLiteral={}, occurrence=[], cardinality=0, nextLiteral=0):
    # Initialize watched literals
    if watchedLiteral == {}:
        partial_assignment = {}
        literalOccurrence = getOccurrence(clause_set)
        occurrence = sorted(literalOccurrence, key=literalOccurrence.get, reverse=True)
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
        

#
#   Wrap main DPLL in auxillary function to keep additional args separate
#
        
def dpll_sat_solve(clause_set, partial_assignment):
    return dpll_sat_solve_WL(clause_set, partial_assignment, {}, [], 0, 0)
    
#########################
#   Additional Tools    #
#########################

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