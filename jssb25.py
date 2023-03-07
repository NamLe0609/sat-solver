# This is an implementation of a SAT solver by Nam Le for COMP1051_2022
import itertools
from collections import Counter

#################
#   Question 4  #
#################

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

#################
#   Question 5  #
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

    return "Cannot Solve"

#################
#   Question 6  #
#################
    
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
        return "Cannot Solve"
    
def eliminate(clause_set, literalAssignment):
    newClauseSet = []
    
    for clause in clause_set:
        
        if literalAssignment not in clause and -literalAssignment not in clause:
            newClauseSet.append(clause)

        elif literalAssignment not in clause and -literalAssignment in clause:
            newClauseSet.append(
                [literal for literal in clause if literal != -literalAssignment])
        
    return newClauseSet

#################
#   Question 7  #
#################

def unit_propagate(clause_set):
    propagateClause = next((clause for clause in clause_set if len(clause) == 1), None)
    while propagateClause:
        clause_set = eliminate(clause_set, propagateClause[0])
        propagateClause = next((clause for clause in clause_set if len(clause) == 1), None)
        
    return clause_set

#################
#   Question 8  #
#################

def dpll_sat_solve(clause_set, partial_assignment):
    newClauseSet = clause_set
    
    if partial_assignment != []:
        newClauseSet = eliminate(clause_set, partial_assignment[-1])
    
    newClauseSet = unit_propagate(newClauseSet)
    
    if newClauseSet == []:
        return partial_assignment
    
    if [] in newClauseSet:
        partial_assignment.pop()
        return False
    
    literalList = [literal for clause in newClauseSet for literal in clause]
    nextLiteral = Counter(literalList).most_common(1)[0][0]
        
    partial_assignment.append(nextLiteral)
    branch1 = dpll_sat_solve(newClauseSet, partial_assignment)
    if branch1:
        return partial_assignment
    
    partial_assignment.append(-nextLiteral)
    branch2 = dpll_sat_solve(newClauseSet, partial_assignment)
    if branch2:
        return partial_assignment
    
    if partial_assignment:
        partial_assignment.pop()
    else:
        return False
    
#################
#   Question 9  #
#################

def watchElse(partial_assignment, watchedLiteral, solved, negUnitLiteral):
    unitPropQueue = []
    watchedClause = watchedLiteral[negUnitLiteral].copy()
    
    for clause in watchedClause:
        if clause not in solved:
            canWatchElse = False
            canWatchWatched = False
            
            for literal in clause:
                if -literal in partial_assignment or literal == negUnitLiteral:
                    continue
                
                elif literal in partial_assignment and clause not in solved:
                    solved.add(clause)
                    canWatchElse = True
                    break
                
                elif literal in watchedLiteral and clause in watchedLiteral[literal]:
                    canWatchWatched = literal
                    
                else:
                    canWatchElse = True
                    watchedLiteral[negUnitLiteral].remove(clause)
                    if literal not in watchedLiteral:
                        watchedLiteral[literal] = {clause}
                    else:
                        watchedLiteral[literal].add(clause)
                    break
            
            if canWatchWatched and not canWatchElse:
                unitPropQueue.append(canWatchWatched)
                
            elif not canWatchElse and not canWatchWatched:
                return False
            
    if unitPropQueue:
        return unitPropQueue
    else:
        return True

def unitPropagateWL(partial_assignment, watchedLiteral, solved):
    if partial_assignment:
        unitPropQueue = [partial_assignment[-1]]
        
        while unitPropQueue:
            unitClauseLiteral = unitPropQueue.pop(0)
            if unitClauseLiteral in watchedLiteral:
                solved.update(watchedLiteral[unitClauseLiteral])
            
            if -unitClauseLiteral in watchedLiteral:
                updateWatched = watchElse(partial_assignment, watchedLiteral, solved, -unitClauseLiteral)
                
                if not updateWatched:
                    return False
                
                if isinstance(updateWatched, list):
                    unitPropQueue = unitPropQueue + updateWatched
            
            if -unitClauseLiteral in partial_assignment:
                return False
            
            if unitPropQueue and unitPropQueue[0] not in partial_assignment:
                partial_assignment.append(unitPropQueue[0])
        
        return True

def dpll_sat_solve_WL(clause_set, partial_assignment=[], watchedLiteral={}, solved=set(), totalClauseLen=0):
    
    # Initialize watched literals
    if partial_assignment == []:
        watchedLiteral = {}
        unitPropQueue = []
        
        for clause in clause_set:
            if len(clause) == 1:
                unitPropQueue.append(clause[0])
                continue
            
            totalClauseLen += 1
            for i in range(2):
                if clause[i] in watchedLiteral:
                    watchedLiteral[clause[i]].add(tuple(clause))
                else:
                    watchedLiteral[clause[i]] = {tuple(clause)}
        
        while unitPropQueue:
            literalAssignment = unitPropQueue.pop()
            
            if literalAssignment in partial_assignment:
                continue
            
            if -literalAssignment in partial_assignment:
                return False
            
            partial_assignment.append(literalAssignment)
            unitPropagateWL(partial_assignment, watchedLiteral, solved)
            
    
    # Unit prop and check if unsat
    if unitPropagateWL(partial_assignment, watchedLiteral, solved) == False:
        return False
    
    # Check if sat
    if len(solved) == totalClauseLen:
        return partial_assignment
    
    # Choose next literal
    nextLiteral = 0
    for key in watchedLiteral:
        if key not in partial_assignment and -key not in partial_assignment:
            nextLiteral = key
            break
    
    # For reset
    previousPartialAssignment = partial_assignment[:]
    previousSolved = solved.copy()
    
    partial_assignment.append(nextLiteral)
    branch1 = dpll_sat_solve_WL(clause_set, partial_assignment, watchedLiteral, solved, totalClauseLen)
    if branch1:
        return branch1
    
    # Reset
    partial_assignment = previousPartialAssignment
    solved = previousSolved
    
    partial_assignment.append(-nextLiteral)
    branch2 = dpll_sat_solve_WL(clause_set, partial_assignment, watchedLiteral, solved, totalClauseLen)
    if branch2:
        return branch2
    
    return False
    
#########################
#   Additional Tools    #
#########################

def sat_checker(clause_set, truthAssignment):
    if type(truthAssignment) == str:
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

#print(simple_sat_solve(problem))
#print(branching_sat_solve(problem, []))
print(dpll_sat_solve_WL(problem))
#print(sat_checker(problem, dpll_sat_solve_WL(problem)))