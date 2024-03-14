#Look for #IMPLEMENT tags in this file.
'''
All encodings need to return a CSP object, and a list of lists of Variable objects 
representing the board. The returned list of lists is used to access the 
solution. 

For example, after these three lines of code

    csp, var_array = caged_csp(board)
    solver = BT(csp)
    solver.bt_search(prop_FC, var_ord)

var_array[0][0].get_assigned_value() should be the correct value in the top left
cell of the FunPuzz puzzle.

The grid-only encodings do not need to encode the cage constraints.

1. binary_ne_grid (worth 10/100 marks)
    - An enconding of a FunPuzz grid (without cage constraints) built using only 
      binary not-equal constraints for both the row and column constraints.

2. nary_ad_grid (worth 10/100 marks)
    - An enconding of a FunPuzz grid (without cage constraints) built using only n-ary 
      all-different constraints for both the row and column constraints. 

3. caged_csp (worth 25/100 marks) 
    - An enconding built using your choice of (1) binary binary not-equal, or (2) 
      n-ary all-different constraints for the grid.
    - Together with FunPuzz cage constraints.

'''
from cspbase import *
import itertools
import math

############################################################################################
############################################################################################
def binary_ne_grid(fpuzz_grid):
    n = fpuzz_grid[0][0]
    dom = list(range(1, n+1))
    
    # Variable at row i, column j can be accessed by vars[i*n + j]
    vars = []
    for i in range(n*n):
        vars.append(Variable("", dom))
    
    cons = []
    # Generate satisfying tuples for binary not-equal constraints
    sat_tuples = []
    for t in itertools.product(dom, dom):
        if t[0] != t[1]:
            sat_tuples.append(t)
    # Set up binary not-equal constraints for rows
    for i in range(n):
        for j in range(n):
            for k in range(j+1, n):
                con = Constraint("", [vars[i*n + j], vars[i*n + k]])
                con.add_satisfying_tuples(sat_tuples)
                cons.append(con)
    # Set up binary not-equal constraints for columns
    for j in range(n):
        for i in range(n):
            for k in range(i+1, n):
                con = Constraint("", [vars[i*n + j], vars[k*n + j]])
                con.add_satisfying_tuples(sat_tuples)
                cons.append(con)
    
    csp = CSP("binary_ne_grid", vars)
    for c in cons:
        csp.add_constraint(c)
        
    # Create a list of lists of Variable objects representing the board
    # The variables should reference the same objects as those in the CSP
    csp_vars = []
    for i in range(n):
        csp_vars.append(vars[i*n : (i+1)*n])
    
    return csp, csp_vars
    
############################################################################################
############################################################################################
def nary_ad_grid(fpuzz_grid):
    n = fpuzz_grid[0][0]
    dom = list(range(1, n+1))
    
    # Variable at row i, column j can be accessed by vars[i*n + j]
    vars = []
    for i in range(n*n):
        vars.append(Variable("", dom))
            
    cons = []
    for i in range(n):
        con = Constraint("", vars[i*n : (i+1)*n])
        con.add_satisfying_tuples(list(itertools.permutations(dom)))
        cons.append(con)
        
    for j in range(n):
        con = Constraint("", [vars[i*n + j] for i in range(n)])
        con.add_satisfying_tuples(list(itertools.permutations(dom)))
        cons.append(con)
        
    csp = CSP("nary_ad_grid", vars)
    for c in cons:
        csp.add_constraint(c)
        
    csp_vars = []
    for i in range(n):
        csp_vars.append(vars[i*n : (i+1)*n])
        
    return csp, csp_vars
    
############################################################################################
############################################################################################
def caged_csp(fpuzz_grid):
    n = fpuzz_grid[0][0]
    dom = list(range(1, n+1))
    
    # Variable at row i, column j can be accessed by vars[i*n + j]
    vars = []
    for i in range(n):
        for j in range(n):
            vars.append(Variable("V{}{}".format(i,j), dom))
    
    #################################################
    # Add constraints for rows and cols
    cons = []
    sat_tuples = []
    for t in itertools.product(dom, dom):
        if t[0] != t[1]:
            sat_tuples.append(t)
    # Set up binary not-equal constraints for rows
    for i in range(n):
        for j in range(n):
            for k in range(j+1, n):
                con = Constraint("", [vars[i*n + j], vars[i*n + k]])
                con.add_satisfying_tuples(sat_tuples)
                cons.append(con)
    # Set up binary not-equal constraints for columns
    for j in range(n):
        for i in range(n):
            for k in range(i+1, n):
                con = Constraint("", [vars[i*n + j], vars[k*n + j]])
                con.add_satisfying_tuples(sat_tuples)
                cons.append(con)
                
    #################################################
    # Add constraints for cages
    for cage in fpuzz_grid[1:]:
        
        if len(cage) == 2:
            cell = cage[0]
            row_idx = (cell // 10) - 1
            col_idx = (cell % 10) - 1
            target_val = cage[1]
            con = Constraint("", [vars[row_idx*n + col_idx]])
            con.add_satisfying_tuples([(target_val,)])
            cons.append(con)
            continue
        
        cage_op = cage[-1]
        cage_res = cage[-2]
        # Extract the variables in the cage
        cage_vars = []
        for cell in cage[:-2]:
            row_idx = (cell // 10) - 1
            col_idx = (cell % 10) - 1
            cage_vars.append(vars[row_idx*n + col_idx])
        con = Constraint("cage {} {}".format(cage_res, cage_op), cage_vars)
        sat_tuples = []
        
        if cage_op == 0: # Addition
            for t in itertools.product(dom, repeat=len(cage_vars)):
                if sum(t) == cage_res:
                    sat_tuples.append(t)
        elif cage_op == 1: # Subtraction
            for t in itertools.product(dom, repeat=len(cage_vars)):
                if (t[0] - sum(t[1:])) == cage_res:
                    perms = itertools.permutations(t)
                    unique_perms = set(perms)
                    for perm in unique_perms:
                        if perm not in sat_tuples:
                            sat_tuples.append(perm)
        elif cage_op == 2: # Division
            for t in itertools.product(dom, repeat=len(cage_vars)):
                if (t[0] / math.prod(t[1:])) == cage_res:
                    perms = itertools.permutations(t)
                    unique_perms = set(perms)
                    for perm in unique_perms:
                        if perm not in sat_tuples:
                            sat_tuples.append(perm)
        else: # Multiplication
            for t in itertools.product(dom, repeat=len(cage_vars)):
                if math.prod(t) == cage_res:
                    sat_tuples.append(t)

        con.add_satisfying_tuples(sat_tuples)
        cons.append(con)
    #################################################
    
    csp = CSP("binary_ne_grid", vars)
    for c in cons:
        csp.add_constraint(c)

    csp_vars = []
    for i in range(n):
        csp_vars.append(vars[i*n : (i+1)*n])
    
    return csp, csp_vars