#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.  

'''This file will contain different constraint propagators to be used within 
   bt_search.

   propagator == a function with the following template
      propagator(csp, newly_instantiated_variable=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newly_instaniated_variable is an optional argument.
      if newly_instantiated_variable is not None:
          then newly_instantiated_variable is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method). 
      bt_search NEEDS to know this in order to correctly restore these 
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been 
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newly_instantiated_variable = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated 
        constraints) 
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope 
        contains only one variable) and we forward_check these constraints.


      PROPAGATOR called with newly_instantiated_variable = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

   '''

def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no 
    propagation at all. Just check fully instantiated constraints'''
    
    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []

def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with 
       only one uninstantiated variable. Remember to keep 
       track of all pruned variable,value pairs and return '''     
    
    constraints = []
    if not newVar:
        constraints = csp.get_all_cons()
    else:
        constraints = csp.get_cons_with_var(newVar)
        
    pruned = []
    for c in constraints:
        if c.get_n_unasgn() == 1:
            uvar = c.get_unasgn_vars()[0]
            # All values in current domain of uvar
            for val in uvar.cur_domain():
                # The value that we are going to check with
                vals = []
                # We have to do this because the scope of constraint must be in correct order
                for var in c.get_scope():
                    if var == uvar:
                        vals.append(val)
                    else:
                        vals.append(var.get_assigned_value())
                # Prune this value of uvar
                if not c.check(vals):
                    pruned.append((uvar, val))
                    uvar.prune_value(val)
            if uvar.cur_domain_size() == 0:
                return False, pruned
    return True, pruned

def prop_FI(csp, newVar=None):
    '''Do full inference. If newVar is None we initialize the queue
       with all variables.'''
    
    queue = []
    if not newVar:
        queue = csp.get_all_vars()
    else:
        queue.append(newVar)
    
    pruned = []
    while queue:
        w = queue.pop(0)
        for c in csp.get_cons_with_var(w):
            for v in c.get_scope():
                if v == w:
                    continue
                s = v.cur_domain_size()
                for d in v.cur_domain():
                    # Check if there is an assignment A for all other variables (other than v and w)
                    # in scope of c such that c(A, d) is true
                    if not c.has_support(v, d):
                        v.prune_value(d)
                        pruned.append((v, d))
                        if v.cur_domain_size() == 0:
                            return False, pruned
                        
                if v.cur_domain_size() != s and v not in queue:
                    queue.append(v)
    return True, pruned
