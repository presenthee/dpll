import argparse
import logging
import time
import random
import numpy as np

# logging.disable(logging.DEBUG)
parser = argparse.ArgumentParser(description="DPLL based SAT solver")
parser.add_argument('fname', type=str, help='Input file name')
parser.add_argument('--b', type=str, default='seq', help='Branching heuristic')
arg = parser.parse_args()

class Clause:
  def __init__(self, clause, learned=False, sat=False, score=0):
    self.origin = clause
    self.current = set(clause)
    self.learned = learned
    self.sat = sat
    self.score = score

  def __str__(self):
    return str(self.current)

  def reset(self):
    self.current = set(self.origin)
    self.sat = False

  # update the clause with the given assignment.
  def update(self, assignment):
    if self.sat:
      return

    # logging.debug("update clause %s, id: %s" % (str(self.current), id(self.current)))
    for var in self.current.copy():
      if abs(var) in assignment:
        self.assign(var, assignment[abs(var)][0])
    # logging.debug("updated clause %s" % str(self.current))
    # logging.debug("sat: %s" % self.sat)

  # check if the clause is unit.
  def is_unit(self):
    return len(self.current) == 1

  # check if the clause is empty.
  def is_empty(self):
    return not self.current and not self.sat

  # check if the clause is satisfied.
  def is_sat(self):
    return self.sat

  # assign a value to the literal in the clause.
  def assign(self, lit, value):
    if value == (lit > 0):
      self.sat = True
      return True
    else:
      self.current.remove(lit)
      return False

class Solver:
  def __init__(self, formula, vars, n_vars, b='seq', limit=100):
    self.assignment = {}
    self.formula = formula
    self.learnts = set()
    self.vars = vars
    self.stack_prop = []
    self.level = 1
    self.heuristic = b
    self.score = np.zeros(n_vars + 1)
    self.limit_factor = 0.5
    self.limit_inc =1.1
    self.learnt_limit = limit
    self.forget_factor = 1

  def __str__(self):
    return ' '.join([ (str(var) if val else str(-var) ) for var, (val, _) in self.assignment.items() ])

  def solve(self):
    while True:
      # logging.debug("level %d started." % self.level)
      # check if the formula is solved.
      if self.is_solved():
        return True

      # unit propagation
      conflict_c = self.unit_propagation()

      # if there is a conflict, learn a new clause and backtrack.
      if conflict_c is not None:
        # decay scores
        self.score = self.score * 0.95

        # clause learning
        learnt_set = self.learn(conflict_c)

        # if we can't learn a new clause, return False.
        if not learnt_set:
          return False

        learnt_c = Clause(frozenset(learnt_set), learned=True, score=1)

        # add the learnt clause to the formula and backtrack.
        self.learnts.add(learnt_c)
        self.backtrack(learnt_c)
        continue

      # if sat is True after propagation, return True.
      elif self.is_solved():
        return True

      # if the limit is reached, restart.
      elif len(self.learnts) > self.learnt_limit:
        self.forget()
        self.restart()
        continue

      # if there is no conflict, determine a new assignment.
      else:
        var = self.decide()
        # logging.debug("var %d selected" % var)
        # logging.debug("var %d is set to False" % var)
        self.assignment[var] = (False, self.level)
        self.level += 1

  def is_solved(self):
    return all([ c.sat for c in self.formula.union(self.learnts) ])

  def unit_propagation(self):
    # logging.debug("level %d unit propagation started." % self.level)
    while True:
      progress = False
      for c in self.formula.union(self.learnts):
        # update the clause with the current assignment.
        c.update(self.assignment)

        if c.is_sat():
          continue

        # if the clause is empty, return the clause.
        if c.is_empty():
          # logging.debug("for clause %s" % str(c.origin))
          # logging.debug("C is empty")
          return c

        # if the clause is unit, assign the variable.
        elif c.is_unit():
          # logging.debug("for clause %s" % str(c.origin))
          # logging.debug("C is unit")
          progress = True
          var = c.current.pop()
          self.stack_prop.append((var, c, self.level))
          self.assignment[abs(var)] = (var > 0, self.level)
          c.assign(var, var > 0)
          # logging.debug("update %d to %d" % (abs(var), var > 0))

      if not progress:
        return None # no conflict

  def learn(self, conflict_c):
    # logging.debug("level %d clause learning started." % self.level)
    # logging.debug("conflict_c: %s" % str(conflict_c.origin))
    learnt_set = set(conflict_c.origin)
    stack_prop = self.stack_prop.copy()
    while stack_prop:
      var, c, _ = stack_prop.pop()
      # logging.debug("var: %d, c: %s" % (var, str(c.origin)))
      if c != conflict_c and -var in learnt_set:
        if c.learned:
          # logging.debug("c is learned.")
          c.score += 1

        # logging.debug("current learnt_set: %s" % str(learnt_set))
        prop_c = set(c.origin.copy())
        prop_c.remove(var)
        learnt_set.remove(-var)
        learnt_set = learnt_set.union(prop_c)
        # logging.debug("updated learnt_set: %s" % str(learnt_set))

        for var in learnt_set:
          self.score[abs(var)] += 1

    return learnt_set

  def backtrack(self, learnt_c, is_restart=False):
    # logging.debug("level %d backtracking started." % self.level)
    # find max level of vars in learnt_c
    if not is_restart:
      max_level = 0
      for var in learnt_c.origin:
        if abs(var) in self.assignment:
          max_level = max(max_level, self.assignment[abs(var)][1])

      # remove assignments with level >= max_level
      for var, (_, level) in self.assignment.copy().items():
        if level < max_level:
          continue
        del self.assignment[var]

      # remove propagated vars with level >= max_level
      self.stack_prop = [ (var, c, level) for var, c, level in self.stack_prop if level < max_level ]

    # restart
    else:
      max_level = 1
      self.stack_prop = []
      self.assignment = {}

    self.level = max_level

    # reset the formula
    for c in self.formula.union(self.learnts):
      c.reset()

  def forget(self):
    # logging.debug("level %d forgetting..." % self.level)
    # sort the learnt clauses by score in descending order.
    learnts = sorted(self.learnts, key=lambda x: x.score, reverse=True)
    # remove half of the learnt clauses
    self.learnts = set(learnts[:len(learnts) // 2])

  def restart(self):
    # logging.debug("level %d restarting..." % self.level)
    self.backtrack(None, is_restart=True)
    self.learnt_limit *= self.limit_inc

  def decide(self):
    # logging.debug("level %d deciding..." % self.level)
    if self.heuristic == 'seq':
      return self.decide_seq()
    elif self.heuristic == 'random':
      return self.decide_random()
    elif self.heuristic == 'vsids':
      return self.decide_vsids()

  def decide_seq(self):
    for var in self.vars:
      if var not in self.assignment:
        return var

  # randomly select a variable to assign.
  def decide_random(self):
    vars = self.vars - set(self.assignment.keys())
    return random.choice(list(vars))

  # vsids heuristic
  def decide_vsids(self):
    vars = self.vars - set(self.assignment.keys())
    max_score = -1
    max_var = None
    logging.debug("scores: %s" % str(self.score))
    for var in vars:
      if self.score[var] > max_score:
        max_score = self.score[var]
        max_var = var

    return max_var

# Read input DIMACS CNF format file and parse it.
# returns a parsed set of sets (clauses) and set of int (variables).
def parse_input(f):
  with open(f, 'r') as f:
    lines = f.readlines()
    lines = [ line.strip() for line in lines if not line.startswith('c') and line.strip() != '']

  n_vars = 0
  n_clauses = 0

  if len(lines) == 0:
    logging.error("Invalid input file format: Empty file")
    exit(1)

  if lines[0].startswith('p'):
    _, _, n_vars, n_clauses = lines[0].split()
    n_vars = int(n_vars)
    n_clauses = int(n_clauses)
  else:
    logging.error("Invalid input file format: First line should start with 'p'")
    exit(1)

  # logging.debug("Number of variables: %s" % n_vars)
  # logging.debug("Number of clauses: %s" % n_clauses)

  clauses = set()
  vars = set()

  for i in range(1, n_clauses + 1):
    clause = lines[i].split()
    clause = [ int(x) for x in clause if x != '0' ] # list?
    vars.update([abs(x) for x in clause])
    clause = Clause(frozenset(clause))
    clauses.add(clause)

  return clauses, vars, n_vars

# Main function of SAT solver.
def main():
  time_start = time.time()
  logger = logging.getLogger(__name__)

  logging.basicConfig(
    level=logging.DEBUG,
    format='[%(levelname)s] %(message)s',
    filename='debug.log',
  )
  # logging.debug("Main function started.")

  # parse the input file.
  clauses, vars, n_vars = parse_input(arg.fname)
  # logging.debug("Parsed variables: %s" % vars)

  # create a solver object and solve the problem.
  solver = Solver(clauses, vars, n_vars, b=arg.b)
  if solver.solve():
    print("s SATISFIABLE")
    print("v %s 0" % str(solver))

  else:
    print("s UNSATISFIABLE")

  print("execution time: %f" % (time.time() - time_start))

if __name__ == '__main__':
  main()
