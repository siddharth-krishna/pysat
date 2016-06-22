import itertools
from pysat import *

def add_rules(solver):
    # Sudoku rules encoding:
    # Each cell has at least one number
    for r, c in itertools.product(range(1, 10), repeat=2):
        solver.addClause([int("%d%d%d" % (r, c, n)) for n in range(1, 10)])
        for n1, n2 in itertools.combinations(range(1, 10), 2):
            solver.addClause([int("-%d%d%d" % (r, c, n1)), int("-%d%d%d" % (r, c, n2))])

    # Each row has 1..9 exactly once
    for r in range(1, 10):
        for n in range(1, 10):
            solver.addClause([int("%d%d%d" % (r, c, n)) for c in range(1, 10)])

    # Each col has 1..9 exactly once        
    for c in range(1, 10):
        for n in range(1, 10):
            solver.addClause([int("%d%d%d" % (r, c, n)) for r in range(1, 10)])

    # Each block has 1..9 exactly once
    for startRow, startCol in itertools.product([1, 4, 7], repeat=2):
        for n in range(1, 10):
            solver.addClause([int("%d%d%d" % (startRow + deltaRow, startCol + deltaCol, n))
                            for deltaRow, deltaCol in itertools.product([0, 1, 2], repeat=2)])

def read_sudoku(fname):
    literals = []
    with open(fname, 'r') as fin:
        for l in fin.readlines():
            n = int(l.replace(" ", ""))
            literals.append(n)
    return literals

def add_sudoku(solver, literals):
    for l in literals:
        solver.addClause([l])

solver = Solver()
add_rules(solver)
sudoku = read_sudoku("../sudoku-ex/ex01.txt")
print(", ".join([str(x) for x in sudoku]))
add_sudoku(solver, sudoku)
result = solver.solve()
cst = Constants()
if result == cst.lit_False:
    print("c UNSATISFIABLE")
elif result == cst.lit_True:
    print("c SATISFIABLE")
else:
    print("c UNKNOWN")
solver.printStats()
