#!/usr/bin/env python3

import fileinput

# mostly stolen from
# https://stackoverflow.com/questions/28890268/parse-dimacs-cnf-file-python

cnf = list()
cnf.append(list())
maxvar = 0

for line in fileinput.input():
    line = line.rstrip()
    tokens = line.split()
    if tokens[0] == "%":
        break
    if len(tokens) != 0 and tokens[0] not in ("p", "c"):
        for tok in tokens:
            lit = int(tok)
            maxvar = max(maxvar, abs(lit))
            if lit == 0:
                cnf.append(list())
            else:
                cnf[-1].append(lit)

assert len(cnf[-1]) == 0
cnf.pop()

def lit_to_str(lit):
    return f"{{atom := {abs(lit)}, negated := {'tt' if lit < 0 else 'ff'}}}"


clause_str = ",\n".join(f"  [{','.join(lit_to_str(lit) for lit in clause)}]"
                      for clause in cnf)

print(f"def sat_formula : formula := [\n{clause_str}\n]")
