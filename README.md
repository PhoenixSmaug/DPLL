# DPLL

This Julia implementation brings to life the renowned [Davis–Putnam–Logemann–Loveland (DPLL) algorithm](https://en.wikipedia.org/wiki/DPLL_algorithm), engineered to address the CNF-SAT problem. The DPLL algorithm is a recursive, backtracking search algorithm for deciding the satisfiability of propositional logic formulas in conjunctive normal form (CNF), serving as a cornerstone for many modern SAT solvers.

The implementation prioritizes both efficiency and readability and includes the following key features:
* DLIS Heuristic: A dynamic heuristic that selects the next variable to assign by preferring the literal that appears in the largest number of remaining clauses.
* Unit Propagation: Simplifies formulas by immediately assigning values to variables that appear in unit clauses.
* Pure Literal Elimination: Removes literals that appear with only one polarity throughout the formula, as they can be assigned in a way that makes all containing clauses true.
* Timeout: Allows the algorithm to exit gracefully if a solution is not found within a specified time frame.

Additionally, an extensive suite of test instances is provided, offering a comprehensive means to evaluate the solver's performance and accuracy. These can be executed via the `runTestInstances()` function.

(c) Mia Muessig
