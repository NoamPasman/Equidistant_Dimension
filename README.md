# Supplementary Material to "Advances in the Equidistant Dimension of Graphs"

This repository contains programs in `C++` used to verifying computations in [MP26].
All programs require a C++17 compiler and have no external dependencies.

# Results

- The lower bound on $r^*(n)$ given by Proposition 6.18 is tight for all $n<64$. Moreover, if $n\in\{1,3,7,15,63\}$, then the set constructed by Proposition 6.18 is the unique set of maximal size that avoids the banned pattern.
- The sets described in the proof of Lemma 7.9 are indeed distance-equalizing.
- Computational Lemma 7.10 is true.

# Authorship and Acknowledgment

This verification software was developed and validated by Noam Pasman and Kai Mawhinney.
The code was developed with the assistance of ChatGPT and has been checked by the authors, who take full responsibility for its mathematical validity.

# References

[MP26]: Kai Mawhinney and Noam Pasman. Advances in the Equidistant Dimension of Graphs, 2026. In preparation.
