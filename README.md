# proof-theoretic-methods
Companion repository for the article
"Proof-theoretic methods in quantifier-free definability", w/ Agda proofs.

## Abstract

We introduce a proof-theoretic method for showing nondefinability of
second-order intuitionistic connectives by quantifier-free schemata.
We apply the method to confirm that Taranovsky's "realizability disjunction"
connective does not admit a quantifier-free definition, and use it to obtain
nuanced information about the nondefinability of Kreisel’s and Polacik’s unary
connectives. The finitary and combinatorial nature of our method makes it more
resilient to changes in metatheory than common semantic approaches, whose
robustness tends to waver once we pass to non-classical and anti-classical
settings. Furthermore, we can easily transcribe the problem-specific subproofs
into univalent type theory and check them using the Agda proof assistant.

## Dependencies

This repository contains the Agda proofs accompanying the article. Running the proofs requires obtaining
[Escardo's Agda implementation of a small type of propositions](https://www.cs.bham.ac.uk/~mhe/impredicativity/),
and placing the files into the repository main directory.

The following files are included:

* `RDisjunction.agda` - All results related to the realizability disjunction connective.
* `KreiselStar.agda` - All results related to Kreisel's star connective and its generalizations.
* `Polacik.agda` - All results related to Połacik's connective and its generalizations.
