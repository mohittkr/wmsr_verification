# wmsr_verification
Verification of the W-MSR algorithm for distributed controls

We formally prove the following in Coq:
- Necessary condition for the asymptotic consensus using thw W--MSR algorithm. This development can be found in the file `necessity.v`
- sufficiency condition for the asymptotic consensus using thw W--MSR algorithm. This development can be found in the file `sufficiency.v`
- Proof of the invariant condition can be found in the file `lemma_1.v`
- Proof of the main theorem can be found in the file `F_total_consensus.v`

# Dependencies:

All the developments have been done in Coq 8.17.1 (https://ocaml.org/p/coq/8.17.1). To successfully compile the code, following dependencies are required:
- `mathcomp 1.17.0` 
- `mathcomp-analysis 0.6.4`
- `coquelicot 3.4.0`
- `coq-graph-theory 0.9.2`

These dependencies can be installed through `opam`. For example, to install `mathcomp-analysis`, run `opam install coq-mathcomp-analysis.0.6.4` . To install `mathcomp 1.17.0` install `opam install coq-mathcomp-ssreflect.1.17.0`, to install coquelicot, run `opam install coq-coquelicot`. To install graph theory library, run `opam install coq-graph-theory`.


# Building and installing instructions

To build and install do:
```
make
make install
```

Link to the git repository: https://github.com/mohittkr/wmsr_verification.git. You can clone this repository and follow the build instructions listed above. 


