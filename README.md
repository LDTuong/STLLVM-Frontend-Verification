
# STLLVM Frontend Verification

This thesis project is a conceptual approach to verifying the soundness of an LLVM-frontend for the PLC language Structured Text. It was developed for the Coq proof assistant.

## Structure

Currently, this implementation consists of the following files:

 - `Prelims.v` for any preliminary definitions
 - `ST.v` contains the language formalism of Structured Text
 - `LLVM.v` contains the language formalism of LLVM-IR
 - `Translation.v` provides a model for the frontend translation
 - `Soundness.v` provides the soundness proof


## TODOs

 - Complete proofs for `snd_cngr_wh`and `snd_cngr_rp`lemmata.
 - Extend language fragment
	 - Function calls
	 - Cyclic execution
	 - Bitvector arithmetic
 - Validation suites for language formalism

