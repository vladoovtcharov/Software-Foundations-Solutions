(** * Extraction2: Extracting ML from Coq, Part 2 *)

(* $Date: 2012-05-03 17:52:38 -0400 (Thu, 03 May 2012) $ *)

(** Let's take a look at a slightly fancier way of using Coq's
    extraction facilities.  Instead of translating a functional
    program in Coq into a functional program in OCaml, we'll extract
    the computational content of an interesting _proof_ -- the proof
    that the STLC is normalizing.  The result will be an evaluator
    that takes well-typed STLC terms to their final normal forms.

    Note that this is a slightly unusual way of using Coq.  In the
    words of Adam Chlipala...

        _Many fans of the Curry-Howard correspondence support the idea of
        extracting programs from proofs. In reality, few users of Coq and
        related tools do any such thing. Instead, extraction is better
        thought of as an optimization that reduces the runtime costs of
        expressive typing_. (Chlipala, CPDT)

    However, it's interesting to see that it's possible at all!  (And
    to think about what the extracted program does.) *)

(** * Extracting a Normalizer *)

Require Import Extraction.
Require Import NormInType.

(** The [NormInType] module is a variant of the [Norm] module with a
    few significant differences.  The essential point is that, during
    extraction, everything to do with [Prop] is _erased_.  So, to
    extract a normalizer from a proof of normalization, we need to
    carry out the essential bits of the normalization proof in [Type]
    rather than [Prop].

    [NormInType] also incorporates a copy of the STLC typechecking
    function from the [Typechecking] module and its proof of
    correctness.  (The function itself is no different from before,
    and the correctness proof has just a few small differences because
    of the changes we made to the basic definitions of STLC.)  We need
    these things because the proof of normalization proceeds by
    induction on a typing derivation, so the extracted normalization
    function must be passed a data structure representing a typing
    derivation.  In [normdriver.ml], we obtain this derivation from
    the proof that the typechecking algorithm is sound. *)

Extraction "norm.ml" normalization type_check type_checking_sound.

(** Take a look at [normdriver.ml] to see how this plumbing works in
    detail. 

    Finally, we can compile and execute our normalizer in the same way
    as we did with our evaluator for [Imp].
<<
	ocamlc -w -20 -o normdriver norm.mli norm.ml normdriver.ml
	./normdriver
>>
*)
