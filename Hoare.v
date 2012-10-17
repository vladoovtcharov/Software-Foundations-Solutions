(** * Hoare: Hoare Logic *)

(* $Date: 2012-05-12 10:20:28 -0400 (Sat, 12 May 2012) $ *)

Require Export Imp.

(** In the past couple of chapters, we've begun applying the
    mathematical tools developed in the first part of the course to
    studying the theory of a small programming language, Imp.

    - We defined a type of _abstract syntax trees_ for Imp, together
      with an _evaluation relation_ (a partial function on states)
      that specifies the _operational semantics_ of programs.

      The language we defined, though small, captures some of the key
      features of full-blown languages like C, C++, and Java,
      including the fundamental notion of mutable state and some
      common control structures.

    - We proved a number of _metatheoretic properties_ -- "meta" in
      the sense that they are properties of the language as a whole,
      rather than properties of particular programs in the language.
      These included:

        - determinism of evaluation

        - equivalence of some different ways of writing down the
          definitions (e.g. functional and relational definitions of
          arithmetic expression evaluation)

        - guaranteed termination of certain classes of programs

        - correctness (in the sense of preserving meaning) of a number
          of useful program transformations

        - behavioral equivalence of programs (in the optional chapter
          [Equiv]).

      If we stopped here, we would still have something useful: a set
      of tools for defining and discussing programming languages and
      language features that are mathematically precise, flexible, and
      easy to work with, applied to a set of key properties.  All of
      these properties are things that language designers, compiler
      writers, and users might care about knowing.  Indeed, many of
      them are so fundamental to our understanding of the programming
      languages we deal with that we might not consciously recognize
      them as "theorems."  But properties that seem intuitively
      obvious can sometimes be quite subtle -- or, in some cases,
      actually even wrong!

      We'll return to this theme later in the course when we discuss
      _types_ and _type soundness_.

    - We saw a couple of examples of _program verification_ -- using
      the precise definition of Imp to prove formally that certain
      particular programs (e.g., factorial and slow subtraction)
      satisfied particular specifications of their behavior. *)

(** In this chapter, we'll take this last idea further.  We'll
    develop a reasoning system called _Floyd-Hoare Logic_ -- commonly
    shortened to just _Hoare Logic_ -- in which each of the syntactic
    constructs of Imp is equipped with a single, generic "proof rule"
    that can be used to reason about programs involving this
    construct.

    Hoare Logic originates in the 1960s, and it continues to be the
    subject of intensive research right up to the present day.  It
    lies at the core of a huge variety of tools that are now being
    used to specify and verify real software systems. *)

  
(* ####################################################### *)
(** * Hoare Logic *)

(** Hoare Logic combines two beautiful ideas: a natural way of
    writing down _specifications_ of programs, and a _compositional
    proof technique_ for proving that these specifications are met --
    where by "compositional" we mean that the structure of proofs
    directly mirrors the structure of the programs that they are
    about. *)

(* ####################################################### *)
(** ** Assertions *)

(** If we're going to talk about specifications of programs, the
    first thing we'll want is a way of making _assertions_ about
    properties that hold at particular points during a program's
    execution -- i.e., properties that may or may not be true of a
    given state of the memory. *)

Definition Assertion := state -> Prop.

(** **** Exercise: 1 star (assertions) *)
(** Paraphrase the following assertions in English.
   1) fun st =>  st X = 3
   2) fun st =>  st X = x
   3) fun st =>  st X <= st Y
   4) fun st =>  st X = 3 \/ st X <= st Y
   5) fun st =>  st Z * st Z <= x /\ ~ (((S (st Z)) * (S (st Z))) <= x)
   6) fun st =>  True
   7) fun st =>  False
*)

(* FILL IN HERE *)
(** [] *)

(** This way of writing assertions is formally correct -- it
    precisely captures what we mean, and it is exactly what we will
    use in Coq proofs.  We'll also want a lighter, less formal
    notation for discussing examples, since this one is a bit
    heavy: (1) every single assertion that we ever write is going to
    begin with [fun st => ]; and (2) this state [st] is the only one that
    we ever use to look up variables (we will never need to talk about
    two different memory states at the same time). So, when writing down
    assertions informally, we'll make some simplifications:
    drop the initial [fun st =>], and write just [X] instead of [st X]. *)
(** Informally, instead of writing
      fun st =>  (st Z) * (st Z) <= x /\ ~ ((S (st Z)) * (S (st Z)) <= x)
    we'll write just
         Z * Z <= x /\ ~((S Z) * (S Z) <= x).
*)

(* ####################################################### *)
(** ** Hoare Triples *)

(** Next, we need a way of specifying -- making claims about -- the
    behavior of commands. *)

(** Since we've defined assertions as a way of making claims about the
    properties of states, and since the behavior of a command is to
    transform one state to another, it is natural to express claims
    about commands in the following way:

      - "If command [c] is started in a state satisfying assertion
        [P], and if [c] eventually terminates, then the final state is
        guaranteed to satisfy the assertion [Q]."

    Such a claim is called a _Hoare Triple_.  The property [P] is
    called the _precondition_ of [c], while [Q] is the _postcondition_
    of [c]. *)
 
Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', 
       c / st || st'  ->
       P st  ->
       Q st'.

(** Since we'll be working a lot with Hoare triples, it's useful to
    have a compact notation:
       {{P}}  c  {{Q}}.
*)
(** (Traditionally, Hoare triples are written [{P} c {Q}], but single
    braces are already used for other things in Coq.)  *)

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.
Open Scope hoare_spec_scope.

(** (The [hoare_spec_scope] annotation here tells Coq that this
    notation is not global but is intended to be used in particular
    contexts.  The [Open Scope] tells Coq that this file is one such
    context.  The first notation -- with missing postcondition -- will
    not actually be used for a while; it's just a placeholder for a
    notation that we'll want to define later, when we discuss
    decorated programs.) *)

(** **** Exercise: 1 star (triples) *)
(** Paraphrase the following Hoare triples in English.  
   1) {{True}} c {{X = 5}}

   2) {{X = x}} c {{X = x + 5)}}

   3) {{X <= Y}} c {{Y <= X}}

   4) {{True}} c {{False}}

   5) {{X = x}} 
      c
      {{Y = real_fact x}}.

   6) {{True}} 
      c 
      {{(Z * Z) <= x /\ ~ (((S Z) * (S Z)) <= x)}}
 *)
(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 1 star (valid_triples) *)
(** Which of the following Hoare triples are _valid_ -- i.e., the
    claimed relation between [P], [c], and [Q] is true?  
   1) {{True}} X ::= 5 {{X = 5}}

   2) {{X = 2}} X ::= X + 1 {{X = 3}}

   3) {{True}} X ::= 5; Y ::= 0 {{X = 5}}

   4) {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}}

   5) {{True}} SKIP {{False}}

   6) {{False}} SKIP {{True}}

   7) {{True}} WHILE True DO SKIP END {{False}}

   8) {{X = 0}} 
      WHILE X == 0 DO X ::= X + 1 END 
      {{X = 1}}

   9) {{X = 1}} 
      WHILE X <> 0 DO X ::= X + 1 END 
      {{X = 100}}
*)
(* FILL IN HERE *)
(** [] *)

(** (Note that we're using informal mathematical notations for
   expressions inside of commands, for readability.  We'll continue
   doing so throughout the chapter.) *)

(** To get us warmed up, here are two simple facts about Hoare
    triples. *)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

(* ####################################################### *) 
(** ** Weakest Preconditions *)

(** Some Hoare triples are more interesting than others.
    For example,
      {{ False }}  X ::= Y + 1  {{ X <= 5 }}
    is _not_ very interesting: it is perfectly valid, but it tells us
    nothing useful.  Since the precondition isn't satisfied by any
    state, it doesn't describe any situations where we can use the
    command [X ::= Y + 1] to achieve the postcondition [X <= 5].

    By contrast, 
      {{ Y <= 4 /\ Z = 0 }}  X ::= Y + 1 {{ X <= 5 }}
    is useful: it tells us that, if we can somehow create a situation
    in which we know that [Y <= 4 /\ Z = 0], then running this command
    will produce a state satisfying the postcondition.  However, this
    triple is still not as useful as it could be, because the [Z = 0]
    clause in the precondition actually has nothing to do with the
    postcondition [X <= 5].  The _most_ useful triple (for a given
    command and postcondition) is this one:
      {{ Y <= 4 }}  X ::= Y + 1  {{ X <= 5 }}
    In other words, [Y <= 4] is the _weakest_ valid precondition of
    the command [X ::= Y + 1] for the postcondition [X <= 5]. *)
 
(** In general, we say that "[P] is the weakest precondition of
    command [c] for postcondition [Q]" if

    - [{{P}} c {{Q}}], and

    - whenever [P'] is an assertion such that [{{P'}} c {{Q}}], we
      have [P' st] implies [P st] for all states [st].  *)

(** That is, [P] is the weakest precondition of [c] for [Q]
    if (a) [P] _is_ a precondition for [Q] and [c], and (b) [P] is the
    _weakest_ (easiest to satisfy) assertion that guarantees [Q] after
    executing [c]. *)

(** The second of the conditions above is essentially a form of
    logical implication at the level of assertions. Because of the
    frequency of its occurrence, it is useful to define a little
    notation: *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

(** We will write [P ~~> Q] (in ASCII, [P ~][~> Q]) for [assert_implies
    P Q]. *)

Notation "P ~~> Q" := (assert_implies P Q) (at level 80).
Notation "P <~~> Q" := (P ~~> Q /\ Q ~~> P) (at level 80).

(** **** Exercise: 1 star (wp) *)
(** What are the weakest preconditions of the following commands
   for the following postconditions?
  1) {{ ? }}  SKIP  {{ X = 5 }}

  2) {{ ? }}  X ::= Y + Z {{ X = 5 }}

  3) {{ ? }}  X ::= Y  {{ X = Y }}

  4) {{ ? }}  
     IFB X == 0 THEN Y ::= Z + 1 ELSE Y ::= W + 2 FI
     {{ Y = 5 }}

  5) {{ ? }}  
     X ::= 5
     {{ X = 0 }}

  6) {{ ? }}  
     WHILE True DO X ::= 0 END
     {{ X = 0 }}
*)
(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, optional (is_wp_formal) *)
(** Weakest preconditions can be defined formally as follows: *)

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (forall st, P' st -> P st).

(** Prove formally using the definition of [hoare_triple] that [Y <= 4]
   is indeed the weakest precondition of [X ::= Y + 1] with respect to
   postcondition [X <= 5]. *)

Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *) 
(** ** Proof Rules *)

(** The goal of Hoare logic is to provide a _compositional_
    method for proving the validity of Hoare triples.  That is, the
    structure of a program's correctness proof should mirror the
    structure of the program itself.  To this end, in the sections
    below, we'll introduce one rule for reasoning about each of the
    different syntactic forms of commands in Imp -- one for
    assignment, one for sequencing, one for conditionals, etc. -- plus
    a couple of "structural" rules that are useful for gluing things
    together. We will prove programs correct using these proof rules,
    without ever unfolding the definition of [hoare_triple]. *)

(* ####################################################### *) 
(** *** Assignment *)

(** The rule for assignment is the most fundamental of the Hoare logic
    proof rules.  Here's how it works.

    Consider this (valid) Hoare triple:
       {{ Y = 1 }}  X ::= Y  {{ X = 1 }}
    In English: if we start out in a state where the value of [Y]
    is [1] and we assign [Y] to [X], then we'll finish in a
    state where [X] is [1].  That is, the property of being equal
    to [1] gets transferred from [Y] to [X].

    Similarly, in
       {{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }}
    the same property (being equal to one) gets transferred to
    [X] from the expression [Y + Z] on the right-hand side of
    the assignment.

    More generally, if [a] is _any_ arithmetic expression, then
       {{ a = 1 }}  X ::= a {{ X = 1 }}
    is a valid Hoare triple. 

    Even more generally, [a] is _any_ arithmetic expression and [Q] is
    _any_ property of numbers, then
       {{ Q(a) }}  X ::= a {{ Q(X) }}
    is a valid Hoare triple.

    Rephrasing this a bit gives us the general Hoare rule for
    assignment:
      {{ Q where a is substituted for X }}  X ::= a  {{ Q }}
    For example, these are valid applications of the assignment
    rule:
      {{ (X <= 5) where X + 1 is substituted for X 
         i.e., X + 1 <= 5 }}  
      X ::= X + 1  
      {{ X <= 5 }}

      {{ (X = 3) where 3 is substituted for X 
         i.e., 3 = 3}}  
      X ::= 3  
      {{ X = 3 }}

      {{ (0 <= X /\ X <= 5) where 3 is substituted for X 
         i.e., (0 <= 3 /\ 3 <= 5)}}  
      X ::= 3  
      {{ 0 <= X /\ X <= 5 }}
*)

(** To formalize the rule, we begin with the notion of "substitution
    in an assertion": *)

Definition assn_sub X a Q : Assertion :=
  fun (st : state) =>
    Q (update st X (aeval st a)).

(** We ask that [Q] holds for the state obtained by assigning [a] to
    [X], i.e. the updated state in which [X] is bound to the result of
    evaluating [a]. Since we've chosen to represent assertions using
    Coq propositions, this is the only way we can "substitute" a
    variable inside an assertion. *)

(** Now the precise proof rule for assignment: 
      ------------------------------ (hoare_asgn)
      {{assn_sub X a Q}} X::=a {{Q}}
*)

Theorem hoare_asgn : forall Q X a,
  {{assn_sub X a Q}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

(** Here's a first formal proof using this rule. *)

Example assn_sub_example : 
  {{assn_sub X (ANum 3) (fun st => st X = 3)}} 
  (X ::= (ANum 3)) 
  {{fun st => st X = 3}}.
Proof.
  apply hoare_asgn.  Qed.

(** **** Exercise: 2 stars (hoare_asgn_examples) *)
(** Translate these informal Hoare triples...
    {{ assn_sub X (X + 1) (X <= 5) }}  X ::= X + 1  {{ X <= 5 }}
    {{ assn_sub X 3 (0 <= X /\ X <= 5) }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}
   ...into formal statements and use [hoare_asgn] to prove them. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars (hoare_asgn_wrong) *)
(** The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems backward to you, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:
      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}
    Give a counterexample showing that this rule is incorrect
    (informally). Hint: The rule universally quantifies over the
    arithmetic expression [a], and your counterexample needs to
    exhibit an [a] for which the rule doesn't work. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, optional (hoare_asgn_fwd) *)
(** However, using an auxiliary variable [x] to remember the original
    value of [X] we can define a Hoare rule for assignment that does,
    intuitively, "work forwards" rather than backwards.
  ------------------------------------------ (hoare_asgn_fwd)
  {{fun st => Q st /\ st X = x}}
    X ::= a
  {{fun st => Q st' /\ st X = aeval st' a }}
  (where st' = update st X x)
    Note that we use the original value of [X] to reconstruct the
    state [st'] before the assignment took place. Prove that this rule
    is correct (the first hypothesis is the functional extensionality
    axiom, which you will need at some point). Also note that this
    rule is more complicated than [hoare_asgn].
*)

Theorem hoare_asgn_fwd :
  (forall {X Y: Type} {f g : X -> Y}, (forall (x: X), f x = g x) ->  f = g) ->
  forall x a Q,
  {{fun st => Q st /\ st X = x}}
    X ::= a
  {{fun st => Q (update st X x) /\ st X = aeval (update st X x) a }}.
Proof.
  intros functional_extensionality v a Q.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (hoare_asgn_weakest) *)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall P X a Q,
  {{P}} (X ::= a) {{Q}} ->
  P ~~> assn_sub X a Q.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *) 
(** *** Consequence *)

(** Sometimes the preconditions and postconditions we get from the
    Hoare rules won't quite be the ones we want in the particular
    situation at hand -- they may be logically equivalent but have a
    different syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker (for
    preconditions) or stronger (for postconditions) than what we need.

    For instance, while
      {{assn_sub X 3 (X = 3)}} X ::= 3 {{X = 3}},
    follows directly from the assignment rule, 
      {{True}} X ::= 3 {{X = 3}}.
    does not.  This triple is also valid, but it is not an instance of
    [hoare_asgn] because [True] and [assn_sub X 3 (X = 3)] are not
    syntactically equal assertions.  However, they are logically
    equivalent, so if one triple is valid, then the other must
    certainly be as well.  We could capture this observation with the
    following rule:
                {{P'}} c {{Q}}
                  P <~~> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}
    Generalizing this line of thought a bit further, if we can derive
    [{{P}} c {{Q}}], it is valid to change [P] to [P'] as long as [P']
    is strong enough to imply [P], and change [Q] to [Q'] as long as
    [Q] implies [Q'].  This observation is captured by two _Rules of
    Consequence_.
                {{P'}} c {{Q}}
                   P ~~> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ~~> Q 
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
*)

(** Here are the formal versions: *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ~~> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st'). 
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ~~> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP. 
  apply Himp.
  apply (Hhoare st st'). 
  assumption. assumption. Qed.

(** For example, we might use the first consequence rule like this:
                {{ True }} =>
                {{ 1 = 1 }} 
    X ::= 1
                {{ X = 1 }}
    Or, formally... 
*)

Example hoare_asgn_example1 :
  {{fun st => True}} (X ::= (ANum 1)) {{fun st => st X = 1}}.
Proof.
  apply hoare_consequence_pre 
    with (P' := assn_sub X (ANum 1) (fun st => st X = 1)).
  apply hoare_asgn. 
  intros st H. reflexivity.  Qed.

(** Finally, for convenience in some proofs, we can state a "combined"
    rule of consequence that allows us to vary both the precondition
    and the postcondition. 
                {{P'}} c {{Q'}}
                   P ~~> P'
                   Q' ~~> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ~~> P' ->
  Q' ~~> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  intros st st' Hc HP.
  apply HQ'Q. apply (Hht st st'). assumption.
  apply HPP'. assumption. Qed.


(* ####################################################### *)
(** *** Digression: The [eapply] Tactic *)

(** This is a good moment to introduce another convenient feature of
    Coq.  We had to write "[with (P' := ...)]" explicitly in the proof
    of [hoare_asgn_example1] above, to make sure that all of the
    metavariables in the premises to the [hoare_consequence_pre] rule
    would be set to specific values; since [P'] doesn't appear in the
    conclusion of [hoare_consequence_pre], the process of unifying the
    conclusion with the current goal doesn't constrain [P'] to a
    specific assertion.

    This is a little annoying, both because the assertion is a bit
    long and also because the very next thing we are going to do --
    applying the [hoare_asgn] rule -- will tell us exactly what it
    should be!  We can use [eapply] instead of [apply] to tell Coq,
    essentially, "Be patient: The missing part is going to be filled
    in soon." *)

Example hoare_asgn_example1' :
  {{fun st => True}} 
  (X ::= (ANum 1)) 
  {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H. reflexivity.  Qed.

(** In general, [eapply H] tactic works just like [apply H]
    except that, instead of failing if unifying the goal with the
    conclusion of [H] does not determine how to instantiate all
    of the variables appearing in the premises of [H], [eapply H]
    will replace these variables with _existential variables_
    (written [?nnn]) as placeholders for expressions that will be
    determined (by further unification) later in the proof. 

    In order for [Qed] to succeed, all existential variables need to
    be determined by the end of the proof. Otherwise Coq will
    (rightfully) refuse to accept the proof. Remember that the Coq
    tactics build proof objects, and proof objects containing
    existential variables are not complete. *)

Lemma silly1 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (forall x y : nat, P x y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. apply HP. Admitted.

(** Coq gives a warning after [apply HP]:
     No more subgoals but non-instantiated existential variables:
     Existential 1 =
     ?171 : [P : nat -> nat -> Prop
             Q : nat -> Prop
             HP : forall x y : nat, P x y
             HQ : forall x y : nat, P x y -> Q x |- nat] 
   Trying to finish the proof with [Qed] instead of [Admitted] gives
   an error:
<<
    Error: Attempt to save a proof with existential variables still
    non-instantiated
>>
*)

(** An additional constraint is that existential variables cannot be
    instantiated with terms containing (normal) variables that did not
    exist at the time the existential variable was created. *)

Lemma silly2 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. destruct HP as [y HP']. Admitted.

(** Doing [apply HP'] above fails with the following error:
     Error: Impossible to unify "?175" with "y".
    In this case there is an easy fix:
    doing [destruct HP] _before_ doing [eapply HQ].
*)

Lemma silly2_fixed : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. apply HP'.
Qed.

(** In the last step we did [apply HP'] which unifies the existential
    variable in the goal with the variable [y]. The [assumption]
    tactic doesn't work in this case, since it cannot handle
    existential variables. However, Coq also provides an [eassumption]
    tactic that solves the goal if one of the premises matches the
    goal up to instantiations of existential variables. We can use
    it instead of [apply HP']. *)

Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.

(** **** Exercise: 2 stars (hoare_asgn_examples_2) *)
(** Translate these informal Hoare triples...
       {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}
       {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}
   ...into formal statements and use [hoare_asgn] and
   [hoare_consequence_pre] to prove them. *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** *** Skip *)

(** Since [SKIP] doesn't change the state, it preserves any
    property P:
      --------------------  (hoare_skip)
      {{ P }} SKIP {{ P }}
*)

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

(* ####################################################### *) 
(** *** Sequencing *)

(** More interestingly, if the command [c1] takes any state where
    [P] holds to a state where [Q] holds, and if [c2] takes any
    state where [Q] holds to one where [R] holds, then doing [c1]
    followed by [c2] will take any state where [P] holds to one
    where [R] holds:
        {{ P }} c1 {{ Q }} 
        {{ Q }} c2 {{ R }}
       ---------------------  (hoare_seq)
       {{ P }} c1;c2 {{ R }}
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

(** Note that, in the formal rule [hoare_seq], the premises are
    given in "backwards" order ([c2] before [c1]).  This matches the
    natural flow of information in many of the situations where we'll
    use the rule: the natural way to construct a Hoare-logic proof is
    to begin at the end of the program (with the final postcondition)
    and push postconditions backwards through commands until we reach
    the beginning. *)

(** Informally, a nice way of recording a proof using the sequencing
    rule is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:
      {{ a = n }}
    X ::= a;
      {{ X = n }}      <---- decoration for Q
    SKIP
      {{ X = n }}
*)

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}} 
  (X ::= a; SKIP) 
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  Case "right part of seq".
    apply hoare_skip.
  Case "left part of seq".
    eapply hoare_consequence_pre. apply hoare_asgn. 
    intros st H. subst. reflexivity. Qed.

(** You will most often use [hoare_seq] and
    [hoare_consequence_pre] in conjunction with the [eapply] tactic,
    as done above. *)

(** **** Exercise: 2 stars (hoare_asgn_example4) *)
(** Translate this decorated program into a formal proof:
                   {{ True }} =>
                   {{ 1 = 1 }}
    X ::= 1;
                   {{ X = 1 }} =>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}
*)

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1); Y ::= (ANum 2)) 
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (swap_exercise) *)
(** Write an Imp program [c] that swaps the values of [X] and [Y]
    and show (in Coq) that it satisfies the following
    specification:
      {{X <= Y}} c {{Y <= X}}
*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, optional (hoarestate1) *)
(** Explain why the following proposition can't be proven:
      forall (a : aexp) (n : nat),
         {{fun st => aeval st a = n}} (X ::= (ANum 3); Y ::= a) 
         {{fun st => st Y = n}}.
*)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *) 
(** *** Conditionals *)

(** What sort of rule do we want for reasoning about conditional
    commands?  Certainly, if the same assertion [Q] holds after
    executing either branch, then it holds after the whole
    conditional.  So we might be tempted to write:
              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      --------------------------------
      {{P}} IFB b THEN c1 ELSE c2 {{Q}}
   However, this is rather weak. For example, using this rule,
   we cannot show that:
     {{True}} 
     IFB X == 0
     THEN Y ::= 2
     ELSE Y ::= X + 1 
     FI
     {{ X <= Y }}
   since the rule tells us nothing about the state in which the
   assignments take place in the "then" and "else" branches.
   
   But, actually, we can say something more precise.  In the "then"
   branch, we know that the boolean expression [b] evaluates to
   [true], and in the "else" branch, we know it evaluates to [false].
   Making this information available in the premises of the rule
   gives us more information to work with when reasoning about the
   behavior of [c1] and [c2] (i.e., the reasons why they establish the
   postcondition [Q]).
              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 
*)

(** To interpret this rule formally, we need to do a little work.

    Strictly speaking, the assertion we've written, [P /\ b], is the
    conjunction of an assertion and a boolean expression, which
    doesn't typecheck.  To fix this, we need a way of formally
    "lifting" any bexp [b] to an assertion.  We'll write [bassn b] for
    the assertion "the boolean expression [b] evaluates to [true] (in
    the given state)." *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

(** A couple of useful facts about [bassn]: *)

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

(** Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst. 
  Case "b is true".
    apply (HTrue st st'). 
      assumption. 
      split. assumption. 
             apply bexp_eval_true. assumption.
  Case "b is false".
    apply (HFalse st st'). 
      assumption. 
      split. assumption.
             apply bexp_eval_false. assumption. Qed.

(** Here is a formal proof that the program we used to motivate the
    rule satisfies the specification we gave. *)

Example if_example : 
    {{fun st => True}} 
  IFB (BEq (AId X) (ANum 0)) 
    THEN (Y ::= (ANum 2)) 
    ELSE (Y ::= APlus (AId X) (ANum 1)) 
  FI
    {{fun st => st X <= st Y}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_if.
  Case "Then".
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, update, assert_implies. simpl. intros st [_ H]. 
    symmetry in H; apply beq_nat_eq in H. 
    rewrite H. omega. 
  Case "Else".
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub, update, assert_implies; simpl; intros st _. omega. 
Qed.

(* ####################################################### *)
(** *** Exercise: One-sided conditionals *)

(** **** Exercise: 4 stars, recommended (if1_hoare) *)

(** In this exercise we consider extending Imp with "one-sided
    conditionals" of the form [IF1 b THEN c FI]. Here [b] is a
    boolean expression, and [c] is a command. If [b] evaluates to
    [true], then command [c] is evaluated. If [b] evaluates to
    [false], then [IF1 b THEN c FI] does nothing.

    We recommend that you do this exercise before the ones that
    follow, as it should help solidify your understanding of the
    material. *)


(** We first extend the syntax of commands, and introduce the usual
    notations. We use a separate module to prevent polluting the
    global name space. *)

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "CIF1" ].

Notation "'SKIP'" := 
  CSkip.
Notation "c1 ; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" := 
  (CAss X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'IF1' b 'THEN' c 'FI'" := 
  (CIf1 b c) (at level 80, right associativity).

(** We now extend the evaluation relation to accommodate [IF1]
    branches. What rule(s) need to be added to [ceval] to evaluate
    one-sided conditionals? *)

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st || st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st || update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st || st' -> c2 / st' || st'' -> (c1 ; c2) / st || st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st || st' ->
                  (WHILE b1 DO c1 END) / st' || st'' ->
                  (WHILE b1 DO c1 END) / st || st''
(* FILL IN HERE *)

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
  (* FILL IN HERE *)
  ].

(** We repeat the definition and notation of Hoare triples. *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', 
       c / st || st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.

(** Now state and prove a theorem, [hoare_if1], that expresses an
    appropriate Hoare logic proof rule for one-sided conditionals. Try
    to come up with a rule that is both sound and as precise as
    possible. *)

(* FILL IN HERE *)

(** For full credit, prove formally that your rule is precise enough
    to show the following valid Hoare triple:
  {{ X + Y = Z }}
  IF1 Y <> 0 THEN
    X ::= X + Y
  FI
  {{ X = Z }}
*)

(** Hint: Your proof of this triple may need to use the other proof
    rules also. Because we're working in a separate module, you'll
    need to copy here the rules you find necessary. *)


Lemma hoare_if1_good :
  {{ fun st => st X + st Y = st Z }}
  IF1 BNot (BEq (AId Y) (ANum 0)) THEN
    X ::= APlus (AId X) (AId Y)
  FI
  {{ fun st => st X = st Z }}.
Proof. (* FILL IN HERE *) Admitted.

End If1.
(** [] *)


(* ####################################################### *)
(** *** Loops *)

(** Finally, we need a rule for reasoning about while loops.  Suppose
    we have a loop
      WHILE b DO c END
    and we want to find a pre-condition [P] and a post-condition
    [Q] such that
      {{P}} WHILE b DO c END {{Q}} 
    is a valid triple. *)

(** First of all, let's think about the case where [b] is false at the
    beginning -- i.e., let's assume that the loop body never executes
    at all.  In this case, the loop behaves like [SKIP], so we might
    be tempted to write
      {{P}} WHILE b DO c END {{P}}.
    But, as we remarked above for the conditional, we know a
    little more at the end -- not just [P], but also the fact
    that [b] is false in the current state.  So we can enrich the
    postcondition a little:
      {{P}} WHILE b DO c END {{P /\ ~b}}
    What about the case where the loop body _does_ get executed?
    In order to ensure that [P] holds when the loop finally
    exits, we certainly need to make sure that the command [c]
    guarantees that [P] holds whenever [c] is finished.
    Moreover, since [P] holds at the beginning of the first
    execution of [c], and since each execution of [c]
    re-establishes [P] when it finishes, we can always assume
    that [P] holds at the beginning of [c].  This leads us to the
    following rule:
                   {{P}} c {{P}}
        -----------------------------------  
        {{P}} WHILE b DO c END {{P /\ ~b}}
    The proposition [P] is called an _invariant_.

    This is almost the rule we want, but again it can be improved a
    little: at the beginning of the loop body, we know not only that
    [P] holds, but also that the guard [b] is true in the current
    state.  This gives us a little more information to use in
    reasoning about [c] (showing that it establishes the invariant by
    the time it finishes).  This gives us the final version of the rule:
               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}
*)




Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction 
     on He, because, in the "keep looping" case, its hypotheses 
     talk about the whole loop instead of just c *)
  remember (WHILE b DO c END) as wcom.
  ceval_cases (induction He) Case; try (inversion Heqwcom); subst.
  
  Case "E_WhileEnd".
    split. assumption. apply bexp_eval_false. assumption.

  Case "E_WhileLoop".
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption. Qed.

Example while_example : 
    {{fun st => st X <= 3}}
  WHILE (BLe (AId X) (ANum 2))
  DO X ::= APlus (AId X) (ANum 1) END
    {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post. 
  apply hoare_while. 
  eapply hoare_consequence_pre. 
  apply hoare_asgn. 
  unfold bassn, assn_sub, assert_implies, update. simpl.
    intros st [H1 H2]. apply ble_nat_true in H2. omega.
  unfold bassn, assert_implies. intros st [Hle Hb]. 
    simpl in Hb. remember (ble_nat (st X) 2) as le. destruct le. 
    apply ex_falso_quodlibet. apply Hb; reflexivity.  
    symmetry in Heqle. apply ble_nat_false in Heqle. omega. 
Qed.

(** We can also use the while rule to prove the following Hoare
    triple, which may seem surprising at first... *)

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof.
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  Case "Loop body preserves invariant".
    apply hoare_post_true. intros st. apply I. 
  Case "Loop invariant and negated guard imply postcondition".
    simpl. intros st [Hinv Hguard].
    apply ex_falso_quodlibet. apply Hguard. reflexivity.
  Case "Precondition implies invariant".
    intros st H. constructor.  Qed.

(** Actually, this result shouldn't be surprising.  If we look back at
    the definition of [hoare_triple], we can see that it asserts
    something meaningful _only_ when the command terminates. *)

Print hoare_triple.

(** If the command doesn't terminate, we can prove anything we like
    about the post-condition.  Here's a more direct proof of the same
    fact: *)

Theorem always_loop_hoare' : forall P Q,
  {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof.  
  unfold hoare_triple. intros P Q st st' contra.
  apply loop_never_stops in contra.  inversion contra. 
Qed.

(** Hoare rules that only talk about terminating commands are often
    said to describe a logic of "partial" correctness.  It is also
    possible to give Hoare rules for "total" correctness, which build
    in the fact that the commands terminate. However, in this course
    we will focus only on partial correctness. *)

(* ####################################################### *)
(** *** Exercise: [REPEAT] *)


Module RepeatExercise.

(** **** Exercise: 4 stars (hoare_repeat) *)
(** In this exercise, we'll add a new command to our language of
    commands: [REPEAT] c [UNTIL] a [END]. You will write the
    evaluation rule for [repeat] and add a new Hoare rule to
    the language for programs involving it. *)

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [REPEAT] behaves like [WHILE], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "CRepeat" ].

Notation "'SKIP'" := 
  CSkip.
Notation "c1 ; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" := 
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" := 
  (CRepeat e1 b2) (at level 80, right associativity).

(** Add new rules for [REPEAT] to [ceval] below.  You can use the rules
    for [WHILE] as a guide, but remember that the body of a [REPEAT]
    should always execute at least once, and that the loop ends when
    the guard becomes true.  Then update the [ceval_cases] tactic to
    handle these added cases.  *)

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass  : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
(* FILL IN HERE *)
.

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" 
(* FILL IN HERE *)
].

(** A couple of definitions from above, copied here so they use the
    new [ceval]. *)

Notation "c1 '/' st '||' st'" := (ceval st c1 st') 
                                 (at level 40, st at level 39).

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) 
                        : Prop :=
  forall st st', (c / st || st') -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

(** To make sure you've got the evaluation rules for [REPEAT] right,
    prove that [ex1_repeat evaluates correctly. *)

Definition ex1_repeat :=
  REPEAT
    X ::= ANum 1;
    Y ::= APlus (AId Y) (ANum 1)
  UNTIL (BEq (AId X) (ANum 1)) END.

Theorem ex1_repeat_works :
  ex1_repeat / empty_state || update (update empty_state X 1) Y 1.
Proof.
  (* FILL IN HERE *) Admitted.

(** Now state and prove a theorem, [hoare_repeat], that expresses an
    appropriate proof rule for [repeat] commands.  Use [hoare_while]
    as a model, and try to make your rule as precise as possible. *)

(* FILL IN HERE *)

(** For full credit, make sure (informally) that your rule can be used
    to prove the following _valid_ Hoare triple:
  {{ X > 0 }}
  REPEAT
    Y ::= X;
    X ::= X - 1
  UNTIL X = 0 END
  {{ X = 0 /\ Y > 0 }}
*)


End RepeatExercise.
(** [] *)

(* ####################################################### *)
(** ** Exercise: [HAVOC] *)

(** **** Exercise: 3 stars (himp_hoare) *)

(** In this exercise, we will derive proof rules for the [HAVOC] command
    which we studied in the last chapter. First, we enclose this work
    in a separate module, and recall the syntax and big-step semantics
    of Himp commands. *)

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "HAVOC" ].

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' X" := (CHavoc X) (at level 60).

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st || st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st || update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st || st' -> c2 / st' || st'' -> (c1 ; c2) / st || st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st || st' ->
                  (WHILE b1 DO c1 END) / st' || st'' ->
                  (WHILE b1 DO c1 END) / st || st''
  | E_Havoc : forall (st : state) (X : id) (n : nat),
              (HAVOC X) / st || update st X n

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
  | Case_aux c "E_Havoc" ].

(** The definition of Hoare triples is exactly as before. Unlike our
    notion of equivalence, which had subtle consequences with
    occassionally nonterminating commands (exercise [havoc_diverge]),
    this definition is still fully satisfactory. Convince yourself of
    this before proceeding. *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', c / st || st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.

(** Complete the Hoare rule for [HAVOC] commands below by defining
    [havoc_pre] and prove that the resulting rule is correct. *)

Definition havoc_pre (X : id) (Q : Assertion) : Assertion :=
(* FILL IN HERE *) admit.

Theorem hoare_havoc : forall (Q : Assertion) (X : id),
  {{ havoc_pre X Q }} HAVOC X {{ Q }}.
Proof.
  (* FILL IN HERE *) Admitted.

(** Like in the [hoare_asgn_weakest] exercise above, show that your
    [havoc_pre] returns the weakest precondition. *)

Lemma hoare_havoc_weakest : forall (P Q : Assertion) (X : id),
  {{ P }} HAVOC X {{ Q }} ->
  P ~~> havoc_pre X Q.
Proof.
(* FILL IN HERE *) Admitted.

(* /SOLUTION *)
End Himp.
(** [] *)


(* ####################################################### *)
(** * Review of Hoare Logic *)

(** Above, we've introduced Hoare Logic as a tool to reasoning
    about Imp programs. In the reminder of this chapter we will
    explore a systematic way to use Hoare Logic to prove properties
    about programs. The rules of Hoare Logic are the following: *)

(**
             ------------------------------ (hoare_asgn)
             {{assn_sub X a Q}} X::=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} SKIP {{ P }}

               {{ P }} c1 {{ Q }} 
               {{ Q }} c2 {{ R }}
              ---------------------  (hoare_seq)
              {{ P }} c1;c2 {{ R }}

              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}

                {{P'}} c {{Q'}}
                   P ~~> P'
                   Q' ~~> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)


(* ####################################################### *)
(** * Decorated Programs *)

(** The beauty of Hoare Logic is that it is _compositional_ -- the
    structure of proofs exactly follows the structure of programs.
    This fact suggests that we could record the essential ideas of
    a proof informally (leaving out some low-level calculational
    details) by decorating programs with appropriate assertions around
    each statement.  Such a _decorated program_ carries with it
    an (informal) proof of its own correctness. *)

(** For example, here is a complete decorated program: *)
(**
      {{ True }} =>
      {{ x = x }}
    X ::= x; 
      {{ X = x }} => 
      {{ X = x /\ z = z }}
    Z ::= z;              
      {{ X = x /\ Z = z }} =>
      {{ Z - X = z - x }}
    WHILE X <> 0 DO
        {{ Z - X = z - x /\ X <> 0 }} =>
        {{ (Z - 1) - (X - 1) = z - x }}
      Z ::= Z - 1;               
        {{ Z - (X - 1) = z - x }}
      X ::= X - 1 
        {{ Z - X = z - x }} 
    END;
      {{ Z - X = z - x /\ ~ (X <> 0) }} =>
      {{ Z = z - x }} =>
      {{ Z + 1 = z - x + 1 }}
    Z ::= Z + 1
      {{ Z = z - x + 1 }}
*)

(** Concretely, a decorated program consists of the program text
    interleaved with assertions.  To check that a decorated program
    represents a valid proof, we check that each individual command is
    _locally_ consistent with its accompanying assertions in the
    following sense: *)

(** 
    - [SKIP] is locally consistent if its precondition and
      postcondition are the same:
          {{ P }} 
          SKIP
          {{ P }} 
    - The sequential composition of commands [c1] and [c2] is locally
      consistent (with respect to assertions [P] and [R]) if [c1] is
      locally consistent (with respect to [P] and [Q]) and [c2] is
      locally consistent (with respect to [Q] and [R]):
          {{ P }} 
          c1;
          {{ Q }} 
          c2
          {{ R }}

    - An assignment is locally consistent if its precondition is
      the appropriate substitution of its postcondition:
          {{ P where a is substituted for X }}  
          X ::= a  
          {{ P }}
    - A conditional is locally consistent (with respect to assertions
      [P] and [Q]) if the assertions at the top of its "then" and
      "else" branches are exactly [P/\b] and [P/\~b] and if its "then"
      branch is locally consistent (with respect to [P/\b] and [Q])
      and its "else" branch is locally consistent (with respect to
      [P/\~b] and [Q]):
          {{ P }} 
          IFB b THEN
            {{ P /\ b }} 
            c1 
            {{ Q }}
          ELSE
            {{ P /\ ~b }} 
            c2
            {{ Q }}
          FI
          {{ Q }}

    - A while loop is locally consistent if its postcondition is
      [P/\~b] (where [P] is its precondition) and if the pre- and
      postconditions of its body are exactly [P/\b] and [P]:
          {{ P }} 
          WHILE b DO
            {{ P /\ b }} 
            c1 
            {{ P }}
          END
          {{ P /\ ~b }} 

    - A pair of assertions separated by [=>] is locally consistent if
      the first implies the second (in all states):
          {{ P }} =>
          {{ P' }} 

      This corresponds to the application of [hoare_consequence] and
      is the only place in a decorated program where checking if the
      decorations are correct is not fully mechanical and syntactic,
      but it involves logical and maybe arithmetic reasoning.
*)

(* ####################################################### *)
(** * Sample Hoare Logic Proofs *)


(* ####################################################### *)
(** ** Example: Slow Subtraction *)

(** We've seen an Imp program for subtracting one number from another by 
    repeatedly subtracting one from each number until the one being 
    subtracted reaches zero.

    Here is a full proof -- presented as a decorated program -- that this 
    program meets a natural specification:
    (1)      {{ X = x /\ Z = z }} =>                      
    (2)      {{ Z - X = z - x }}                      
           WHILE X <> 0 DO                            
    (3)        {{ Z - X = z - x /\ X <> 0 }} =>       
    (4)        {{ (Z - 1) - (X - 1) = z - x }}        
             Z ::= Z - 1;
    (5)        {{ Z - (X - 1) = z - x }}              
             X ::= X - 1
    (6)        {{ Z - X = z - x }}                    
           END
    (7)      {{ Z - X = z - x /\ ~ (X <> 0) }} =>     
    (8)      {{ Z = z - x }}                          
    The decorations were constructed as follows:
      - Begin with the undecorated program (the unnumbered lines).
      - Add the specification -- i.e., the outer precondition (1) and
        postcondition (8).
      - Write down the invariant of the loop (6).
      - Following the format dictated by the [hoare_while] rule, add
        the final use of the rule of consequence -- the assertion in
        line (7) and the check that (7) implies (8).
      - Check that the loop invariant _is_ an invariant of the loop
        body by using the assignment rule twice to push the invariant
        backwards from the end of the loop body to the
        beginning (line (5) and then line (4)), and then filling in
        the rule of consequence asserting that the invariant plus the
        fact that the loop guard is true (line (3)) implies line (4).
      - Check that the invariant is established at the beginning of
        the loop verifying that line (2) is implied by line (1).

    As in most Hoare Logic proofs, the only challenging part of this
    process is finding the right loop invariant.  There is no
    foolproof procedure for this, but a helpful heuristic is to begin
    by assumimng that the loop invariant is exactly the desired
    postcondition (i.e., that lines (6) and (8) are the same) and then
    calculating a bit to find out why this assertion is _not_ an
    invariant of the loop body.  

    In this case, it quickly becomes clear that assertion (8) is not
    an invariant of the loop body because the loop body changes the
    variable [Z], but (obviously) not the global constants [x] and
    [z].  So we need to generalize (8) to some statement that is
    equivalent to (8) when [X] is [0], since this will be the case
    when the loop terminates, and that "fills the gap" in some
    appropriate way when [X] is nonzero. *)

(** From this informal proof, it is now easy to read off a formal
    proof in terms of the Hoare rules: *)

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Z ::= AMinus (AId Z) (ANum 1);
    X ::= AMinus (AId X) (ANum 1)
  END.

Definition subtract_slowly_invariant x z := 
  fun st => minus (st Z) (st X) = minus z x.

Theorem subtract_slowly_correct : forall x z,
  {{fun st => st X = x /\ st Z = z}} 
  subtract_slowly 
  {{fun st => st Z = minus z x}}.
Proof.
  (* Note that we do NOT unfold the definition of hoare_triple
     anywhere in this proof!  The goal is to use only the Hoare
     rules. Your proofs should do the same. *)

  intros x z. unfold subtract_slowly.
  (* First we need to transform the pre and postconditions so
     that hoare_while will apply.  In particular, the
     precondition should be the loop invariant. *)
  eapply hoare_consequence with (P' := subtract_slowly_invariant x z).
  apply hoare_while.

  Case "Loop body preserves invariant".
    (* Split up the two assignments with hoare_seq - using eapply 
       lets us solve the second one immediately with hoare_asgn *)
    eapply hoare_seq. apply hoare_asgn.
    (* Now for the first assignment, transform the precondition
       so we can use hoare_asgn *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    (* Finally, we need to justify the implication generated by
       hoare_consequence_pre (this bit of reasoning is elided in the
       informal proof) *)
    unfold subtract_slowly_invariant, assn_sub, update, bassn. simpl.
    intros st [Inv GuardTrue].
    (* Could alternatively do case analysis on 
        negb (beq_nat (st X) 0) here;
        but SearchAbout reveals some nice lemmas *)
    SearchAbout [negb true]. rewrite negb_true_iff in GuardTrue.
    SearchAbout [beq_nat false]. apply beq_nat_false in GuardTrue.
    omega. (* slow but effective! *)
    (* Faster variant: rewrite <- Inv. clear Inv. omega. *)
  Case "Initial state satisfies invariant".
    (* This is the subgoal generated by the precondition part of our
       first use of hoare_consequence.  It's the first implication
       written in the decorated program (though we elided the actual
       proof there). *)
    unfold subtract_slowly_invariant.
    intros st [HX HZ]. omega.  
  Case "Invariant and negated guard imply postcondition".
   (* This is the subgoal generated by the postcondition part of
      out first use of hoare_consequence.  This implication is
      the one written after the while loop in the informal proof. *)
    intros st [Inv GuardFalse].
    unfold subtract_slowly_invariant in Inv.
    unfold bassn in GuardFalse. simpl in GuardFalse.
    (* SearchAbout helps again to find the right lemmas *)
    SearchAbout [not true]. rewrite not_true_iff_false in GuardFalse. 
    SearchAbout [negb false]. rewrite negb_false_iff in GuardFalse.
    SearchAbout [beq_nat true]. apply beq_nat_true in GuardFalse.
    omega. Qed.

(* ####################################################### *)
(** ** Exercise: Reduce to Zero *)

(** **** Exercise: 2 stars (reduce_to_zero_correct) *)
(** Here is a while loop that is so simple it needs no invariant: 
          {{ True }}
        WHILE X <> 0 DO
            {{ True /\ X <> 0 }} =>
            {{ True }}
          X ::= X - 1
            {{ True }}
        END
          {{ True /\ X = 0 }} =>
          {{ X = 0 }}
   Your job is to translate this proof to Coq.  Refer to the
   [slow_subtraction] example for ideas.
*)

Definition reduce_to_zero : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem reduce_to_zero_correct : 
  {{fun st => True}}
  reduce_to_zero
  {{fun st => st X = 0}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *)
(** ** Exercise: Slow Addition *)

(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z. *)

Definition add_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Z ::= APlus (AId Z) (ANum 1);
    X ::= AMinus (AId X) (ANum 1)
  END.

(** **** Exercise: 3 stars (add_slowly_decoration) *)
(** Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars (add_slowly_formal) *)
(** Now write down your specification of [add_slowly] formally, as a
    Coq [Hoare_triple], and prove it valid. *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** ** Example: Parity *)

(** Here's another, slightly trickier example.  Make sure you
    understand the decorated program completely.  You may find it
    instructive to start with the bare program and try to fill in the
    decorations yourself.  Notice exactly where the condition [X<=x]
    comes up. *)
(** 
    {{ X = x }} =>
    {{ X = x /\ 0 = 0 }}
  Y ::= 0;
    {{ X = x /\ Y = 0 }} =>
    {{ (Y=0 <-> ev (x-X)) /\ X<=x }} 
  WHILE X <> 0 DO
      {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ X<>0 }} =>
      {{ (1-Y)=0 <-> ev (x-(X-1)) /\ X-1<=x }} 
    Y ::= 1 - Y;
      {{ Y=0 <-> ev (x-(X-1)) /\ X-1<=x }} 
    X ::= X - 1
      {{ Y=0 <-> ev (x-X) /\ X<=x }} 
  END
    {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ ~(X<>0) }} =>
    {{ Y=0 <-> ev x }}
*)

(** And here is the formal version of this proof.  Skim them,
    but you do not need to understand every detail (though the details
    are not actually very hard), since all the important ideas are
    already in the informal version. *)

Definition find_parity : com :=
  Y ::= (ANum 0);
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    Y ::= AMinus (ANum 1) (AId Y);
    X ::= AMinus (AId X) (ANum 1)
  END.

Definition find_parity_invariant x := 
  fun st => 
     st X <= x /\ ((st Y = 0 /\ ev (x - st X))
                    \/ (st Y = 1 /\ ~ev (x - st X))). 

(** We'll need the following lemma... *)

Lemma not_ev_ev_S_gen: forall n,
  (~ ev n -> ev (S n)) /\
  (~ ev (S n) -> ev (S (S n))).
Proof.
  induction n as [| n'].
  Case "n = 0".
    split; intros H.
    SCase "->".
      apply ex_falso_quodlibet. apply H. apply ev_0.
    SCase "<-".
      apply ev_SS. apply ev_0.
  Case "n = S n'".
    inversion IHn' as [Hn HSn]. split; intros H.
    SCase "->".
      apply HSn. apply H.
    SCase "<-".
      apply ev_SS. apply Hn. intros contra. 
      apply H. apply ev_SS. apply contra.  Qed.

Lemma not_ev_ev_S : forall n,
  ~ ev n -> ev (S n).
Proof.
  intros n.
  destruct (not_ev_ev_S_gen n) as [H _].
  apply H.
Qed.

Theorem find_parity_correct : forall x,
  {{fun st => st X = x}} 
  find_parity
  {{fun st => st Y = 0 <-> ev x}}.
Proof.
  intros x. unfold find_parity.
  apply hoare_seq with (Q := find_parity_invariant x).
  eapply hoare_consequence.
  apply hoare_while with (P := find_parity_invariant x).
  Case "Loop body preserves invariant".
    eapply hoare_seq.
    apply hoare_asgn.
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    intros st [[Inv1 Inv2] GuardTrue].
    unfold find_parity_invariant, bassn, assn_sub, aeval in *.
    rewrite update_eq.
    rewrite (update_neq Y X). 
    rewrite (update_neq X Y).
    rewrite update_eq.
    simpl in GuardTrue. destruct (st X). 
      inversion GuardTrue. simpl.
    split. omega. 
    inversion Inv2 as [[H1 H2] | [H1 H2]]; rewrite H1;
                     [right|left]; (split; simpl; [omega |]).
    apply ev_not_ev_S in H2. 
    replace (S (x - S n)) with (x-n) in H2 by omega.
    rewrite <- minus_n_O. assumption.
    apply not_ev_ev_S in H2.
    replace (S (x - S n)) with (x - n) in H2 by omega.
    rewrite <- minus_n_O. assumption.
    reflexivity. reflexivity.
  Case "Precondition implies invariant".
    intros st H. assumption.
  Case "Invariant implies postcondition".
    unfold bassn, find_parity_invariant. simpl.
    intros st [[Inv1 Inv2] GuardFalse].
    destruct (st X).
      split; intro.   
        inversion Inv2.  
           inversion H0 as [_ H1]. replace (x-0) with x in H1 by omega. 
           assumption.
           inversion H0 as [H0' _]. rewrite H in H0'. inversion H0'. 
        inversion Inv2. 
           inversion H0. assumption. 
           inversion H0 as [_ H1]. replace (x-0) with x in H1 by omega. 
           apply ex_falso_quodlibet. apply H1. assumption.
      apply ex_falso_quodlibet. apply GuardFalse. reflexivity.
  Case "invariant established before loop".
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    intros st H.
    unfold assn_sub, find_parity_invariant, update. simpl.
    subst. 
    split.
    omega. 
    replace (st X - st X) with 0 by omega. 
    left. split. reflexivity.
    apply ev_0.  Qed.

(** **** Exercise: 2 stars (wrong_find_parity_invariant) *)
(** A plausible first attempt at stating an invariant for [find_parity]
    is the following. *)

Definition find_parity_invariant' x := 
  fun st => 
    (st Y) = 0 <-> ev (x - st X). 

(** Why doesn't this work?  (Hint: Don't waste time trying to answer
    this exercise by attempting a formal proof and seeing where it
    goes wrong.  Just think about whether the loop body actually
    preserves the property.) *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *) 
(** ** Example: Finding Square Roots *)

(** Here's another example, starting with the formal version this
    time. *)

Definition sqrt_loop : com :=
  WHILE BLe (AMult (APlus (ANum 1) (AId Z)) 
                   (APlus (ANum 1) (AId Z))) 
            (AId X) DO
    Z ::= APlus (ANum 1) (AId Z)
  END.

Definition sqrt_com : com :=
  Z ::= ANum 0;
  sqrt_loop.

Definition sqrt_spec (x : nat) : Assertion := 
  fun st => 
       ((st Z) * (st Z)) <= x 
    /\ ~ (((S (st Z)) * (S (st Z))) <= x).

Definition sqrt_inv (x : nat) : Assertion :=
  fun st => 
       st X = x
    /\ ((st Z) * (st Z)) <= x.

Theorem random_fact_1 : forall st,
     (S (st Z)) * (S (st Z)) <= st X ->
     bassn (BLe (AMult (APlus (ANum 1) (AId Z)) 
                       (APlus (ANum 1) (AId Z))) 
                (AId X)) st.
Proof.
  intros st Hle.  unfold bassn. simpl.
  destruct (st X) as [|x'].
  Case "st X = 0".
    inversion Hle.
  Case "st X = S x'".
    simpl in Hle. apply le_S_n in Hle.
    remember (ble_nat (plus (st Z) 
                      ((st Z) * (S (st Z)))) x')
      as ble.
    destruct ble. reflexivity. 
    symmetry in Heqble. apply ble_nat_false in Heqble.
    unfold not in Heqble. apply Heqble in Hle. inversion Hle.
Qed.

Theorem random_fact_2 : forall st,
     bassn (BLe (AMult (APlus (ANum 1) (AId Z)) 
                       (APlus (ANum 1) (AId Z))) 
                (AId X)) st ->
       aeval st (APlus (ANum 1) (AId Z))
     * aeval st (APlus (ANum 1) (AId Z))
     <= st X.
Proof.
  intros st Hble. unfold bassn in Hble. simpl in *.
  destruct (st X) as [| x'].
  Case "st X = 0".
    inversion Hble.
  Case "st X = S x'".
    apply ble_nat_true in Hble. omega. Qed.

Theorem sqrt_com_correct : forall x,
  {{fun st => True}} (X ::= ANum x; sqrt_com) {{sqrt_spec x}}.
Proof.
  intros x.
  apply hoare_seq with (Q := fun st => st X = x).
  Case "sqrt_com".
    unfold sqrt_com.
    apply hoare_seq with (Q := fun st => st X = x 
                                      /\ st Z = 0).
    SCase "sqrt_loop".
      unfold sqrt_loop.
      eapply hoare_consequence.
      apply hoare_while with (P := sqrt_inv x).

      SSCase "loop preserves invariant".
        eapply hoare_consequence_pre.
        apply hoare_asgn. intros st H.
        unfold assn_sub. unfold sqrt_inv in *.
        inversion H as [[HX HZ] HP]. split.
        SSSCase "X is preserved".
          rewrite update_neq; try assumption; try reflexivity.
        SSSCase "Z is updated correctly".
          rewrite (update_eq (aeval st (APlus (ANum 1) (AId Z))) Z st).
          subst. apply random_fact_2. assumption.

      SSCase "invariant is true initially".
        intros st H. inversion H as [HX HZ]. 
        unfold sqrt_inv. split. assumption. 
        rewrite HZ. simpl. omega.

      SSCase "after loop, spec is satisfied".
        intros st H. unfold sqrt_spec.
        inversion H as [HX HP].
        unfold sqrt_inv in HX.  inversion HX as [HX' Harith].
        split. assumption. 
        intros contra. apply HP. clear HP. 
        simpl. simpl in contra.
        apply random_fact_1. subst x. assumption.

    SCase "Z set to 0".
      eapply hoare_consequence_pre. apply hoare_asgn. 
      intros st HX.
      unfold assn_sub. split.
      rewrite update_neq. assumption. reflexivity.
      rewrite update_eq. reflexivity.

  Case "assignment of X".
    eapply hoare_consequence_pre. apply hoare_asgn. 
    intros st H.
    unfold assn_sub. rewrite update_eq. reflexivity. Qed.

(** **** Exercise: 3 stars (sqrt_informal) *)
(** Write an informal decorated program corresponding to this formal
    correctness proof. *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** ** Exercise: Factorial *)

Module Factorial.

(** Recall the mathematical factorial function... *)

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(** ... and the Imp program that we wrote to calculate factorials: *)

Definition fact_body : com :=
  Y ::= AMult (AId Y) (AId Z);
  Z ::= AMinus (AId Z) (ANum 1).

Definition fact_loop : com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    fact_body
  END.

Definition fact_com : com :=
  Z ::= (AId X);
  Y ::= ANum 1;
  fact_loop.

(** **** Exercise: 3 stars, optional (fact_informal) *)
(** Decorate the [fact_com] program to show that it satisfies the
    specification given by the pre and postconditions below.  As
    usual, feel free to elide the algebraic reasoning about
    arithmetic, the less-than relation, etc., that is formally
    required by the rule of consequence:

(* FILL IN HERE *)
    {{ X = x }}
  Z ::= X;
  Y ::= 1;
  WHILE Z <> 0 DO
    Y ::= Y * Z;
    Z ::= Z - 1
  END
    {{ Y = real_fact x }}
*)
(** [] *)


(** **** Exercise: 4 stars, optional (fact_formal) *)
(** Prove formally that fact_com satisfies this specification,
    using your informal proof as a guide.  You may want to state
    the loop invariant separately (as we did in the examples). *)

Theorem fact_com_correct : forall x,
  {{fun st => st X = x}} fact_com
  {{fun st => st Y = real_fact x}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End Factorial.

(* ####################################################### *)
(** * Formalizing Decorated Programs (Optional) *)

(** The informal conventions for decorated programs amount to a way of
    displaying Hoare triples in which commands are annotated with
    enough embedded assertions that checking the validity of the
    triple is reduced to simple logical and algebraic calculations
    showing that some assertions imply others.

    In this optional section, we show that this informal presentation
    style can actually be made completely formal.  *)

(** ** Syntax *)

(** The first thing we need to do is to formalize a variant of the
    syntax of commands with embedded assertions.  We call the new
    commands _decorated commands_, or [dcom]s. *)

Inductive dcom : Type :=
  | DCSkip :  Assertion -> dcom
  | DCSeq : dcom -> dcom -> dcom
  | DCAsgn : id -> aexp ->  Assertion -> dcom
  | DCIf : bexp ->  Assertion -> dcom ->  Assertion -> dcom
           -> Assertion-> dcom
  | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
  | DCPre : Assertion -> dcom -> dcom
  | DCPost : dcom -> Assertion -> dcom.

Tactic Notation "dcom_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Skip" | Case_aux c "Seq" | Case_aux c "Asgn"
  | Case_aux c "If" | Case_aux c "While"
  | Case_aux c "Pre" | Case_aux c "Post" ].

Notation "'SKIP' {{ P }}" 
      := (DCSkip P) 
      (at level 10) : dcom_scope.
Notation "l '::=' a {{ P }}" 
      := (DCAsgn l a P) 
      (at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}" 
      := (DCWhile b Pbody d Ppost) 
      (at level 80, right associativity) : dcom_scope.
Notation "'IFB' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI' {{ Q }}" 
      := (DCIf b P d P' d' Q) 
      (at level 80, right associativity)  : dcom_scope.
Notation "'=>' {{ P }} d" 
      := (DCPre P d) 
      (at level 90, right associativity)  : dcom_scope.
Notation "{{ P }} d" 
      := (DCPre P d) 
      (at level 90)  : dcom_scope.
Notation "d '=>' {{ P }}" 
      := (DCPost d P) 
      (at level 91, right associativity)  : dcom_scope.
Notation " d ; d' " 
      := (DCSeq d d') 
      (at level 80, right associativity)  : dcom_scope.

Delimit Scope dcom_scope with dcom.

(** To avoid clashing with the existing [Notation] definitions
    for ordinary [com]mands, we introduce these notations in a special
    scope called [dcom_scope], and we wrap examples with the
    declaration [% dcom] to signal that we want the notations to be
    interpreted in this scope.  

    Careful readers will note that we've defined two notations for the
    [DCPre] constructor, one with and one without a [=>].  The
    "without" version is intended to be used to supply the initial
    precondition at the very top of the program. *)

Example dec_while : dcom := (
  {{ fun st => True }}
  WHILE (BNot (BEq (AId X) (ANum 0))) 
  DO
    {{ fun st => True /\ bassn (BNot (BEq (AId X) (ANum 0))) st}}
    X ::= (AMinus (AId X) (ANum 1)) 
    {{ fun _ => True }}
  END
  {{ fun st => True /\ ~bassn (BNot (BEq (AId X) (ANum 0))) st}} =>
  {{ fun st => st X = 0 }}
) % dcom.

(** It is easy to go from a [dcom] to a [com] by erasing all
    annotations. *)

Fixpoint extract (d:dcom) : com :=
  match d with
  | DCSkip _           => SKIP
  | DCSeq d1 d2        => (extract d1 ; extract d2) 
  | DCAsgn X a _       => X ::= a
  | DCIf b _ d1 _ d2 _ => IFB b THEN extract d1 ELSE extract d2 FI
  | DCWhile b _ d _    => WHILE b DO extract d END
  | DCPre _ d          => extract d
  | DCPost d _         => extract d
  end.

(** The choice of exactly where to put assertions in the definition of
    [dcom] is a bit subtle.  The simplest thing to do would be to
    annotate every [dcom] with a precondition and postcondition.  But
    this would result in very verbose programs with a lot of repeated
    annotations: for example, a program like [SKIP;SKIP] would have to
    be annotated as
        {{P}} ({{P}} SKIP {{P}}) ; ({{P}} SKIP {{P}}) {{P}},
    with pre- and post-conditions on each [SKIP], plus identical pre-
    and post-conditions on the semicolon!  

    Instead, the rule we've followed is this:

       - The _post_-condition expected by each [dcom] [d] is embedded in [d]

       - The _pre_-condition is supplied by the context. *)

(** In other words, the invariant of the representation is that a
    [dcom] [d] together with a precondition [P] determines a Hoare
    triple [{{P}} (extract d) {{post d}}], where [post] is defined as
    follows: *)

Fixpoint post (d:dcom) : Assertion :=
  match d with
  | DCSkip P                => P
  | DCSeq d1 d2             => post d2
  | DCAsgn X a Q            => Q
  | DCIf  _ _ d1 _ d2 Q     => Q
  | DCWhile b Pbody c Ppost => Ppost
  | DCPre _ d               => post d
  | DCPost c Q              => Q
  end.

(** We can define a similar function that extracts the "initial
    precondition" from a decorated program. *)

Fixpoint pre (d:dcom) : Assertion :=
  match d with
  | DCSkip P                => fun st => True
  | DCSeq c1 c2             => pre c1
  | DCAsgn X a Q            => fun st => True
  | DCIf  _ _ t _ e _       => fun st => True
  | DCWhile b Pbody c Ppost => fun st => True
  | DCPre P c               => P
  | DCPost c Q              => pre c
  end.

(** This function is not doing anything sophisticated like calculating
    a weakest precondition; it just recursively searches for an
    explicit annotation at the very beginning of the program,
    returning default answers for programs that lack an explicit
    precondition (like a bare assignment or [SKIP]).  

    Using [pre] and [post], and assuming that we adopt the convention
    of always supplying an explicit precondition annotation at the
    very beginning of our decorated programs, we can express what it
    means for a decorated program to be correct as follows: *)

Definition dec_correct (d:dcom) := 
  {{pre d}} (extract d) {{post d}}.

(** To check whether this Hoare triple is _valid_, we need a way to
    extract the "proof obligations" from a decorated program.  These
    obligations are often called _verification conditions_, because
    they are the facts that must be verified to see that the
    decorations are logically consistent and thus add up to a complete
    proof of correctness. *)

(** ** Extracting Verification Conditions *)

(** The function [verification_conditions] takes a [dcom] [d] together
    with a precondition [P] and returns a _proposition_ that, if it
    can be proved, implies that the triple [{{P}} (extract d) {{post d}}]
    is valid.  It does this by walking over [d] and generating a big
    conjunction including all the "local checks" that we listed when
    we described the informal rules for decorated programs.
    (Strictly speaking, we need to massage the informal rules a little
    bit to add some uses of the rule of consequence, but the
    correspondence should be clear.) *)

Fixpoint verification_conditions (P : Assertion) (d:dcom) : Prop :=
  match d with
  | DCSkip Q          => 
      (P ~~> Q)
  | DCSeq d1 d2      => 
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q      => 
      (P ~~> assn_sub X a Q)
  | DCIf b P1 d1 P2 d2 Q => 
      ((fun st => P st /\ bassn b st) ~~> P1)
      /\ ((fun st => P st /\ ~ (bassn b st)) ~~> P2)
      /\ (Q = post d1) /\ (Q = post d2)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost      => 
      (* post d is the loop invariant and the initial precondition *)
      (P ~~> post d)  
      /\ (Pbody = (fun st => post d st /\ bassn b st))
      /\ (Ppost = (fun st => post d st /\ ~(bassn b st)))
      /\ verification_conditions Pbody d
  | DCPre P' d         => 
      (P ~~> P') /\ verification_conditions P' d
  | DCPost d Q        => 
      verification_conditions P d /\ (post d ~~> Q)
  end.

(** And now, the key theorem, which captures the claim that the
    [verification_conditions] function does its job correctly.  Not
    surprisingly, we need all of the Hoare Logic rules in the
    proof. *)
(** We have used _in_ variants of several tactics before to
    apply them to values in the context rather than the goal. An
    extension of this idea is the syntax [tactic in *], which applies
    [tactic] in the goal and every hypothesis in the context.  We most
    commonly use this facility in conjunction with the [simpl] tactic,
    as below. *)

Theorem verification_correct : forall d P, 
  verification_conditions P d -> {{P}} (extract d) {{post d}}.
Proof.
  dcom_cases (induction d) Case; intros P H; simpl in *.
  Case "Skip".
    eapply hoare_consequence_pre.
      apply hoare_skip.
      assumption.
  Case "Seq". 
    inversion H as [H1 H2]. clear H. 
    eapply hoare_seq. 
      apply IHd2. apply H2.
      apply IHd1. apply H1.
  Case "Asgn". 
    eapply hoare_consequence_pre.
      apply hoare_asgn.
      assumption.
  Case "If".
    inversion H as [HPre1 [HPre2 [Hd1 [Hd2 [HThen HElse]]]]]; clear H.
    subst.
    apply hoare_if.
      eapply hoare_consequence_pre. apply IHd1. eassumption. assumption.
      rewrite Hd2.
      eapply hoare_consequence_pre. apply IHd2. eassumption. assumption.
  Case "While".
    inversion H as [Hpre [Hbody [Hpost Hd]]]; subst; clear H.
    eapply hoare_consequence_pre.
    apply hoare_while with (P := post d). 
      apply IHd. apply Hd. 
      assumption.
  Case "Pre".
    inversion H as [HP Hd]; clear H. 
    eapply hoare_consequence_pre. apply IHd. apply Hd. assumption.
  Case "Post".
    inversion H as [Hd HQ]; clear H.
    eapply hoare_consequence_post. apply IHd. apply Hd. assumption.
Qed.

(** ** Examples *)

(** The propositions generated by [verification_conditions] are fairly
    big, and they contain many conjuncts that are essentially trivial. *)

Eval simpl in (verification_conditions (fun st => True) dec_while).
(* ====>
 = (((fun _ : state => True) ~~> (fun _ : state => True)) /\
    ((fun _ : state => True) ~~> (fun _ : state => True)) /\
    (fun st : state => True /\ bassn (BNot (BEq (AId X) (ANum 0))) st) =
    (fun st : state => True /\ bassn (BNot (BEq (AId X) (ANum 0))) st) /\
    (fun st : state => True /\ ~ bassn (BNot (BEq (AId X) (ANum 0))) st) =
    (fun st : state => True /\ ~ bassn (BNot (BEq (AId X) (ANum 0))) st) /\
    (fun st : state => True /\ bassn (BNot (BEq (AId X) (ANum 0))) st) ~~>
    assn_sub X (AMinus (AId X) (ANum 1)) (fun _ : state => True)) /\
   (fun st : state => True /\ ~ bassn (BNot (BEq (AId X) (ANum 0))) st) ~~>
   (fun st : state => st X = 0) *)

(** We can certainly work with them using just the tactics we have so
    far, but we can make things much smoother with a bit of
    automation.  We first define a custom [verify] tactic that applies
    splitting repeatedly to turn all the conjunctions into separate
    subgoals and then uses [omega] and [eauto] (a handy
    general-purpose automation tactic that we'll discuss in detail
    later) to deal with as many of them as possible. *)

Tactic Notation "verify" :=
  apply verification_correct; 
  repeat split;
  simpl; unfold assert_implies; 
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat rewrite update_eq;
  repeat (rewrite update_neq; [| reflexivity]);
  simpl in *; 
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite beq_nat_true_iff in *;
  repeat rewrite beq_nat_false_iff in *;
  try eauto; try omega.

(** What's left after [verify] does its thing is "just the interesting
    parts" of checking that the decorations are correct. For very
    simple examples [verify] immediately solves the goal (provided
    that the annotations are correct). *)

Theorem dec_while_correct :
  dec_correct dec_while.
Proof. verify. Qed.

(** Another example (formalizing a decorated program we've seen
    before): *)

Example subtract_slowly_dec (x:nat) (z:nat) : dcom := (
    {{ fun st => st X = x /\ st Z = z }}
  WHILE BNot (BEq (AId X) (ANum 0))
  DO   {{ fun st => st Z - st X = z - x
                 /\ bassn (BNot (BEq (AId X) (ANum 0))) st }}
     Z ::= AMinus (AId Z) (ANum 1)
       {{ fun st => st Z - (st X - 1) = z - x }} ;
     X ::= AMinus (AId X) (ANum 1) 
       {{ fun st => st Z - st X = z - x }}
  END
    {{ fun st =>   st Z 
                 - st X 
                 = z - x 
              /\ ~ bassn (BNot (BEq (AId X) (ANum 0))) st }}
    =>
    {{ fun st => st Z = z - x }}
) % dcom.

Theorem subtract_slowly_dec_correct : forall x z, 
  dec_correct (subtract_slowly_dec x z).
Proof. intros x z. verify. (* this grinds for a bit! *) Qed.

(** **** Exercise: 3 stars, optional (slow_assignment_dec) *)

(** A roundabout way of assigning a number currently stored in [X] to
   the variable [Y] is to start [Y] at [0], then decrement [X] until it
   hits [0], incrementing [Y] at each step.

   Here is an informal decorated program that implements this idea
   given a parameter [x]: *)

(**
      {{ True }}
    X ::= x
      {{ X = x }} ;
    Y ::= 0
      {{ X = x /\ Y = 0 }} ;
    WHILE X <> 0 DO
        {{ X + Y = x /\ X > 0 }}
      X ::= X - 1
        {{ Y + X + 1 = x }} ;
      Y ::= Y + 1
        {{ Y + X = x }}
    END
      {{ Y = x /\ X = 0 }}
*)

(** Write a corresponding formal decorated program (parametrized by x)
    and prove it correct. *)

Example slow_assignment_dec (x:nat) : dcom :=
(* FILL IN HERE *) admit.

Theorem slow_assignment_dec_correct : forall x,
  dec_correct (slow_assignment_dec x).
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, optional (factorial_dec)  *)
(** Remember the factorial function we worked with before: *)

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(** Following the pattern of [subtract_slowly_dec], write a decorated
    Imp program that implements the factorial function, and prove it
    correct. *)

(* FILL IN HERE *)
(** [] *)

Definition div_mod_dec (a b : nat) : dcom := (
{{ fun st => True }} =>
  {{ fun st => b * 0 + a = a }}
  X ::= ANum a
  {{ fun st => b * 0 + st X = a }};
  Y ::= ANum 0
  {{ fun st => b * st Y + st X = a }};
  WHILE (BLe (ANum b) (AId X)) DO
    {{ fun st => b * st Y + st X = a /\ (bassn (BLe (ANum b) (AId X)) st) }} =>
    {{ fun st => b * (st Y + 1) + (st X - b) = a }}
    X ::= AMinus (AId X) (ANum b)
    {{ fun st => b * (st Y + 1) + st X = a }};
    Y ::= APlus (AId Y) (ANum 1)
    {{ fun st => b * st Y + st X = a }}
  END
  {{ fun st => b * st Y + st X = a /\ ~(bassn (BLe (ANum b) (AId X)) st) }} =>
  {{ fun st => b * st Y + st X = a /\ (st X < b) }}
)%dcom.

Theorem div_mod_dec_correct : forall a b,
  dec_correct (div_mod_dec a b).
Proof.
  intros a b. verify. 
  Case "1". apply ble_nat_true in H0. rewrite mult_plus_distr_l. omega.
  Case "2". apply ble_nat_false in H0. omega.
            (* more automation would help  here *)
Qed.


