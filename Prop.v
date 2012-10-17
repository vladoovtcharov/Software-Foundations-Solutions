(** * Prop: Propositions and Evidence *)

(* $Date: 2012-07-23 16:26:25 -0400 (Mon, 23 Jul 2012) $ *)

Require Export Poly.



(** In previous chapters, we have seen many examples of factual
    claims (_propositions_) and ways of presenting evidence of their
    truth (_proofs_).  In particular, we have worked extensively with
    _equality propositions_ of the form [e1 = e2], with
    implications ([P -> Q]), and with quantified propositions 
    ([forall x, P]).

    In this chapter we take a deeper look at the way propositions are
    expressed in Coq and at the structure of the logical evidence that
    we construct when we carry out proofs.  

    Some of the concepts in this chapter may seem a bit abstract on a
    first encounter.  We've included a _lot_ of exercises, most of
    which should be quite approachable even if you're still working on
    understanding the details of the text.  Try to work as many of
    them as you can, especially the one-starred exercises. *)

(* ##################################################### *)
(** * Inductively Defined Propositions *)

(** As a running example for the first part of the chapter, let's
    consider a simple property of natural numbers, and let's say that
    the numbers possessing this property are "beautiful." *)

(** Informally, a number is _beautiful_ if it is [0], [3], [5], or the
    sum of two beautiful numbers.  More pedantically, we can define
    beautiful numbers by giving four rules:

       - Rule [b_0]: The number [0] is beautiful.
       - Rule [b_3]: The number [3] is beautiful. 
       - Rule [b_5]: The number [5] is beautiful. 
       - Rule [b_sum]: If [n] and [m] are both beautiful, then so is
         their sum. *)

(** We will see many definitions like this one during the rest of the
    course, and for purposes of informal discussions, it is helpful to
    have a lightweight notation that makes them easy to read and
    write.  _Inference rules_ are one such notation: *)
(**
                              -----------                               (b_0)
                              beautiful 0
                              
                              ------------                              (b_3)
                              beautiful 3

                              ------------                              (b_5)
                              beautiful 5    

                       beautiful n     beautiful m
                       ---------------------------                      (b_sum)
                              beautiful (n+m)   
*)

(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [b_sum] says that, if [n] and [m]
    are both beautiful numbers, then it follows that [n+m] is
    beautiful too.  The rules with no premises above the line are
    called _axioms_.

    These rules _define_ the property [beautiful].  That is, if we
    want to convince someone that some particular number is beautiful,
    our argument must be based on these rules.  For a simple example,
    suppose we claim that the number [5] is beautiful.  To support
    this claim, we just need to point out that rule [b_5] says it is.
    Or, if we want to claim that [8] is beautiful, we can support our
    claim by first observing that [3] and [5] are both beautiful (by
    rules [b_3] and [b_5]) and then pointing out that their sum, [8],
    is therefore beautiful by rule [b_sum].  This argument can be
    expressed graphically with the following _proof tree_:
         ----------- (b_3)   ----------- (b_5)
         beautiful 3         beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8   
    Of course, there are other ways of using these rules to argue that
    [8] is beautiful -- for instance:
         ----------- (b_5)   ----------- (b_3)
         beautiful 5         beautiful 3
         ------------------------------- (b_sum)
                   beautiful 8   
*)

(** **** Exercise: 1 star (varieties_of_beauty) *)
(** How many different ways are there to show that [8] is beautiful? *)

(* FILL IN HERE *)
(** [] *)

(** In Coq, we can express the definition of [beautiful] as
    follows: *)

Inductive beautiful : nat -> Prop :=
  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

(** The first line declares that [beautiful] is a proposition -- or,
    more formally, a family of propositions "indexed by" natural
    numbers.  (For each number [n], the claim that "[n] is
    [beautiful]" is a proposition.)  Such a family of propositions is
    often called a _property_ of numbers.

    Each of the remaining lines embodies one of the rules for
    beautiful numbers. 

    We can use Coq's tactic scripting facility to assemble proofs that
    particular numbers are beautiful. *)

Theorem three_is_beautiful: beautiful 3.
Proof.
   (* This simply follows from the axiom [b_3]. *)
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   (* First we use the rule [b_sum], telling Coq how to
      instantiate [n] and [m]. *)
   apply b_sum with (n:=3) (m:=5).
   (* To solve the subgoals generated by [b_sum], we must provide
      evidence of [beautiful 3] and [beautiful 5]. Fortunately we
      have axioms for both. *)
   apply b_3.
   apply b_5.
Qed.

(* ##################################################### *)
(** * Proof Objects *)

(** Look again at the formal definition of the [beautiful] property.
    The opening keyword, [Inductive], has been used up to this point
    to declare new types of _data_, such as numbers and lists.  Does
    this interpretation also make sense for the Inductive definition
    of [beautiful]?  That is, can we view evidence of beauty as some
    kind of data structure? Yes, we can!  

    The trick is to introduce an alternative pronunciation of "[:]".
    Instead of "has type," we can also say "is a proof of."  For
    example, the second line in the definition of [beautiful] declares
    that [b_0 : beautiful 0].  Instead of "[b_0] has type 
    [beautiful 0]," we can say that "[b_0] is a proof of [beautiful 0]."
    Similarly for [b_3] and [b_5].

    This pun between "[:]" as "has type" and [:] as "is a proof of" is
    called the _Curry-Howard correspondence_ (or sometimes
    _Curry-Howard isomorphism_).  It proposes a deep connection
    between the world of logic and the world of computation.
<<
                 propositions  ~  types
                 evidence      ~  data 
>>
    Many useful things follow from this connection.  To begin with, it
    gives us a natural interpretation of the [b_sum] constructor: *)
(**
    b_sum : forall n m, 
            beautiful n -> beautiful m -> beautiful (n+m).
*)
(** If we read [:] as "has type," this says that [b_sum] is a data
    constructor that takes four arguments: two numbers, [n] and [m],
    and two values of type [beautiful n] and [beautiful m].  That is,
    [b_sum] can be viewed as a _function_ that, given evidence for the
    propositions [beautiful n] and [beautiful m], gives us evidence
    for the proposition that [beautiful (n+m)]. *)

(** In view of this, we might wonder whether we can write an
    expression of type [beautiful 8] by applying [b_sum] to
    appropriate arguments.  Indeed, we can: *)

Check (b_sum 3 5 b_3 b_5).  

(** The expression [b_sum 3 5 b_3 b_5] can be thought of as
    instantiating the parameterized constructor [b_sum] with the
    specific arguments [3] [5] and the corresponding proof objects for
    its premises [beautiful 3] and [beautiful 5] (Coq is smart enough
    to figure out that 3+5=8).  Alternatively, we can think of [b_sum]
    as a primitive "evidence constructor" that, when applied to two
    particular numbers, wants to be further applied to evidence that
    those two numbers are beautiful; its type, 
[[  
    forall n m, beautiful n -> beautiful m -> beautiful (n+m),
    expresses this functionality, in the same way that the polymorphic
    type [forall X, list X] in the previous chapter expressed the fact
    that the constructor [nil] can be thought of as a function from
    types to empty lists with elements of that type. *)

(** This gives us an alternative way to write the proof that [8] is
    beautiful: *)

Theorem eight_is_beautiful': beautiful 8.
Proof.
   apply (b_sum 3 5 b_3 b_5).
Qed.

(** Notice that we're using [apply] here in a new way: instead of just
    supplying the _name_ of a hypothesis or previously proved theorem
    whose type matches the current goal, we are supplying an
    _expression_ that directly builds evidence with the required
    type. *)

(* ##################################################### *)
(** ** Proof Scripts and Proof Objects *)

(** These proof objects lie at the core of how Coq operates. 

    When Coq is following a proof script, what is happening internally
    is that it is gradually constructing a proof object -- a term
    whose type is the proposition being proved.  The tactics between
    the [Proof] command and the [Qed] instruct Coq how to build up a
    term of the required type.  To see this process in action, let's
    use the [Show Proof] command to display the current state of the
    proof tree at various points in the following tactic proof. *)

Theorem eight_is_beautiful'': beautiful 8.
Proof.
   apply b_sum with (n:=3) (m:=5).
   Show Proof.
   apply b_3.
   Show Proof.
   apply b_5.
   Show Proof.
Qed.

(** At any given moment, Coq has constructed a term with some
    "holes" (indicated by [?1], [?2], and so on), and it knows what
    type of evidence is needed at each hole.  In the [Show Proof]
    output, lines of the form [?1 -> beautiful n] record these
    requirements.  (The [->] here has nothing to do with either
    implication or function types -- it is just an unfortunate choice
    of concrete syntax for the output!)  

    Each of the holes corresponds to a subgoal, and the proof is
    finished when there are no more subgoals.  At this point, the
    [Theorem] command gives a name to the evidence we've built and
    stores it in the global context. *)

(** Tactic proofs are useful and convenient because they avoid
    building proof trees by hand, but they are not essential: in
    principle, we can always construct the required evidence by hand.
    Indeed, we don't even need the [Theorem] command: we can use
    [Definition] instead, to directly give a global name to a piece of
    evidence. *)

Definition eight_is_beautiful''' : beautiful 8 :=
  b_sum 3 5 b_3 b_5.

(** All these different ways of building the proof lead to exactly the
    same evidence being saved in the global environment. *)

Print eight_is_beautiful.
(* ===> eight_is_beautiful = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful'.
(* ===> eight_is_beautiful' = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful''.
(* ===> eight_is_beautiful'' = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful'''.
(* ===> eight_is_beautiful''' = b_sum 3 5 b_3 b_5 : beautiful 8 *)

(** **** Exercise: 1 star (six_is_beautiful) *)
(** Give a tactic proof and a proof object showing that [6] is [beautiful]. *)

Theorem six_is_beautiful :
  beautiful 6.
Proof.
  (* FILL IN HERE *) Admitted.

Definition six_is_beautiful' : beautiful 6 :=
  (* FILL IN HERE *) admit.
(** [] *)

(** **** Exercise: 1 star (nine_is_beautiful) *)
(** Give a tactic proof and a proof object showing that [9] is [beautiful]. *)

Theorem nine_is_beautiful :
  beautiful 9.
Proof.
  (* FILL IN HERE *) Admitted.

Definition nine_is_beautiful' : beautiful 9 :=
  (* FILL IN HERE *) admit.
(** [] *)


(* ##################################################### *)
(** ** Implications and Functions *)

(** If we want to substantiate the claim that [P -> Q], what sort of
    proof object should count as evidence?

    We've seen one case above: the [b_sum] constructor, which is
    _primitive_ evidence for an implication proposition -- it is part
    of the very meaning of the word "beautiful" in this context.  But
    what about other implications that we might want to prove?

    For example, consider this statement: *)

Theorem b_plus3: forall n, beautiful n -> beautiful (3+n).
Proof.
   intros n H.
   apply b_sum.
   apply b_3.
   apply H.
Qed.

(** What is the proof object corresponding to [b_plus3]? 

    We've made a notational pun between [->] as implication and [->]
    as the type of functions.  If we take this pun seriously, then
    what we're looking for is an expression whose _type_ is 
    [forall n, beautiful n -> beautiful (3+n)] -- that is, a
    _function_ that takes two arguments (one number and a piece of
    evidence) and returns a piece of evidence!  Here it is: *)

Definition b_plus3' : forall n, beautiful n -> beautiful (3+n) := 
  fun n => fun H : beautiful n =>
    b_sum 3 n b_3 H.
Check b_plus3'.
(* ===> b_plus3' : forall n, beautiful n -> beautiful (3+n) *)

(** Recall that [fun n => blah] means "the function that, given [n],
    yields [blah]."  Another equivalent way to write this definition is: *)

Definition b_plus3'' (n : nat) (H : beautiful n) : beautiful (3+n) := 
  b_sum 3 n b_3 H.
Check b_plus3''.
(* ===> b_plus3'' : forall n, beautiful n -> beautiful (3+n) *)

(** **** Exercise: 2 stars (b_times2) *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
    (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (b_times2') *)
(** Write a proof object corresponding to [b_times2] above *)

Definition b_times2': forall n, beautiful n -> beautiful (2*n) :=
  (* FILL IN HERE *) admit.

(** **** Exercise: 2 stars (b_timesm) *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
   (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *)
(** ** Induction Over Proof Objects *)

(** Since we use the keyword [Induction] to define primitive
    propositions together with their evidence, we might wonder whether
    there are some sort of induction principles associated with these
    definitions.  Indeed there are, and in this section we'll take a
    look at how they can be used.  *)

(** Besides _constructing_ evidence that numbers are beautiful, we can
    also _reason about_ such evidence.  The fact that we introduced
    [beautiful] with an [Inductive] declaration tells us not only that
    the constructors [b_0], [b_3], [b_5] and [b_sum] are ways to build
    evidence, but also that these two constructors are the _only_ ways
    to build evidence that numbers are beautiful. *)

(** In other words, if someone gives us evidence [E] justifying the
    assertion [beautiful n], then we know that [E] can only have one
    of four forms: either [E] is [b_0] (and [n] is [O]) or [E] is
    [b_3] (and [n] is [3]), or [E] is [b_5] (and [n] is [5]), or [E]
    is [b_sum n1 n2 E1 E2] (and [n] is [(n1+n2)], and [E1] is evidence
    that [n1] is beauiful and [E2] is evidence that [n2] is
    beautiful). *)
    
(** Thus, it makes sense to use the tactics that we have already seen
    for inductively defined _data_ to reason instead about inductively
    defined _evidence_.

    Let's introduce a new property of numbers to help illustrate the
    role of induction. *)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(** **** Exercise: 1 star (gorgeous_tree) *)
(** Write out the definition of gorgeous numbers using the _inference
    rule_ notation.
 
(* FILL IN HERE *)
[]
*)

(** It seems intuitively obvious that, although [gorgeous] and
    [beautiful] are presented using slightly different rules, they are
    actually the same property in the sense that they are true of the
    same numbers.  Indeed, we can prove this. *)

Theorem gorgeous__beautiful : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros.
   (* The argument proceeds by induction on the evidence H! *) 
   induction H as [|n'|n'].
   Case "g_0".
       apply b_0.
   Case "g_plus3". 
       apply b_sum. apply b_3.
       apply IHgorgeous.
   Case "g_plus5".
       apply b_sum. apply b_5. apply IHgorgeous. 
Qed.

(** Let's see what happens if we try to prove this by induction on [n]
   instead of induction on the evidence [H]. *)

Theorem gorgeous__beautiful_FAILED : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros. induction n as [| n'].
   Case "n = 0". apply b_0.
   Case "n = S n'". (* We are stuck! *)
Admitted.


(** **** Exercise: 1 star (gorgeous_plus13) *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
   (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (gorgeous_plus13_po):
Give the proof object for theorem [gorgeous_plus13] above. *)

Definition gorgeous_plus13_po: forall n, gorgeous n -> gorgeous (13+n):=
   (* FILL IN HERE *) admit.
(** [] *)

(** **** Exercise: 2 stars (gorgeous_sum) *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (beautiful__gorgeous) *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (b_times2) *)
(** Prove the [g_times2] theorem below without using [gorgeous__beautiful].
    You might find the following helper lemma useful. *)

Lemma helper_g_times2 : forall x y z, x + (z + y)= z + x + y.
Proof.
   (* FILL IN HERE *) Admitted.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
   intros n H. simpl. 
   induction H.
   (* FILL IN HERE *) Admitted.
(** [] *)


(* ####################################################### *)
(** ** Evenness *)

(** In chapter [Basics] we defined a _function_ [evenb] that tests a number
    for evenness, yielding [true] if so.  This gives us an obvious way
    of defining the _concept_ of evenness: *)

Definition even (n:nat) : Prop := 
  evenb n = true.

(** That is, we can define "[n] is even" to mean "the function
    [evenb] returns [true] when applied to [n]."

    Another alternative is to define the concept of evenness directly.
    Instead of going via the [evenb] function ("a number is even if a
    certain computation yields [true]"), we can say what the concept
    of evenness means by giving two different ways of presenting
    _evidence_ that a number is even. *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** This definition says that there are two ways to give
    evidence that a number [m] is even.  First, [0] is even, and
    [ev_0] is evidence for this.  Second, if [m = S (S n)] for some
    [n] and we can give evidence [e] that [n] is even, then [m] is
    also even, and [ev_SS n e] is the evidence. *)

(** **** Exercise: 1 star (double_even) *)
(** Construct a tactic proof of the following proposition. *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, optional (double_even_pfobj) *)
(** Try to predict what proof object is constructed by the above
    tactic proof.  (Before checking your answer, you'll want to
    strip out any uses of [Case], as these will make the proof
    object look a bit cluttered.) *)
(** [] *)

(** *** Discussion: Computational vs. Inductive Definitions *)

(** We have seen that the proposition "some number is even" can
    be phrased in two different ways -- indirectly, via a boolean
    testing function [evenb], or directly, by inductively describing
    what constitutes evidence for evenness.  These two ways of
    defining evenness are about equally easy to state and work with.
    Which we choose is basically a question of taste.

    However, for many other properties of interest, the direct
    inductive definition is preferable, since writing a testing
    function may be awkward or even impossible.  

    One such property is [beautiful].  This is a perfectly sensible
    definition of a set of numbers, but we cannot translate its
    definition directly as a Coq Fixpoint (or translate it directly
    into a recursive function in any other programming language).  We
    might be able to find a clever way of testing this property using
    a [Fixpoint] (indeed, it is not too hard to find one in this
    case), but in general this could require arbitrarily deep
    thinking.  In fact, if the property we are interested in is
    uncomputable, then we cannot define it as a [Fixpoint] no matter
    how hard we try, because Coq requires that all [Fixpoint]s
    correspond to terminating computations.

    On the other hand, writing an inductive definition of what it
    means to give evidence for the property [beautiful] is
    straightforward. *)


(* ####################################################### *)
(** ** Inverting Evidence *)

(** Besides induction, we can use the other tactics in our toolkit
    with evidence.  For example, this proof uses [destruct] on
    evidence. *)

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  destruct E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0. 
  Case "E = ev_SS n' E'". simpl. apply E'.  Qed.

(** **** Exercise: 1 star, optional (ev_minus2_n) *)
(** What happens if we try to [destruct] on [n] instead of [E]? *)
(** [] *)

(** **** Exercise: 1 star, recommended (ev__even) *)
(** Here is a proof that the inductive definition of evenness implies
    the computational one. *)

Theorem ev__even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0". 
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".  
    unfold even. apply IHE'.  
Qed.
(** Could this proof also be carried out by induction on [n] instead
    of [E]?  If not, why not? *)

(* FILL IN HERE *)
(** [] *)

(** The induction principle for inductively defined propositions does
    not follow quite the same form as that of inductively defined
    sets.  For now, you can take the intuitive view that induction on
    evidence [ev n] is similar to induction on [n], but restricts our
    attention to only those numbers for which evidence [ev n] could be
    generated.  We'll look at the induction principle of [ev] in more
    depth below, to explain what's really going on. *)

(** **** Exercise: 1 star (l_fails) *)
(** The following proof attempt will not succeed.
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...
   Briefly explain why.
 
(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars (ev_sum) *)
(** Here's another exercise requiring induction. *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Here's another situation where we want to analyze evidence for
    evenness: proving that if [n+2] is even, then [n] is.  Our first
    idea might be to use [destruct] for this kind of case analysis: *)

Theorem SSev_ev_firsttry : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  destruct E as [| n' E'].
  (* Stuck: [destruct] gives us un-provable subgoal here! *)
Admitted.

(** In the first sub-goal, we've lost the information that [n] is [0].
   We could have used [remember], but then we still need [inversion]
   on both cases. *)

Theorem SSev_ev_secondtry : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. remember (S (S n)) as n2.
  destruct E as [| n' E'].
  Case "n = 0". inversion Heqn2.
  Case "n = S n'". inversion Heqn2. rewrite <- H0. apply E'.
Qed.

(** There is a much simpler way to this: we can use [inversion] directly
    on the inductively defined proposition [ev (S (S n))]. *)

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E']. apply E'. Qed.

(* Print SSev__even. *)

(** This use of [inversion] may seem a bit mysterious at first.
    Until now, we've only used [inversion] on equality
    propositions, to utilize injectivity of constructors or to
    discriminate between different constructors.  But we see here
    that [inversion] can also be applied to analyzing evidence
    for inductively defined propositions.

    Here's how [inversion] works in general.  Suppose the name
    [I] refers to an assumption [P] in the current context, where
    [P] has been defined by an [Inductive] declaration.  Then,
    for each of the constructors of [P], [inversion I] generates
    a subgoal in which [I] has been replaced by the exact,
    specific conditions under which this constructor could have
    been used to prove [P].  Some of these subgoals will be
    self-contradictory; [inversion] throws these away.  The ones
    that are left represent the cases that must be proved to
    establish the original goal.

    In this particular case, the [inversion] analyzed the construction
    [ev (S (S n))], determined that this could only have been
    constructed using [ev_SS], and generated a new subgoal with the
    arguments of that constructor as new hypotheses.  (It also
    produced an auxiliary equality, which happens to be useless here.)
    We'll begin exploring this more general behavior of inversion in
    what follows. *)

(** **** Exercise: 1 star (inversion_practice) *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* FILL IN HERE *) Admitted.

(** The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We can generally use [inversion] on inductive propositions.
    This illustrates that in general, we get one case for each
    possible constructor.  Again, we also get some auxiliary
    equalities that are rewritten in the goal but not in the other
    hypotheses. *)

Theorem ev_minus2': forall n,
  ev n -> ev (pred (pred n)). 
Proof.
  intros n E. inversion E as [| n' E']. 
  Case "E = ev_0". simpl. apply ev_0. 
  Case "E = ev_SS n' E'". simpl. apply E'.  Qed.

(** **** Exercise: 3 stars, recommended (ev_ev__ev) *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_plus_plus) *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious.  You'll want the [replace] tactic used for [plus_swap']
    in Basics.v *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ##################################################### *)
(* ##################################################### *)
(** * Programming with Propositions *)

(** A _proposition_ is a statement expressing a factual claim,
    like "two plus two equals four."  In Coq, propositions are written
    as expressions of type [Prop].  Although we haven't mentioned it
    explicitly, we have already seen numerous examples. *)

Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ===> ble_nat 3 2 = false : Prop *)

Check (beautiful 8).
(* ===> beautiful 8 : Prop *)

(** Both provable and unprovable claims are perfectly good
    propositions.  Simply _being_ a proposition is one thing; being
    _provable_ is something else! *)

Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)

(** Both [2 + 2 = 4] and [2 + 2 = 5] are legal expressions
    of type [Prop]. *)

(** We've seen one way that propositions can be used in Coq: in
    [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 : 
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But they can be used in many other ways.  For example, we
    can give a name to a proposition using a [Definition], just as we
    have given names to expressions of other sorts (numbers,
    functions, types, type functions, ...). *)

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** Now we can use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem]
    declaration. *)

Theorem plus_fact_is_true : 
  plus_fact.
Proof. reflexivity.  Qed.

(** There are many ways of constructing propositions.  We can define a
    new proposition primitively using [Inductive], we can form an
    equality proposition from two computational expressions, and we
    can build up a new proposition from existing ones using
    implication and quantification. *)

Definition strange_prop1 : Prop :=
  (2 + 2 = 5) -> (99 + 26 = 42).

(** Also, given a proposition [P] with a free variable [n], we can
    form the proposition [forall n, P]. *)

Definition strange_prop2 :=
  forall n, (ble_nat n 17 = true) -> (ble_nat n 99 = true).

(** We can also define _parameterized propositions_, such as
    the property of being even. *)

Check even. 
(* ===> even : nat -> Prop *)
Check (even 4).
(* ===> even 4 : Prop *)
Check (even 3).
(* ===> even 3 : Prop *)

(** The type of [even], [nat->Prop], can be pronounced in three
    equivalent ways: (1) "[even] is a _function_ from numbers to
    propositions," (2) "[even] is a _family_ of propositions, indexed
    by a number [n]," or (3) "[even] is a _property_ of numbers."  *)

(** Propositions -- including parameterized propositions -- are
    first-class citizens in Coq.  For example, we can define them to
    take multiple arguments... *)

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

(** ... and then partially apply them: *)

Definition teen : nat->Prop := between 13 19.

(** We can even pass propositions -- including parameterized
    propositions -- as arguments to functions: *)

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

(** Here are two more examples of passing parameterized propositions
    as arguments to a function.  The first takes a proposition [P] as
    argument and builds the proposition that [P] is true for all
    natural numbers.  The second takes [P] and builds the proposition
    that, if [P] is true for some natural number [n'], then it is also
    true by the successor of [n'] -- i.e. that [P] is _preserved by
    successor_:*)

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(* ##################################################### *)
(** * Induction Principles *)

(** This is a good point to pause and take a deeper look at induction
    principles in general. *)

(* ##################################################### *)
(** ** Induction Principles for Inductively Defined Types *)

(** Every time we declare a new [Inductive] datatype, Coq
    automatically generates an axiom that embodies an _induction
    principle_ for this type.

    The induction principle for a type [t] is called [t_ind].  Here is
    the one for natural numbers: *)

Check nat_ind.
(*  ===> nat_ind : 
           forall P : nat -> Prop,
              P 0  ->
              (forall n : nat, P n -> P (S n))  ->
              forall n : nat, P n  *)

(** The [induction] tactic is a straightforward wrapper that, at
    its core, simply performs [apply t_ind].  To see this more
    clearly, let's experiment a little with using [apply nat_ind]
    directly, instead of the [induction] tactic, to carry out some
    proofs.  Here, for example, is an alternate proof of a theorem
    that we saw in the [Basics] chapter. *)

Theorem mult_0_r' : forall n:nat, 
  n * 0 = 0.
Proof.
  apply nat_ind. 
  Case "O". reflexivity.
  Case "S". simpl. intros n IHn. rewrite -> IHn. 
    reflexivity.  Qed.

(** This proof is basically the same as the earlier one, but a
    few minor differences are worth noting.  First, in the induction
    step of the proof (the ["S"] case), we have to do a little
    bookkeeping manually (the [intros]) that [induction] does
    automatically.

    Second, we do not introduce [n] into the context before applying
    [nat_ind] -- the conclusion of [nat_ind] is a quantified formula,
    and [apply] needs this conclusion to exactly match the shape of
    the goal state, including the quantifier.  The [induction] tactic
    works either with a variable in the context or a quantified
    variable in the goal.

    Third, the [apply] tactic automatically chooses variable names for
    us (in the second subgoal, here), whereas [induction] lets us
    specify (with the [as...]  clause) what names should be used.  The
    automatic choice is actually a little unfortunate, since it
    re-uses the name [n] for a variable that is different from the [n]
    in the original theorem.  This is why the [Case] annotation is
    just [S] -- if we tried to write it out in the more explicit form
    that we've been using for most proofs, we'd have to write [n = S
    n], which doesn't make a lot of sense!  All of these conveniences
    make [induction] nicer to use in practice than applying induction
    principles like [nat_ind] directly.  But it is important to
    realize that, modulo this little bit of bookkeeping, applying
    [nat_ind] is what we are really doing. *)

(** **** Exercise: 2 stars, optional (plus_one_r') *)
(** Complete this proof as we did [mult_0_r'] above, without using
    the [induction] tactic. *)

Theorem plus_one_r' : forall n:nat, 
  n + 1 = S n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The induction principles that Coq generates for other datatypes
    defined with [Inductive] follow a similar pattern. If we define a
    type [t] with constructors [c1] ... [cn], Coq generates a theorem
    with this shape:
    t_ind :
       forall P : t -> Prop,
            ... case for c1 ... ->
            ... case for c2 ... ->
            ...                 ->
            ... case for cn ... ->
            forall n : t, P n
    The specific shape of each case depends on the arguments to the
    corresponding constructor.  Before trying to write down a general
    rule, let's look at some more examples. First, an example where
    the constructors take no arguments: *)

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind. 
(* ===> yesno_ind : forall P : yesno -> Prop, 
                      P yes  ->
                      P no  ->
                      forall y : yesno, P y *)

(** **** Exercise: 1 star (rgb) *)
(** Write out the induction principle that Coq will generate for
    the following datatype.  Write down your answer on paper, and
    then compare it with what Coq prints. *)

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Check rgb_ind.
(** [] *)

(** Here's another example, this time with one of the constructors
    taking some arguments. *)

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.
(* ===> (modulo a little tidying)
   natlist_ind :
      forall P : natlist -> Prop,
         P nnil  ->
         (forall (n : nat) (l : natlist), P l -> P (ncons n l)) ->
         forall n : natlist, P n *)

(** **** Exercise: 1 star (natlist1) *)
(** Suppose we had written the above definition a little
   differently: *)

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

(** Now what will the induction principle look like? *)
(** [] *)

(** From these examples, we can extract this general rule:

    - The type declaration gives several constructors; each
      corresponds to one clause of the induction principle.
    - Each constructor [c] takes argument types [a1]...[an].
    - Each [ai] can be either [t] (the datatype we are defining) or
      some other type [s].
    - The corresponding case of the induction principle
      says (in English):
        - "for all values [x1]...[xn] of types [a1]...[an], if
           [P] holds for each of the [x]s of type [t], then [P]
           holds for [c x1 ... xn]". *)

(** **** Exercise: 1 star (ex_set) *)
(** Here is an induction principle for an inductively defined
    set.
      ExSet_ind :
         forall P : ExSet -> Prop,
             (forall b : bool, P (con1 b)) ->
             (forall (n : nat) (e : ExSet), P e -> P (con2 n e)) ->
             forall e : ExSet, P e
    Give an [Inductive] definition of [ExSet]: *)

Inductive ExSet : Type :=
  (* FILL IN HERE *)
.
(** [] *)

(** What about polymorphic datatypes?

    The inductive definition of polymorphic lists
      Inductive list (X:Type) : Type :=
        | nil : list X
        | cons : X -> list X -> list X.
    is very similar to that of [natlist].  The main difference is
    that, here, the whole definition is _parameterized_ on a set [X]:
    that is, we are defining a _family_ of inductive types [list X],
    one for each [X].  (Note that, wherever [list] appears in the body
    of the declaration, it is always applied to the parameter [X].)
    The induction principle is likewise parameterized on [X]:
     list_ind :
       forall (X : Type) (P : list X -> Prop),
          P [] ->
          (forall (x : X) (l : list X), P l -> P (x :: l)) ->
          forall l : list X, P l
   Note the wording here (and, accordingly, the form of [list_ind]):
   The _whole_ induction principle is parameterized on [X].  That is,
   [list_ind] can be thought of as a polymorphic function that, when
   applied to a type [X], gives us back an induction principle
   specialized to the type [list X]. *)

(** **** Exercise: 1 star (tree) *)
(** Write out the induction principle that Coq will generate for
   the following datatype.  Compare your answer with what Coq
   prints. *)

Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.
Check tree_ind.
(** [] *)

(** **** Exercise: 1 star (mytype) *)
(** Find an inductive definition that gives rise to the
    following induction principle:
      mytype_ind :
        forall (X : Type) (P : mytype X -> Prop),
            (forall x : X, P (constr1 X x)) ->
            (forall n : nat, P (constr2 X n)) ->
            (forall m : mytype X, P m -> 
               forall n : nat, P (constr3 X m n)) ->
            forall m : mytype X, P m                   
*) 
(** [] *)

(** **** Exercise: 1 star, optional (foo) *)
(** Find an inductive definition that gives rise to the
    following induction principle:
      foo_ind :
        forall (X Y : Type) (P : foo X Y -> Prop),
             (forall x : X, P (bar X Y x)) ->
             (forall y : Y, P (baz X Y y)) ->
             (forall f1 : nat -> foo X Y,
               (forall n : nat, P (f1 n)) -> P (quux X Y f1)) ->
             forall f2 : foo X Y, P f2       
*) 
(** [] *)

(** **** Exercise: 1 star, optional (foo') *)
(** Consider the following inductive definition: *)

Inductive foo' (X:Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.

(** What induction principle will Coq generate for [foo']?  Fill
   in the blanks, then check your answer with Coq.)
     foo'_ind :
        forall (X : Type) (P : foo' X -> Prop),
              (forall (l : list X) (f : foo' X),
                    _______________________ -> 
                    _______________________   ) ->
             ___________________________________________ ->
             forall f : foo' X, ________________________
*)

(** [] *)

(* ##################################################### *)
(** ** Induction Hypotheses *)

(** Where does the phrase "induction hypothesis" fit into this story?

    The induction principle for numbers
       forall P : nat -> Prop,
            P 0  ->
            (forall n : nat, P n -> P (S n))  ->
            forall n : nat, P n
   is a generic statement that holds for all propositions
   [P] (strictly speaking, for all families of propositions [P]
   indexed by a number [n]).  Each time we use this principle, we
   are choosing [P] to be a particular expression of type
   [nat->Prop].

   We can make the proof more explicit by giving this expression a
   name.  For example, instead of stating the theorem [mult_0_r] as
   "[forall n, n * 0 = 0]," we can write it as "[forall n, P_m0r
   n]", where [P_m0r] is defined as... *)

Definition P_m0r (n:nat) : Prop := 
  n * 0 = 0.

(** ... or equivalently... *)

Definition P_m0r' : nat->Prop := 
  fun n => n * 0 = 0.

(** Now when we do the proof it is easier to see where [P_m0r]
    appears. *)

Theorem mult_0_r'' : forall n:nat, 
  P_m0r n.
Proof.
  apply nat_ind.
  Case "n = O". reflexivity.
  Case "n = S n'". 
    (* Note the proof state at this point! *)
    unfold P_m0r. simpl. intros n' IHn'. 
    apply IHn'.  Qed.

(** This extra naming step isn't something that we'll do in
    normal proofs, but it is useful to do it explicitly for an example
    or two, because it allows us to see exactly what the induction
    hypothesis is.  If we prove [forall n, P_m0r n] by induction on
    [n] (using either [induction] or [apply nat_ind]), we see that the
    first subgoal requires us to prove [P_m0r 0] ("[P] holds for
    zero"), while the second subgoal requires us to prove [forall n',
    P_m0r n' -> P_m0r n' (S n')] (that is "[P] holds of [S n'] if it
    holds of [n']" or, more elegantly, "[P] is preserved by [S]").
    The _induction hypothesis_ is the premise of this latter
    implication -- the assumption that [P] holds of [n'], which we are
    allowed to use in proving that [P] holds for [S n']. *)


(* ##################################################### *)
(** * Optional Material *)

(** This section offers some additional details on how induction works
    in Coq and the process of building proof trees.  It can safely be
    skimmed on a first reading.  (We recommend skimming rather than
    skipping over it outright: it answers some questions that occur to
    many Coq users at some point, so it is useful to have a rough idea
    of what's here.) *)

(* ##################################################### *)
(** ** Induction Principles in [Prop] *)

(** Earlier, we looked in detail at the induction principles that Coq
    generates for inductively defined _sets_.  The induction
    principles for inductively defined _propositions_ like [gorgeous]
    are a tiny bit more complicated.  As with all induction
    principles, we want to use the induction principle on [gorgeous]
    to prove things by inductively considering the possible shapes
    that something in [gorgeous] can have -- either it is evidence
    that [0] is gorgeous, or it is evidence that, for some [n], [3+n]
    is gorgeous, or it is evidence that, for some [n], [5+n] is
    gorgeous and it includes evidence that [n] itself is.  Intuitively
    speaking, however, what we want to prove are not statements about
    _evidence_ but statements about _numbers_.  So we want an
    induction principle that lets us prove properties of numbers by
    induction on evidence.

    For example, from what we've said so far, you might expect the
    inductive definition of [gorgeous]...
    Inductive gorgeous : nat -> Prop :=
         g_0 : gorgeous 0
       | g_plus3 : forall n, gorgeous n -> gorgeous (3+m)
       | g_plus5 : forall n, gorgeous n -> gorgeous (5+m).
    ...to give rise to an induction principle that looks like this...
    gorgeous_ind_max :
       forall P : (forall n : nat, gorgeous n -> Prop),
            P O g_0 ->
            (forall (m : nat) (e : gorgeous m), 
               P m e -> P (3+m) (g_plus3 m e) ->
            (forall (m : nat) (e : gorgeous m), 
               P m e -> P (5+m) (g_plus5 m e) ->
            forall (n : nat) (e : gorgeous n), P n e
    ... because:

     - Since [gorgeous] is indexed by a number [n] (every [gorgeous]
       object [e] is a piece of evidence that some particular number
       [n] is gorgeous), the proposition [P] is parameterized by both
       [n] and [e] -- that is, the induction principle can be used to
       prove assertions involving both a gorgeous number and the
       evidence that it is gorgeous.

     - Since there are three ways of giving evidence of gorgeousness
       ([gorgeous] has three constructors), applying the induction
       principle generates three subgoals:

         - We must prove that [P] holds for [O] and [b_0].

         - We must prove that, whenever [n] is a gorgeous
           number and [e] is an evidence of its gorgeousness,
           if [P] holds of [n] and [e],
           then it also holds of [3+m] and [g_plus3 n e].

         - We must prove that, whenever [n] is a gorgeous
           number and [e] is an evidence of its gorgeousness,
           if [P] holds of [n] and [e],
           then it also holds of [5+m] and [g_plus5 n e].

     - If these subgoals can be proved, then the induction principle
       tells us that [P] is true for _all_ gorgeous numbers [n] and
       evidence [e] of their gorgeousness.

    But this is a little more flexibility than we actually need or
    want: it is giving us a way to prove logical assertions where the
    assertion involves properties of some piece of _evidence_ of
    gorgeousness, while all we really care about is proving
    properties of _numbers_ that are gorgeous -- we are interested in
    assertions about numbers, not about evidence.  It would therefore
    be more convenient to have an induction principle for proving
    propositions [P] that are parameterized just by [n] and whose
    conclusion establishes [P] for all gorgeous numbers [n]:
       forall P : nat -> Prop,
          ... ->
             forall n : nat, gorgeous n -> P n
    For this reason, Coq actually generates the following simplified
    induction principle for [gorgeous]: *)

Check gorgeous_ind.
(* ===>  gorgeous_ind
     : forall P : nat -> Prop,
       P 0 ->
       (forall n : nat, gorgeous n -> P n -> P (3 + n)) ->
       (forall n : nat, gorgeous n -> P n -> P (5 + n)) ->
       forall n : nat, gorgeous n -> P n *)

(** In particular, Coq has dropped the evidence term [e] as a
    parameter of the the proposition [P], and consequently has
    rewritten the assumption [forall (n : nat) (e: gorgeous n), ...]
    to be [forall (n : nat), gorgeous n -> ...]; i.e., we no longer
    require explicit evidence of the provability of [gorgeous n]. *)

(** In English, [gorgeous_ind] says:

    - Suppose, [P] is a property of natural numbers (that is, [P n] is
      a [Prop] for every [n]).  To show that [P n] holds whenever [n]
      is gorgeous, it suffices to show:
  
      - [P] holds for [0],
  
      - for any [n], if [n] is gorgeous and [P] holds for
        [n], then [P] holds for [3+n],

      - for any [n], if [n] is gorgeous and [P] holds for
        [n], then [P] holds for [5+n]. *)

(** We can apply [gorgeous_ind] directly instead of using [induction]. *)

Theorem gorgeous__beautiful' : forall n, gorgeous n -> beautiful n.
Proof.
   intros.
   apply gorgeous_ind.
   Case "g_0".
       apply b_0.
   Case "g_plus3".
       intros.
       apply b_sum. apply b_3.
       apply H1.
   Case "g_plus5".
       intros.
       apply b_sum. apply b_5.
       apply H1.
   apply H.
Qed.

Module P.

(** **** Exercise: 3 stars, optional (p_provability) *)
(** Consider the following inductively defined proposition: *)

Inductive p : (tree nat) -> nat -> Prop :=
   | c1 : forall n, p (leaf _ n) 1
   | c2 : forall t1 t2 n1 n2,
            p t1 n1 -> p t2 n2 -> p (node _ t1 t2) (n1 + n2)
   | c3 : forall t n, p t n -> p t (S n).

(** Describe, in English, the conditions under which the
   proposition [p t n] is provable. 

   (* FILL IN HERE *)
*)
(** [] *)

End P.

(* ##################################################### *)
(** ** More on the [induction] Tactic *)

(** The [induction] tactic actually does even more low-level
    bookkeeping for us than we discussed above.

    Recall the informal statement of the induction principle for
    natural numbers:
      - If [P n] is some proposition involving a natural number n, and
        we want to show that P holds for _all_ numbers n, we can
        reason like this:
          - show that [P O] holds
          - show that, if [P n'] holds, then so does [P (S n')]
          - conclude that [P n] holds for all n.
    So, when we begin a proof with [intros n] and then [induction n],
    we are first telling Coq to consider a _particular_ [n] (by
    introducing it into the context) and then telling it to prove
    something about _all_ numbers (by using induction).

    What Coq actually does in this situation, internally, is to
    "re-generalize" the variable we perform induction on.  For
    example, in the proof above that [plus] is associative...
*)

Theorem plus_assoc' : forall n m p : nat, 
  n + (m + p) = (n + m) + p.   
Proof.
  (* ...we first introduce all 3 variables into the context,
     which amounts to saying "Consider an arbitrary [n], [m], and
     [p]..." *)
  intros n m p. 
  (* ...We now use the [induction] tactic to prove [P n] (that
     is, [n + (m + p) = (n + m) + p]) for _all_ [n],
     and hence also for the particular [n] that is in the context
     at the moment. *)
  induction n as [| n'].
  Case "n = O". reflexivity.
  Case "n = S n'". 
    (* In the second subgoal generated by [induction] -- the
       "inductive step" -- we must prove that [P n'] implies 
       [P (S n')] for all [n'].  The [induction] tactic 
       automatically introduces [n'] and [P n'] into the context
       for us, leaving just [P (S n')] as the goal. *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** It also works to apply [induction] to a variable that is
   quantified in the goal. *)

Theorem plus_comm' : forall n m : nat, 
  n + m = m + n.
Proof.
  induction n as [| n']. 
  Case "n = O". intros m. rewrite -> plus_0_r. reflexivity.
  Case "n = S n'". intros m. simpl. rewrite -> IHn'. 
    rewrite <- plus_n_Sm. reflexivity.  Qed.

(** Note that [induction n] leaves [m] still bound in the goal --
    i.e., what we are proving inductively is a statement beginning
    with [forall m].

    If we do [induction] on a variable that is quantified in the goal
    _after_ some other quantifiers, the [induction] tactic will
    automatically introduce the variables bound by these quantifiers
    into the context. *)

Theorem plus_comm'' : forall n m : nat, 
  n + m = m + n.
Proof.
  (* Let's do induction on [m] this time, instead of [n]... *)
  induction m as [| m']. 
  Case "m = O". simpl. rewrite -> plus_0_r. reflexivity.
  Case "m = S m'". simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity.  Qed.

(** **** Exercise: 1 star, optional (plus_explicit_prop) *)
(** Rewrite both [plus_assoc'] and [plus_comm'] and their proofs in
    the same style as [mult_0_r''] above -- that is, for each theorem,
    give an explicit [Definition] of the proposition being proved by
    induction, and state the theorem and proof in terms of this
    defined proposition.  *)

(* FILL IN HERE *)
(** [] *)

(* ##################################################### *)
(** One more quick digression, for adventurous souls: if we can define 
    parameterized propositions using [Definition], then can we also
    define them using [Fixpoint]?  Of course we can!  However, this
    kind of "recursive parameterization" doesn't correspond to
    anything very familiar from everyday mathematics.  The following
    exercise gives a slightly contrived example. *)

(** **** Exercise: 4 stars, optional (true_upto_n__true_everywhere) *)
(** Define a recursive function
    [true_upto_n__true_everywhere] that makes
    [true_upto_n_example] work. *)

(* 
Fixpoint true_upto_n__true_everywhere 
(* FILL IN HERE *)

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.
*)
(** [] *)

(* ####################################################### *)
(** ** Building Proof Objects Incrementally *)

(** As you probably noticed while solving the exercises earlier in the
    chapter, constructing proof objects is more involved than
    constructing the corresponding tactic proofs. Fortunately, there
    is a bit of syntactic sugar that we've already introduced to help
    in the construction: the [admit] term, which we've sometimes used
    to force Coq into accepting incomplete exercies. As an example,
    let's walk through the process of constructing a proof object
    demonstrating the beauty of [16]. *)

Definition b_16_atmpt_1 : beautiful 16 := admit.

(** Maybe we can use [b_sum] to construct a term of type [beautiful 16]?
    Recall that [b_sum] is of type

    forall n m : nat, beautiful n -> beautiful m -> beautiful (n + m)

    If we can demonstrate the beauty of [5] and [11], we should
    be done. *)

Definition b_16_atmpt_2 : beautiful 16 := b_sum 5 11 admit admit.

(** In the attempt above, we've omitted the proofs of the propositions
    that [5] and [11] are beautiful. But the first of these is already
    axiomatized in [b_5]: *)

Definition b_16_atmpt_3 : beautiful 16 := b_sum 5 11 b_5 admit.

(** What remains is to show that [11] is beautiful. We repeat the
    procedure: *)

Definition b_16_atmpt_4 : beautiful 16 :=
  b_sum 5 11 b_5 (b_sum 5 6 admit admit).

Definition b_16_atmpt_5 : beautiful 16 :=
  b_sum 5 11 b_5 (b_sum 5 6 b_5 admit).

Definition b_16_atmpt_6 : beautiful 16 :=
  b_sum 5 11 b_5 (b_sum 5 6 b_5 (b_sum 3 3 admit admit)).

(** And finally, we can complete the proof object: *)

Definition b_16 : beautiful 16 :=
  b_sum 5 11 b_5 (b_sum 5 6 b_5 (b_sum 3 3 b_3 b_3)).

(** To recap, we've been guided by an informal proof that we have in
    our minds, and we check the high level details before completing
    the intricacies of the proof. The [admit] term allows us to do
    this. *)

(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars, recommended (palindromes) *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
    c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove that 
       forall l, pal (l ++ rev l).
    - Prove that 
       forall l, pal l -> l = rev l.
*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 5 stars, optional (palindrome_converse) *)
(** Using your definition of [pal] from the previous exercise, prove
    that
     forall l, l = rev l -> pal l.
*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars (subsequence) *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
    [1,2,3]
    is a subsequence of each of the lists
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
    but it is _not_ a subsequence of any of the lists
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove that subsequence is reflexive, that is, any list is a
      subsequence of itself.  

    - Prove that for any lists [l1], [l2], and [l3], if [l1] is a
      subsequence of [l2], then [l1] is also a subsequence of [l2 ++
      l3].

    - (Optional, harder) Prove that subsequence is transitive -- that
      is, if [l1] is a subsequence of [l2] and [l2] is a subsequence
      of [l3], then [l1] is a subsequence of [l3].  Hint: choose your
      induction carefully!
*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars, optional (foo_ind_principle) *)
(** Suppose we make the following inductive definition:
   Inductive foo (X : Set) (Y : Set) : Set :=
     | foo1 : X -> foo X Y
     | foo2 : Y -> foo X Y
     | foo3 : foo X Y -> foo X Y.
   Fill in the blanks to complete the induction principle that will be
   generated by Coq. 
   foo_ind
        : forall (X Y : Set) (P : foo X Y -> Prop),   
          (forall x : X, __________________________________) ->
          (forall y : Y, __________________________________) ->
          (________________________________________________) ->
           ________________________________________________

*)
(** [] *)

(** **** Exercise: 2 stars, optional (bar_ind_principle) *)
(** Consider the following induction principle:
   bar_ind
        : forall P : bar -> Prop,
          (forall n : nat, P (bar1 n)) ->
          (forall b : bar, P b -> P (bar2 b)) ->
          (forall (b : bool) (b0 : bar), P b0 -> P (bar3 b b0)) ->
          forall b : bar, P b
   Write out the corresponding inductive set definition.
   Inductive bar : Set :=
     | bar1 : ________________________________________
     | bar2 : ________________________________________
     | bar3 : ________________________________________.

*)
(** [] *)

(** **** Exercise: 2 stars, optional (no_longer_than_ind) *)
(** Given the following inductively defined proposition:
  Inductive no_longer_than (X : Set) : (list X) -> nat -> Prop :=
    | nlt_nil  : forall n, no_longer_than X [] n
    | nlt_cons : forall x l n, no_longer_than X l n -> 
                               no_longer_than X (x::l) (S n)
    | nlt_succ : forall l n, no_longer_than X l n -> 
                             no_longer_than X l (S n).
  write the induction principle generated by Coq.
  no_longer_than_ind
       : forall (X : Set) (P : list X -> nat -> Prop),
         (forall n : nat, ____________________) ->
         (forall (x : X) (l : list X) (n : nat),
          no_longer_than X l n -> ____________________ -> 
                                  _____________________________ ->
         (forall (l : list X) (n : nat),
          no_longer_than X l n -> ____________________ -> 
                                  _____________________________ ->
         forall (l : list X) (n : nat), no_longer_than X l n -> 
           ____________________

*)
(** [] *)

(** **** Exercise: 2 stars, optional (R_provability) *)
(** Suppose we give Coq the following definition:
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    Which of the following propositions are provable?

    - [R 2 [1,0]]
    - [R 1 [1,2,1,0]]
    - [R 6 [3,2,1,0]]
*)

(** [] *)


(* ##################################################### *)
(* ##################################################### *)
(* ##################################################### *)
(* ##################################################### *)


