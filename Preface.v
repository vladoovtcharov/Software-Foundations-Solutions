(** * Preface *)

(* $Date: 2012-07-23 16:26:25 -0400 (Mon, 23 Jul 2012) $ *)

(** This electronic book is a one-semester course on _Software
    Foundations_ -- the mathematical theory of programming and
    programming languages -- suitable for graduate or upper-level
    undergraduate students.  It develops basic concepts of functional
    programming, logic, operational semantics, lambda-calculus, and
    static type systems, using the Coq proof assistant.  

    The main novelty of the course is that the development is
    formalized and machine-checked: the text is literally a script for
    the Coq proof assistant.  It is intended to be read hand-in-hand
    with the accompanying Coq source file in an interactive session
    with Coq.  All the details of the lectures are fully developed in
    Coq, and the exercises are designed to be worked using Coq.

    The files are organized into a sequence of core chapters, covering
    about one semester's worth of material and organized into a
    coherent linear narrative, plus several "appendices" covering
    additional topics. *)


(* ###################################################################### *)
(** * Overview *)

(** The course weaves together several fundamental themes:
  - _Logic_ as the mathematical basis for software engineering:
<<
                logic                        calculus
         --------------------   =   ----------------------------
         software engineering       mechanical/civil engineering
>>
         In particular, inductively defined sets and relations and
         inductive proofs about them are ubiquitous in all of computer
         science.  The course examines them from many angles.

  - _Functional programming_, an increasingly important part of
    the software developer's bag of tricks:

       - Advanced programming idioms in mainstream software
         development methodologies are increasingly incorporating
         ideas from functional programming.

       - In particular, using persistent data structures and avoiding
         mutable state enormously simplifies many concurrent
         programming tasks.

  - _Foundations of programming languages_ (the second part of the
    course):

        - Notations and techniques for rigorously describing and
          stress-testing new programming languages and language
          features.  (Designing new programming languages is a
          surprisingly common activity!  Most
          large software systems include subsystems that are basically
          programming languages -- think of regular expressions,
          command-line formats, preference and configuration files,
          SQL, Flash, PDF, etc., etc.)

        - A more sophisticated understanding of the everyday tools
          used to build software... what's going on under the hood of
          your favorite programming language.

  - _Coq_, an industrial-strength proof assistant:

       - Proof assistants are becoming more and more popular in both
         software and hardware industries.  Coq is not the only one
         out there, but learning one thoroughly will give you a big
         advantage in coming to grips with another.
*)

(* ###################################################################### *)
(** * Practicalities *)

(* ###################################################################### *)
(** ** Chapter Dependencies *)

(** A diagram of the dependencies between chapters and some suggested
    paths through the material can be found in the file [deps.html]. *)

(* ###################################################################### *)
(** ** Required Background *)

(** These notes are intended to be accessible to a broad range of
    readers, from advanced undergraduates to PhD students and
    researchers.  They assume little specific background in
    programming languages or logic.  However, a degree of mathematical
    maturity will be helpful. *)


(* ###################################################################### *)
(** * Coq *)

(** Our laboratory for this course is the Coq proof assistant.  
    Coq can be seen as a combination of two things:
      - a simple and slightly idiosyncratic (but, in its way,
        extremely expressive) _programming language_, together with
      - a set of tools for stating _logical assertions_ (including
        assertions about the behavior of programs) and marshalling
        evidence of their truth.
    We will be investigating both aspects in tandem.  
*)

(* ###################################################################### *)
(** ** System Requirements *)

(** Coq runs on Windows and pretty much all flavors of Unix (including
    Linux and OS X).  You will need:
       - A current installation of Coq, available from the Coq home
         page.  (Everything is known to compile with 8.3.)
       - An IDE for interacting with Coq.  Currently, there are two choices:
           - Proof General is an Emacs-based IDE.  It tends to be
             preferred by users who are already comfortable with
             Emacs.  It requires a separate installation (google
             "Proof General").
           - CoqIDE is a simpler stand-alone IDE.  It is distributed
             with Coq, but on some platforms compiling it involves
             installing additional packages for GUI libraries and
             such. *)

(* ###################################################################### *)
(** ** Access to the Coq files *)

(** A tar file containing the full sources for the "release version"
    of these notes (as a collection of Coq scripts and HTML files) is
    available here:
<<
        http://www.cis.upenn.edu/~bcpierce/sf   
>>
    If you are using the notes as part of a class, you may be given
    access to a locally extended version of the files, which you
    should use instead of the release version.
*)

(* ###################################################################### *)
(** * Exercises *)

(** Each chapter of the notes includes numerous exercises.  Some are
    marked "optional", some "recommended."  Doing just the
    non-optional exercises should provide good coverage of the
    material in approximately six or eight hours of study time (for
    the longer chapters).

    The "star ratings" for the exercises can be interpreted as follows: 

       - One star: easy exercises that for most readers should take
         only a minute or two.  None of these are explicitly marked
         "Recommended"; rather, _all_ of them should be considered as
         recommended: readers should be in the habit of working them
         as they reach them.

       - Two stars: straightforward exercises (five or ten minutes).

       - Three stars: exercises requiring a bit of thought (fifteen 
         minutes to half an hour).

       - Four stars: more difficult exercises (an hour or two).
*)

(* ###################################################################### *)
(** * Recommended Reading *)

(** Some suggestions for supplemental texts can be found in the
    [Postscript] chapter. *)

(* ###################################################################### *)
(** * Translations *)

(** Thanks to the efforts of a team of volunteer translators, _Software 
    Foundations_ can now be enjoyed in Japanese:

      - http://proofcafe.org/sf
*)

(* ###################################################################### *)
(** * For Instructors *)

(** If you intend to use these materials in your own course, you will
    undoubtedly find things you'd like to change, improve, or add.
    Your contributions are welcome!

    Please send an email to Benjamin Pierce, and we'll set you up with
    read/write access to our subversion repository and developers'
    mailing list; in the repository you'll find a [README] with further
    instructions. *)



