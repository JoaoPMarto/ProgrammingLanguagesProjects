From FirstProject Require Import Maps Imp.
From Coq Require Import Lists.List. Import ListNotations.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".


(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** We'll use the notation [st1 / q1 =[ c ]=> st2 / q2 / r] for the [ceval] relation:
    [st1 / q1 =[ c ]=> st2 / q2 / r] means that executing program [c] in a starting
    state [st1] with continuations [q1] results in an ending state [st2] with unexplored
    continuations [q2]. Moreover the result of the computation will be [r].*)

(* Type of result *)
Inductive result : Type :=
| Success
| Fail.

(* Notation that we use *)
Reserved Notation "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r"
(at level 40,
 q1 constr at next level,
 c custom com at level 99, 
 st2 constr at next level,
 q2 constr at next level,
 r constr at next level).

(* 
3: Define the relational semantics (ceval) to support the required constructs.
*)
Inductive ceval : com -> state -> list (state * com) -> result -> state -> list (state * com) -> Prop :=
  | E_Skip : forall st q,
    st / q =[ skip ]=> st / q / Success
  | E_Asgn : forall st q a n x suc,
    aeval st a = n ->
    st / q =[ x:= a ]=> (x !-> n ; st) / q / suc
  | E_Seq : forall c1 c2 st st' st'' q suc,
    st / q =[ c1 ]=> st' / q / suc ->
    st' / q =[ c2 ]=> st'' / q / suc ->
    st / q =[ c1; c2 ]=> st'' / q / suc
  | E_IfTrue : forall st st' b c1 c2 q suc,
    beval st b = true ->
    st / q =[ c1 ]=> st' / q / suc ->
    st / q =[ if b then c1 else c2 end ]=> st' / q / suc
  | E_IfFalse : forall st st' b c1 c2 q suc,
    beval st b = false ->
    st / q =[ c2 ]=> st' / q / suc ->
    st / q =[ if b then c1 else c2 end ]=> st' / q / suc
  | E_WhileFalse : forall st b c q suc,
    beval st b = false ->
    st / q =[ while b do c end ]=> st / q / suc
  | E_WhileTrue : forall st st' st'' b c q suc,
      beval st b = true ->
      st / q =[ c ]=> st' / q / suc ->
      st' / q =[ while b do c end ]=> st'' / q / suc ->
      st / q =[ while b do c end ]=> st'' / q / suc
  | E_NonDet_X1 : forall st st' q q' x1 x2 suc, 
      st / q =[ x1 ]=> st' / q' / suc -> 
      st / q =[ x1 !! x2 ]=> st' / ((st, x2) :: q') / suc
  | E_NonDet_X2 : forall st st' q q' x1 x2 suc, 
      st / q =[ x2 ]=> st' / q' / suc -> 
      st / q =[ x1 !! x2 ]=> st' / ((st, x1) :: q') / suc
  | E_CondGuardTrue : forall st b q c st' suc,
      beval st b = true ->
      st / q =[ c ]=> st' / q / suc ->
      st / q =[ b -> c ]=> st' / q / suc
  | E_CondGuardFalse : forall st b q c,
      beval st b = false ->
      st / q =[ b -> c ]=> empty_st / q / Fail
where "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r" := (ceval c st1 q1 r st2 q2).


(*

Example ceval_example1:
  empty_st =[
     X := 2;
     if (X ≤ 1)
       then Y := 3
       else Z := 4
     end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (X !-> 2).
  - (* assignment command *)
    apply E_Asgn. reflexivity.
  - (* if command *)
    apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed.

*)



(**
  3.1: Use the new relational semantics to prove the examples
             ceval_example_if, ceval_example_guard1, ceval_example_guard2,
             ceval_example_guard3 and ceval_example_guard4.
*)

(* repeat econstructor; reflexivity. *)
Example ceval_example_if:
empty_st / [] =[
X := 2;
if (X <= 1)
  then Y := 3
  else Z := 4
end
]=> (Z !-> 4 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq with (X !-> 2).
  - apply E_Asgn. reflexivity.
  - apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed.



Example ceval_example_guard1:
empty_st / [] =[
   X := 2;
   (X = 1) -> X:=3
]=> (empty_st) / [] / Fail.
Proof.
  apply E_Seq with (X !-> 2).
  - apply E_Asgn. reflexivity.
  - apply E_CondGuardFalse.
    + reflexivity.
Qed. 

Example ceval_example_guard2:
empty_st / [] =[
   X := 2;
   (X = 2) -> X:=3
]=> (X !-> 3 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq with (X !-> 2).
  - apply E_Asgn. reflexivity.
  - apply E_CondGuardTrue.
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed. 

(*
Example ceval_example_guard3: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
    eexists.
    eapply E_Seq.
Abort.
(* Qed. *)
    
Example ceval_example_guard4: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
  (* TODO *)
Abort.

*)


(* 3.2. Behavioral equivalence *)

Definition cequiv_imp (c1 c2 : com) : Prop := 
forall (st st' : state) q q' result,
(st / q =[ c1 ]=> st' / q' / result) ->
exists q'', 
(st / q =[ c2 ]=> st' / q'' / result).

Definition cequiv (c1 c2 : com) : Prop :=
cequiv_imp c1 c2 /\ cequiv_imp c2 c1.

Infix "==" := cequiv (at level 99).


(**
  3.2: Prove the properties below.
*)

(*
Definition ccequiv (c1 c2 : com) : Prop :=
  forall (st st' : state) q q' q'' res,
  (st / q =[ c1 ]=> st' / q' / res) <-> (st / q =[ c2 ]=> st' / q'' / res).

Theorem skip_left : forall c,
  ccequiv <{ skip; c }> c.
Proof.
  intros c st st' q q' q'' res.
  split; intros H.
  - 
    inversion H2. subst.
    assumption.
  - 
    apply E_Seq with st.
    + apply E_Skip.
    + assumption.
Qed.
 *)

Lemma cequiv_ex1:
<{ X := 2; X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  split; intros st st' q q' res H; eexists.
Admitted.
(*   - eapply E_Asgn. *)
(*   - *)
(*     eapply E_Seq. *)
(*     + apply E_Asgn. reflexivity. *)
(*     + apply E_CondGuardTrue. *)
(*       ++ reflexivity. *)
(*       ++ apply E_Skip. *)
(* Qed. *)

Lemma cequiv_ex2:
<{ (X := 1 !! X := 2); X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
Admitted.
(* Qed. *)


Lemma choice_idempotent: forall c,
<{ c !! c }> == <{ c }>.
Proof.
  split; intros st st' q q' res H.
  - inversion H. subst. exists q'0. eapply H7. exists q'0. assumption.
  - eexists. eapply E_NonDet_X1. apply H.
Qed.

Lemma choice_comm: forall c1 c2,
<{ c1 !! c2 }> == <{ c2 !! c1 }>.
Proof.
  intros.
  split; intros st st' q q' res H.
  - inversion H. subst. eexists. apply E_NonDet_X2. eapply H7. eexists. apply E_NonDet_X1. eapply H7.
  - inversion H. subst. eexists. apply E_NonDet_X2. eapply H7. eexists. apply E_NonDet_X1. eapply H7.
Qed.

Lemma choice_assoc: forall c1 c2 c3,
<{ (c1 !! c2) !! c3 }> == <{ c1 !! (c2 !! c3) }>.
Proof.
  intros.
  split; intros st st' q q' res H.
  Admitted.
  (* - inversion H. subst. eexists. apply E_NonDet_X1. apply E_NonDet_X1 in H7. *)
  (* - eexists. apply E_NonDet_X2. apply E_NonDet_X2. inversion H; subst. *)
(* Qed. *)


Lemma choice_seq_distr_l: forall c1 c2 c3,
<{ c1 ; (c2 !! c3)}> == <{ (c1;c2) !! (c1;c3) }>.
Proof.
  intros.
  split; intros st st' q q' res H.
  - inversion H. subst. apply E_NonDet_X1 with (x2 := c3) in H8. eexists. eapply E_NonDet_X1. eapply E_Seq.
    -- apply H2.
Admitted.
(* Qed. *)

Ltac choice_congruence_solve_nondet H H' E_NonDet :=
    apply H in H'; destruct H' as [q'' H']; eexists; apply E_NonDet; apply H'.

Lemma choice_congruence: forall c1 c1' c2 c2',
c1 == c1' -> c2 == c2' ->
<{ c1 !! c2 }> == <{ c1' !! c2' }>.
Proof.
  intros c1 c1' c2 c2' H1 H2.
  split; intros st st' q q' res H'.
  - inversion H'; subst.
    -- choice_congruence_solve_nondet H1 H8 E_NonDet_X1.
    -- choice_congruence_solve_nondet H2 H8 E_NonDet_X2.
  - inversion H'; subst.
    -- choice_congruence_solve_nondet H1 H8 E_NonDet_X1.
    -- choice_congruence_solve_nondet H2 H8 E_NonDet_X2.
Qed.
