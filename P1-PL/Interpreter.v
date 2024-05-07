From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import List.
Import ListNotations.
From FirstProject Require Import Imp Maps.


Inductive interpreter_result : Type :=
  | Success (s: state * (list (state*com)))
  | Fail
  | OutOfGas.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)

Notation "'CHECKSUC' x y <== e1 'IN' e2"
   := (match e1 with
       | Success (x, y) => e2
       | a => a
       end)
   (at level 10, x at next level, y at next level, e1 at next level, e2 at next level).

(**
  2.1. Implement ceval_step as specified. To improve readability,
             you are strongly encouraged to define auxiliary notation.
             See the notation LETOPT in the ImpCEval chapter.
*)
Fixpoint ceval_step (st : state) (c : com) (continuation: list (state * com)) (i : nat)
                    : interpreter_result :=
  match i with
  | O => OutOfGas
  | S i' => 
      match c with
      | <{ skip }> =>
          Success (st, continuation)
      | <{ l := a1 }> =>
          Success ((l !-> aeval st a1 ; st), continuation)
      | <{ c1 ; c2 }> =>
          match c1 with 
          | <{ x1 !! x2 }> =>
            match ceval_step st <{ x1 ; c2 }> ((st, x2) :: continuation) i' with
            | Fail => 
               match i' with
               | O => OutOfGas
               | S i'' => ceval_step st <{ x2 ; c2 }> (tail continuation) i''
               end
            | a => a
            end
          | _ => 
            CHECKSUC st' cont' <== (ceval_step st c1 continuation i') IN
              (ceval_step st' c2 cont' i')
          end
      | <{ if b then c1 else c2 end }> =>
          if (beval st b) then 
            ceval_step st c1 continuation i'
          else 
            ceval_step st c2 continuation i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1) then
            CHECKSUC st' cont' <== (ceval_step st c1 continuation i') IN
              (ceval_step st' c cont' i')
          else 
            Success (st, continuation)
      | <{ x1 !! x2 }> =>
          ceval_step st x1 ((st, x2) :: continuation) i'
      | <{ b -> c }> => 
          if (beval st b) then
            ceval_step st c (tail continuation) i'
          else 
            Fail
      end
  end.

(* Helper functions that help with running the interpreter *)
Inductive show_result : Type :=
  | OK (st: list (string*nat))
  | KO
  | OOG.

Open Scope string_scope.
Definition run_interpreter (st: state) (c:com) (n:nat) :=
  match (ceval_step st c [] n) with
    | OutOfGas => OOG
    | Fail => KO
    | Success (st', _) => OK [("X", st' X); ("Y", st' Y); ("Z", st' Z)]
  end.

(* Tests are provided to ensure that your interpreter is working for these examples *)
Example test_1: 
  run_interpreter (X !-> 5) <{skip}> 1 = OK [("X", 5); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_2: 
  run_interpreter (X !-> 5) <{ X:= X+1 }> 1 = OK [("X", 6); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_3: 
  run_interpreter (X !-> 5) <{ X:= X+1; X:=X+2; Y:=Y+1 }> 3 = OK [("X", 8); ("Y", 1); ("Z", 0)].
Proof. auto. Qed.

Example test_4: 
  run_interpreter (X !-> 5) <{ X:= X+1; X:=X+2; Y:=Y+1 }> 2 = OOG.
Proof. auto. Qed.

Example test_5:
  run_interpreter (X !-> 5) <{ X:= X+1; X=5 -> skip }> 2 = KO.
Proof. auto. Qed.

Example test_6:
  run_interpreter (X !-> 5) <{ X:= X+1; X=5 -> skip }> 1 = OOG.
Proof. auto. Qed.

Example test_7:
  run_interpreter (X !-> 5) <{ X:= X+1; X=6 -> skip }> 3 = OK [("X", 6); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

(*

  This is currentl working fine because I added an i decrease when the first clause of 
  non-det choice fails. @TODO review with prof in lab to see if this makes sense

*)
Example test_8:
  run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X = 2) -> X:=3 }> 4 = OOG.
Proof. auto. Qed.

Example test_9:
  run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X = 2) -> X:=3 }> 5 = OK [("X", 3); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_10:
  run_interpreter (X !-> 5) <{ (X:=1 !! (X:=2; Y:=1));X=2 -> skip }> 5 = OK [("X", 2); ("Y", 1); ("Z", 0)].
Proof. auto. Qed.

Example test_11:
  run_interpreter (X !-> 5) 
  <{  while ~(X = 0) do 
        X:=X-1; Y:=Y+1
      end;
      Y=5 -> skip
  }>
  8 
  = OK [("X", 0); ("Y", 5); ("Z", 0)].
Proof. auto. Qed.



(**
  2.2. TODO: Prove p1_equals_p2. Recall that p1 and p2 are defined in Imp.v


Theorem p1_equals_p2: forall st cont,
  (exists i0,
    (forall i1, i1 >= i0 -> ceval_step st p1 cont i1 = ceval_step st p2 cont i1)).
Proof.
  intros st cont. induction p1 as [].
  induction p2 as [].
  - split.
Qed.

*)


(**
  2.3. TODO: Prove ceval_step_more.


Theorem ceval_step_more: forall i1 i2 st st' c cont cont',
  i1 <= i2 ->
  ceval_step st c cont i1 = Success (st', cont') ->
  ceval_step st c cont i2 = Success (st', cont').
Proof.
  (* TODO *)
Qed.
*)
