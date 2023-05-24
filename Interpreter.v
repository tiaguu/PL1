(** * An Evaluation Function for Imp *)


(** Taken from the chapter Imp:
  https://softwarefoundations.cis.upenn.edu/lf-current/ImpCEvalFun.html

    It might be a good idea to read the chapter before or as you
    develop your solution.
*)

From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
Import Nat.
From Coq Require Import Arith.EqNat.
From FirstProject Require Import Imp Maps.

(* Let's import the result datatype from the relational evaluation file *)
From FirstProject Require Import RelationalEvaluation.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)

(*
Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).
*)

(** 2.1. TODO: Implement ceval_step as specified. To improve readability,
               you are strongly encouraged to define auxiliary notation.
               See the notation LETOPT commented above (or in the ImpCEval chapter).
*)

Declare Scope ceval_step_scope.

Open Scope ceval_step_scope.

Notation "'con' st" :=    (* Notation to simplify writing when result is Some(st, SContinue) *)
  (Some (st, SContinue))
    (at level 70, no associativity)
    : ceval_step_scope.

Notation "'brk' st" :=    (* Notation to simplify writing when result is Some(st, SBreak) *)
  (Some (st, SBreak))
    (at level 70, no associativity)
    : ceval_step_scope.

Notation "'err'" :=       (* Notation to simplify writing when result is None *)
  (None)
    (at level 70, no associativity)
    : ceval_step_scope.

Fixpoint ceval_step (st : state) (c : com) (i : nat): option (state*result) :=
  match i with
  | O => err
  | S i' =>           (* Gas check *)
    match c with
    | <{skip}> => con st (* Skip command, return current state *)
    | <{var := val}> => con (var !-> aeval st val; st) (* Assign new variable *)
    | <{c1; c2}> =>    (* Sequential commands *)
      match ceval_step st c1 i' with   (* Check if first command runs without break *)
      | con st' => ceval_step st' c2 i'   (* If so, do the second command *)
      | brk st' => brk st'     (* If break, skip the second command*)
      | _ => err    (* If evaluation of c1 fails, return None *)
      end
    | <{if b then c1 else c2 end}> => (* If b is true, perform command c1, otherwise do c2 *)
      if (beval st b) then ceval_step st c1 i' else ceval_step st c2 i' 
    | <{while b do c end}> =>
      if (beval st b) then    (* If b is true *)
        match ceval_step st c i' with (* evaluates command c, checks the result *)
        | con st' =>   (* If it returns SContinue, recursively evaluate loop *)
          match ceval_step st' <{while b do c end}> i' with
          | con st'' => con st'' (* If SContinue, propagate SContinue *)
          | brk st'' => con st'' (* if SBreak, propagate SContinue *)
          | _ => err    (* if evaluation fails, returns None *)
          end
        | _ => con st (* Else return current state with SContinue*)
        end
      else con st
    | <{break}> => brk st  (* Return current state with SBreak *)
    end
  end.       

Close Scope ceval_step_scope.

Definition example_command1 : com := 
<{ X := 5;
   Y := 7;
   Z := 0;
   while X > 3 do
     if Y > 5 then break else Y := Y + 1; Z := Z + 2; X := X - 1
   end
end }>. (* COMANDO PRA TESTAR *)


(* The following definition is taken from the book and it can be used to
   test the step-indexed interpreter. *)
Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some (st, _) => Some (st X, st Y, st Z)
  end.

Compute test_ceval (empty_st) (example_command1). (* OBTER VALORES DE OUTPUT *)

Example example_test_ceval :
     test_ceval empty_st

     <{ X := 2;
        if (X <= 1)
        then Y := 3
        else Z := 4
        end }>

     = Some (2, 0, 4).
Proof. reflexivity. Qed.


(** 
  2.2. TODO: Prove the following three properties.
             Add a succint explanation in your own words of why `equivalence1` and `inequivalence1` are valid.
*)
Theorem equivalence1: forall st c,
(exists i0,
forall i1, i1>=i0 ->
ceval_step st <{ break; c }> i1
=
ceval_step st <{ break; skip }> i1
).
Proof.
  exists 2. intros. destruct i1; try lia. destruct i1; try lia. simpl. reflexivity.
Qed.

Theorem inequivalence1: forall st c,
(exists i0,
forall i1, i1>=i0 ->
ceval_step st <{ break; c }> i1
<>
ceval_step st <{ skip }> i1
).
Proof.
  exists 2. intros. destruct i1; try lia. destruct i1; try lia. simpl. 
  injection. discriminate. Qed.

(* NOTA: ainda n ta 100%, mas o resultado ta mm quase lá. N tou a conseguir terminar *)

(* TODO *)
Theorem p1_equivalent_p2: forall st,
  (exists i0,
    forall i1, i1>=i0 ->
      ceval_step st p1 i1 = ceval_step st p2 i1
  ).
Proof.
  exists 6. intros. 
  destruct i1; try lia. 
  destruct i1; try lia. 
  destruct i1; try lia. 
  destruct i1; try lia. 
  destruct i1; try lia.
  destruct i1; try lia. simpl. reflexivity. 
Qed. 
  
