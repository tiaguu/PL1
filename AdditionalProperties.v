(* ################################################################# *)
(** * Additional Properties 

      It might be a good idea to read the relevant book chapters/sections before or as you
      develop your solution. The properties below are discussed and some of them proved
      for the original Imp formulation.
*)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From FirstProject Require Import Maps Imp Interpreter RelationalEvaluation.
Set Default Goal Selector "!".


(**
  3.2. TODO: Prove all the properties below that are stated without proof.
             Add a succint comment before each property explaining the property in your own words.
*)

(* ################################################################# *)
(** * Property of the Step-Indexed Interpreter *)

Theorem ceval_step_more: forall i1 i2 st st' res c,
i1 <= i2 ->
ceval_step st c i1 = Some (st', res) ->
ceval_step st c i2 = Some (st', res).
Proof.


(*   intros i1 i2 st st' res c Hleq Hstep.
  generalize dependent i2.
  induction i2; intros.
  - inversion Hleq; subst. assumption.
  - destruct i1.
    + simpl in Hstep. inversion Hstep; subst.
    + destruct i2 as [| i2'].
      * inversion Hleq.
        ** rewrite <- Hstep. apply Hleq. 
      * apply le_S_n in Hleq. assumption.
      * assumption. *)

 induction i1 as [|i1']; intros i2 st st' res c Hle Hceval.
  - simpl in Hceval. discriminate Hceval.
  - destruct i2 as [|i2'].
    + inversion Hle.
    + assert (Hle': i1' <= i2') by lia.
    destruct c.
      * simpl in Hceval. inversion Hceval.
        reflexivity.
      * simpl in Hceval. inversion Hceval.
        reflexivity.
      * simpl in Hceval. simpl. assumption.
      * simpl in Hceval. simpl. destruct (ceval_step st c1 i1') eqn:Heqst1'o. 
          ** assert (prop: ceval_step st c1 i2' = Some p).
          {
              inversion Hle.
              + subst. rewrite <- Heqst1'o. try reflexivity.
              + subst. rewrite <- Heqst1'o. 
          }
  






        ++ destruct (ceval_step st c1 i1') eqn:Heqst1'o.
    *** simpl in H. apply H.
        destruct (ceval_step st c1 i1') eqn:Heqst1'o.
        ** (*"st1'o = Some".*)
          apply (IHi1' i2') in Heqst1'o; try assumption.
          rewrite Heqst1'o. simpl. simpl in Hceval.
          apply (IHi1' i2') in Hceval; try assumption.
         (*"st1'o = None".*)
          inversion Hceval. 
  (* TODO *)
 *)Qed.



(* ################################################################# *)
(** * Relational vs. Step-Indexed Evaluation *)

(** As for arithmetic and boolean expressions, we'd hope that
    the two alternative definitions of evaluation would actually
    amount to the same thing in the end.  This section shows that this
    is the case. *)

Theorem ceval_step__ceval: forall c st st' res,
    (exists i, ceval_step st c i = Some (st', res)) ->
    st =[ c ]=> st' / res.
Proof.
intros c st st' res H.
inversion H as [i E].
clear H.
generalize dependent res.
generalize dependent st'.
generalize dependent st.
generalize dependent c.
induction i as [| i' ].

(* TODO *)

Qed.

(** 
  TODO: For the following proof, you'll need [ceval_step_more] in a
  few places, as well as some basic facts about [<=] and [plus]. *)

Theorem ceval__ceval_step: forall c st st' res,
    st =[ c ]=> st' / res ->
    exists i, ceval_step st c i = Some (st', res).
Proof.
  (* TODO *)
Qed. 



(* Note that with the above properties, we can say that both semantics are equivalent! *)

Theorem ceval_and_ceval_step_coincide: forall c st st' res,
    st =[ c ]=> st' / res
<-> exists i, ceval_step st c i = Some (st', res).
Proof.
intros c st st'.
split. 
 - apply ceval__ceval_step. 
 - apply ceval_step__ceval.
Qed.


(* ################################################################# *)
(** * Determinism of Evaluation Again *)

(** Using the fact that the relational and step-indexed definition of
  evaluation are the same, we can give a short proof that the
  evaluation _relation_ is deterministic. *)

(* TODO: Write/explain the following proof in natural language, 
         using your own words. *)  

Theorem ceval_deterministic' : forall c st st1 st2 res1 res2,
   st =[ c ]=> st1 / res1 ->
   st =[ c ]=> st2 / res2 ->
   st1 = st2.
Proof.
intros c st st1 st2 res1 res2 He1 He2.
apply ceval__ceval_step in He1.
apply ceval__ceval_step in He2.
inversion He1 as [i1 E1].
inversion He2 as [i2 E2].
apply ceval_step_more with (i2 := i1 + i2) in E1.
 - apply ceval_step_more with (i2 := i1 + i2) in E2.
  -- rewrite E1 in E2. inversion E2. reflexivity.
  -- lia. 
 - lia.  
 Qed.