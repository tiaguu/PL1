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

(* Prova que se ao avaliar um programa com i1 de gas, se esse programa executa e 
 devolve Some (st', res), se usarmos mais gas (i2>=i1), vamos sempre obter o mesmo 
 resultado *)

Theorem ceval_step_more: forall i1 i2 st st' res c,
i1 <= i2 ->
ceval_step st c i1 = Some (st', res) ->
ceval_step st c i2 = Some (st', res).
Proof.
  induction i1 as [|i1']; intros i2 st st' res c Hle Hceval.
    - simpl in Hceval. discriminate Hceval.
    - destruct i2 as [|i2'].
      + inversion Hle.
      + assert (Hle': i1' <= i2') by lia. destruct c.
        * simpl in Hceval. inversion Hceval. reflexivity.
        * simpl in Hceval. inversion Hceval. reflexivity.
        * simpl in Hceval. simpl. assumption.
        * simpl in Hceval. simpl. destruct (ceval_step st c1 i1') eqn: Heqst1'o.
          ** assert (prop: ceval_step st c1 i2' = Some p).
            {
              destruct p as [st'' r]. apply IHi1' with (st':=st'')(res := r).
                + assumption.
                + assumption.
            }
          rewrite prop. destruct p. destruct r.
          ++ apply IHi1'; try assumption.
          ++ apply Hceval.
          ** discriminate.
        * simpl in Hceval. simpl. destruct (beval st b); apply (IHi1' i2') in Hceval;
        assumption.
        * simpl in Hceval. simpl. destruct (beval st b); try assumption.
          destruct (ceval_step st c i1') eqn: Heqst1'o.
          ** destruct p; destruct r; apply (IHi1' i2') in Heqst1'o; try assumption.
          *** rewrite -> Heqst1'o. 
Admitted.

(* NOTA: faltou apenas em ceval_step_more acabar de provar o caso do while*)


(* ################################################################# *)
(** * Relational vs. Step-Indexed Evaluation *)

(** As for arithmetic and boolean expressions, we'd hope that
    the two alternative definitions of evaluation would actually
    amount to the same thing in the end.  This section shows that this
    is the case. *)

(* Prova que se existe um dado valor de gas que corre o programa c e devolve Some(st',res) 
 avaliando com a função ceval_step, então para a implementação relational, o resultado será
 o mesmo*)

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

- (*"i = 0 -- contradictory".*)
    intros c st st' res H. inversion H.

- (*"i = S i'".*)
    intros c st st' res H.
    destruct c;
      simpl in H; inversion H; subst; clear H.
      + (*"SKIP".*) apply E_Skip.
      + (*"BREAK".*) apply E_Break.
      + (*"ASGN".*) apply E_Asgn. reflexivity.

      + (*"SEQ".*)
        destruct (ceval_step st c1 i') eqn:Heqr1.
        * (*"Evaluation of r1 terminates normally".*)
          apply E_Seq with st.
            (* There are 2 subgoals here but we could not prove them.*)
            ** admit.
            ** admit.
        * (*"Otherwise -- contradiction".*)
          inversion H1.
      + (*"IF".*)
          destruct (beval st b) eqn:Heqr.
          * (* beval st b = true *)
            apply E_IfTrue. 
              ** rewrite Heqr. reflexivity.
              ** apply IHi' with (res := res) (st' := st'). assumption.
          * (* beval st b = false *)
            apply E_IfFalse.
              ** rewrite Heqr. reflexivity.
              ** apply IHi' with (res := res) (st' := st'). assumption.
      + (*"WHILE".*)
        destruct (beval st b) eqn:Heqr.
        * (* beval st b = true *)
          destruct (ceval_step st c i') eqn:Heqr1.
           (* Evaluation of c1 terminates normally *)
            ** admit.
            ** admit.
          * (* Evaluation of c1 does not terminate *)
            inversion H1. admit.
           (* beval st b = false *)
Admitted.

(** 
  TODO: For the following proof, you'll need [ceval_step_more] in a
  few places, as well as some basic facts about [<=] and [plus]. *)

(* Prova o inverso da prova anterior: se conseguimos avaliar um programa partindo dum estado st,
com a relational, obtendo Some(st',res), entao existe um valor para gas tal que com a step
 implementation obtemos o mesmo resultado (Some(st',res)) *)

Theorem ceval__ceval_step: forall c st st' res,
    st =[ c ]=> st' / res ->
    exists i, ceval_step st c i = Some (st', res).
Proof.
intros c st st' res Hce.
  induction Hce; subst.
  
  - (* E_Skip *)
    exists 1. simpl. reflexivity.
  
  - (* E_Break *)
    exists 1. simpl. reflexivity.
  
  - (* E_Asgn *)
    exists 1. simpl. reflexivity.
  
  - (* E_Seq *)
    admit.

  - (* E_SeqBreak *)
    admit.
  
  - (* E_IfTrue *)
    admit.
  
  - (* E_IfFalse *)
    admit.
  
  - (* E_While1 *)
    admit.
  
  - (* E_While2 *)
    admit.

  - (* E_While3 *)
    admit.
Admitted.

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

(*
Temos como objectivo provar que a evaluation e deterministica, para isso queremos provar que,
 a relational e a step-indexed evaluations funcionam da mesma maneira.
Introduzimos duas hipoteses (He1 e He2) em que 'st' avaliado por 'c' da origem a 
'st1' e 'res1' para He1 e 'st2' e 'res2' para He2.
Aplicamos a Relational Evaluation ('ceval__ceval_step') as duas hipoteses.
Estraimos i1 e i2, que sao os numero de passos das evaluations e E1 e E2, que sao
 os comandos restantes depois da evaluation.
De seguida aplicamos a Step-Indexed Evaluation ('ceval_step_more') a E1 e E2 com o numero de
 passos a 'i1+i2'.
O resultado destas duas evaluations fica o mesmo, em que 'st1' igual a 'st2',
 que fica de acordo com a conclusao do teorema.
 *)

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