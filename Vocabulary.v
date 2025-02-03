Require Import EDiagrams.FiniteSets.


(* Here, the concepts of a participant identifier and
   an event tag is introduced *)

Definition PID : Set := nat.  (* The type is inhabited by participant IDs *)
Coercion unwrap_PID (p : PID) : nat := p.

Instance enumPID : Enum PID.
Proof.
  pose (tonat := fun n : PID => n).
  constructor 1 with tonat. compute. auto.
Defined.


Definition TimeStamp : Set := nat.  (* The type is inhabited by timestamps *)
Coercion unwrap_TS (t : TimeStamp) : nat := t.

Instance enumTS : Enum TimeStamp.
Proof.
  pose (tonat := fun n : TimeStamp => n).
  constructor 1 with tonat. compute. auto.
Defined.


Record ETag : Set :=
(* The type is inhabited by event tags *) 
{ pid : PID (* the participant that observes the event *)
; num : nat (* the number of the event in the ledger of the participant *)
}.

(*
  Local Definition to2nat (e : EventTag) (*
    transforms an event tag into a pair of natural numbers *) : nat * nat :=
  let '{| pid := p; num := n |} := e in
  let 'Pid ip := p in (ip, n).

  Local Definition tonat' (*
    encodes an event tag using Cantor pairing function *) : EventTag -> nat :=
  fun e => to_nat (to2nat e).


  Instance Enum_EventTag (* EventTag is an enumerable set *) : Enum EventTag.
  Proof.
    constructor 1 with (tonat := tonat'). unfold tonat'.
    intros e1 e2 H.
    assert (H' : to2nat e1 = to2nat e2). {
      now apply (to_nat_inj (to2nat e1) (to2nat e2)). }
    destruct e1 as (p1, n1), e2 as (p2, n2). simpl in H'.
    destruct p1 as (ip1), p2 as (ip2).
    f_equal; f_equal; now injection H'.
  Defined.
*)

