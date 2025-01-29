Require Import EDiagrams.FiniteSets.
Require Import EDiagrams.Diagram.
Require Import EDiagrams.Vocabulary.
Require Import Coq.Arith.PeanoNat.
Require Import Lists.List.


Section CausalOrder.
Variable dgm : Diagram.

  Inductive happen_before : ETag -> ETag -> Prop :=
  | hbline :
    (* if two events have the same source then their causal order is
       the order of their numbers in the local ledger of their source *)
      forall e1 e2, event dgm e1 -> event dgm e2 ->
        pid e1 = pid e2 -> num e1 < num e2 -> happen_before e1 e2
  | hbcomm :
    (* the sending event of a message causes the receiving of this message *)
      forall e1 e2, sending dgm e2 = Some e1 -> happen_before e1 e2
  | hbtrans :
    (* the causal order is transitive *)
      forall e1 e2 e3,
        happen_before e1 e2 -> happen_before e2 e3 -> happen_before e1 e3.


  Lemma happen_before_event :
  (*  *)
    forall e1 e2, happen_before e1 e2 -> event dgm e1 /\ event dgm e2.
  Proof.
    destruct (diagram_guarantees dgm).
    intros.
    induction H; split; trivial.
    - now apply sending_cod with e2.
    - apply sending_dom. intro H'. rewrite H in H'. discriminate H'.
    - exact (proj1 IHhappen_before1).
    - exact (proj2 IHhappen_before2).
  Qed.
End CausalOrder.

Notation "z [ x --> y ]" := (happen_before z x y)  (at level 70).

Section NoIrreflexivity.

  Example deadlock : Diagram.
  Proof.
    pose (participants' := @fromlist PID _ (1 :: 0 :: nil)).
    pose (event' := fun e => match e with
            | {| pid := S (S _) |} => False
            | _ => True
            end).
    pose (sending' := fun e => match e with
            | {| num := S _ |} => None
            | {| pid := 0 |} => Some {| pid := 1; num := 1 |}
            | {| pid := 1 |} => Some {| pid := 0; num := 1 |}
            | _ => None
            end).
    assert (H : aDiagram participants' event' sending'). {
      constructor.
      - constructor.
      - intros. destruct e. subst participants'. simpl.
        case pid as [| k].
        + now left.
        + case k as [| k']; right; now left.
      - intros. destruct e as (p, m). compute in H0 |-*.
        trivial.
      - intros. destruct e as (p, n).
        case p as [| k]; try (now compute).
        case k as [| k']; try (now compute).
        destruct n as [| n']; compute in H; contradiction.
      - intros. destruct e as (p, n).
        case p as [| k]; destruct n as [| n']; try discriminate H.
        + simpl in H.
          assert (e' = {| pid := 1; num := 1 |}). { now injection H. }
          rewrite H0. now compute.
        + simpl in H. case k as [| k']; try discriminate H.
          assert (e' = {| pid := 0; num := 1 |}). { now injection H. }
          rewrite H0. now compute.
        + destruct k as [| k']; discriminate H.
      - intros. destruct e' as (p, n). simpl.
        destruct p as [| k]; destruct n as [| n'].
        + compute in H.
          assert (e = {| pid := 1; num := 1 |}). { now injection H. }
          rewrite H0. compute. intro. discriminate H1.
        + destruct n' as [| n'']; try discriminate H.
        + destruct k as [| k']; try discriminate H.
          compute in H.
          assert (e = {| pid := 0; num := 1 |}). { now injection H. }
          rewrite H0. compute. intro. discriminate H1.
        + destruct n' as [| n'']; compute in H; destruct k as [| k'];
          try discriminate H.
      - intros * H1 H2.
        destruct e as (p, n), e' as (p1, n1), e'' as (p2, n2).
        destruct n1 as [| n1']; compute in H1;
        destruct n2 as [| n2']; compute in H2.
        + destruct p1 as [| k1], p2 as [| k2]; trivial.
          destruct k2 as [| k2']; rewrite H2 in H1; discriminate H1.
          destruct k1 as [| k1']; rewrite H2 in H1; discriminate H1.
          destruct k1 as [| k1']; destruct k2 as [| k2']; trivial;
          discriminate H1 || discriminate H2.
        + destruct p2 as [| k2];
          discriminate H2 || destruct k2 as [| k2']; discriminate H2.
        + destruct p1 as [| k1];
          discriminate H1 || destruct k1 as [| k1']; discriminate H1.
        + destruct p1 as [| k1], p2 as [| k2];
          try (discriminate H1 || discriminate H2).
          destruct k1 as [| k1']; discriminate H1. }
    constructor 1 with participants' event' sending'; trivial.
  Defined.

  Lemma deadlock_presence :
    deadlock[{| pid := 0; num := 0|} --> {| pid := 0; num := 0|}].
  Proof.
    constructor 3 with (e2 := {| pid := 0; num := 1 |}).
    - constructor 1; compute; trivial.
    - constructor 3 with (e2 := {| pid := 1; num := 0 |}).
      + constructor 2. now compute.
      + constructor 3 with (e2 := {| pid := 1; num := 1 |}).
        * constructor 1; compute; trivial.
        * constructor 2. now compute.
  Qed.
End NoIrreflexivity.


Section Clocks.
Variable dgm : Diagram.

  Class aClock (ts : ETag -> nat -> Prop) : Prop :=
  { clock_dom : forall e, exists n, ts e n <-> event dgm e
  ; clock_func : forall e n m, ts e n -> ts e m -> n = m
  ; clock_mono : forall e1 e2 n1 n2,
      dgm[e1 --> e2] -> ts e1 n1 -> ts e2 n2 -> n1 < n2
  }. 

Definition Clock := { clock : ETag -> nat -> Prop | aClock clock }.

End Clocks.


Theorem clock_irrefl : forall dgm, (exists ts, aClock dgm ts) ->
  forall e, ~ dgm[e --> e].
Proof.
  intros. destruct H as (ts, H). destruct H as (H1, H2, H3).
  intro.
  pose (H1' := H1 e). destruct H1' as (n, H4).
  assert (n < n). {
    apply H3 with (e1 := e) (e2 := e); trivial;
    apply H4; pose (proj1 (happen_before_event dgm e e H)); assumption. }
  now apply Nat.lt_irrefl with n.
Qed.


Fixpoint initiators (dgm : Diagram) : FSet PID.
Proof.
  destruct dgm.
  destruct participants as (lst, H).
  induction lst as [| e lst' IHlst'].
  - exact empty.
  - exists lst'. inversion H; constructor || assumption.
  